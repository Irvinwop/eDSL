/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Lean
import EDSL.Grading.Runtime.Checker
import EDSL.Grading.Runtime.DAG

set_option warningAsError true
open Lean EDSLGrader.Runtime

namespace GradingDAGTests

/-! Owned synthetic expressions test data reconstruction and independent forced
kernel checks. Shared open syntax must never cache a context-dependent typing
judgment. No candidate expression is compiled or evaluated. -/

def unwrap (result : Except Failure α) : IO α :=
  match result with
  | .ok value => pure value
  | .error failure => throw (IO.userError s!"{failure}")

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def reject (label : String) (kind : FailureKind) (message : String)
    (result : Except Failure α) : IO Unit := do
  match result with
  | .error err =>
    require (err.kind == kind && err.message == message)
      s!"{label}: unexpected failure {err}"
    IO.println s!"PASS {label}: {err}"
  | .ok _ => throw (IO.userError s!"unexpected acceptance: {label}")

/-- Independently authored expected proposition. -/
def expected : Expr :=
  .forallE `n (mkConst ``Nat)
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat)
      (mkApp2 (mkConst ``Nat.add) (.bvar 0) (mkNatLit 0)) (.bvar 0)) .default

def repeatProof (prop proof : Expr) : Nat → Expr
  | 0 => proof
  | n+1 =>
    let previous := repeatProof prop proof n
    mkApp3 (mkConst ``And.left) prop prop
      (mkApp4 (mkConst ``And.intro) prop prop previous previous)

def candidate : Expr :=
  .lam `n (mkConst ``Nat)
    (repeatProof expected.bindingBody! (mkApp (mkConst ``Nat.add_zero) (.bvar 0)) 12) .default

def contextCandidate (bad : Bool) : Expr × Expr := Id.run do
  let bv := Expr.bvar 0
  let nt := mkConst ``Nat
  let bt := mkConst ``Bool
  let eq (t : Expr) := mkApp3 (mkConst ``Eq [1]) t bv bv
  let np := Expr.forallE `n nt (eq nt) .default
  let bp := Expr.forallE `b bt (eq bt) .default
  let nr := mkApp2 (mkConst ``Eq.refl [1]) nt bv
  let br := if bad then nr else mkApp2 (mkConst ``Eq.refl [1]) bt bv
  return (mkApp2 (mkConst ``And) np bp,
    mkApp4 (mkConst ``And.intro) np bp (.lam `n nt nr .default) (.lam `b bt br .default))

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let imported ← importModules #[{ module := `Lean }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false)
  let env := imported.toKernelEnv
  let lim : Limits := {}
  let decode (j : Json) := (DAG.decodeDag env lim [] [] j).run lim.maxNodes
  let dag (rows : Array Json) (root : String) := Json.arr #[.str "dag", .arr rows, .str root]
  let natZero := Json.arr #[.str "nat", .str "0"]
  let bvarZero := Json.arr #[.str "bvar", .str "0"]
  let natType := Json.arr #[.str "const", nameJson ``Nat, .arr #[]]
  let encoded ← unwrap (DAG.encodeDag candidate)
  -- Exercise parser admission as well as the in-memory decoder.
  let text := encoded.compress
  let _ ← unwrap (preflight lim text)
  let parsed ← match Json.parse text with
    | .ok j => pure j
    | .error err => throw (IO.userError err)
  let (value, remaining) ← unwrap (decode parsed)
  let checked ← unwrap (checkExpr env lim expected value `EDSLGrader.Internal.dagRoundtrip)
  let originalTree ← unwrap (encodeExpr candidate)
  let decodedTree ← unwrap (encodeExpr value)
  require (originalTree == decodedTree) "DAG roundtrip changed canonical expression syntax"
  require (originalTree.compress.utf8ByteSize > lim.maxInputBytes && text.utf8ByteSize < 4096)
    "repeated proof no longer exercises compression across the default input bound"
  IO.println s!"PASS repeated-open-proof: treeBytes={originalTree.compress.utf8ByteSize}, dagBytes={text.utf8ByteSize}, decoder={lim.maxNodes-remaining}, audit={checked.auditSteps}"
  let checkContext (bad : Bool) := do
    let (ty, proof) := contextCandidate bad
    let (proof, _) ← unwrap (decode (← unwrap (DAG.encodeDag proof)))
    return checkExpr env lim ty proof `EDSLGrader.Internal.dagContext
  let _ ← unwrap (← checkContext false)
  IO.println "PASS shared-bound-variable-under-different-types"
  reject "context-dependent-application-not-reused-as-typing" .rejected "kernel appTypeMismatch"
    (← checkContext true)
  reject "expected-proposition-remains-independent" .rejected "kernel declTypeMismatch"
    (checkExpr env lim (mkConst ``False) value `EDSLGrader.Internal.dagWrongType)
  reject "self-reference" .malformed "DAG forward, cyclic, or missing reference"
    (decode (dag #[.arr #[.str "app", .str "0", .str "0"]] "0"))
  reject "forward-reference" .malformed "DAG forward, cyclic, or missing reference"
    (decode (dag #[.arr #[.str "app", .str "1", .str "1"], natZero] "0"))
  reject "machine-width-reference-does-not-wrap" .malformed "DAG forward, cyclic, or missing reference"
    (decode (dag #[natZero] "18446744073709551616"))
  reject "large-bvar-before-Expr-construction" .resource "DAG bound variable range"
    (decode (dag #[.arr #[.str "bvar", .str "18446744073709551616"]] "0"))
  reject "large-projection-index-before-Expr-construction" .resource "DAG projection index"
    (decode (dag #[natZero,
      .arr #[.str "proj", nameJson ``Prod, .str "18446744073709551616", .str "0"]] "1"))
  reject "loose-root" .malformed "loose bound variable at DAG root"
    (decode (dag #[bvarZero] "0"))
  reject "binder-does-not-bind-its-type" .malformed "loose bound variable at DAG root"
    (decode (dag #[bvarZero, .arr #[.str "lam", .str "default", .str "0", .str "0"]] "1"))
  reject "let-does-not-bind-its-value" .malformed "loose bound variable at DAG root"
    (decode (dag #[natType, bvarZero, .arr #[.str "let", .str "0", .str "1", .str "1"]] "2"))
  reject "undeclared-universe" .malformed "undeclared universe parameter"
    (decode (dag #[.arr #[.str "sort", .arr #[.str "param", nameJson `u]]] "0"))
  reject "unused-forbidden-node" .malformed "unreachable DAG node"
    (decode (dag #[.arr #[.str "const", nameJson ``sorryAx, .arr #[.str "zero"]], natZero] "1"))
  let shallow : Limits := { lim with maxExprDepth := 20 }
  reject "shallow-json-cannot-hide-expanded-depth" .resource "expanded DAG expression depth"
    ((DAG.decodeDag env shallow [] [] parsed).run lim.maxNodes)
  -- Encode the shared subtree first on a shorter path, then reuse it under
  -- more successors. A cache hit must retain its full expanded syntax height.
  let successors (count : Nat) (base : Expr) :=
    (List.range count).foldl (fun value _ => mkApp (mkConst ``Nat.succ) value) base
  -- A raw literal avoids the frontend's additional OfNat application layers.
  let shared := successors 118 (mkRawNatLit 0)
  let atBoundary := mkApp2 (mkConst ``Nat.add) shared (successors 8 shared)
  let (boundary, _) ← unwrap (decode (← unwrap (DAG.encodeDag atBoundary)))
  let boundaryEquation := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) boundary (mkNatLit 244)
  let _ ← unwrap (checkExpr env lim boundaryEquation
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 244))
    `EDSLGrader.Internal.dagDepthBoundary)
  IO.println "PASS shared-depth-boundary-kernel-arithmetic"
  reject "encoder-cache-cannot-hide-expanded-depth" .resource "client expanded DAG expression depth"
    (DAG.encodeDag (mkApp2 (mkConst ``Nat.add) shared (successors 9 shared)))
  reject "aggregate-work-counts-reference-and-reachability" .resource "decoder steps"
    ((DAG.decodeDag env lim [] [] parsed).run 100)
  let (_, left) ← unwrap ((DAG.decodeDag env lim [] [] parsed).run (2 * (lim.maxNodes-remaining) - 1))
  reject "caller-budget-spans-expression-fields" .resource "decoder steps"
    ((DAG.decodeDag env lim [] [] parsed).run left)
  reject "expression-pools-are-isolated" .malformed "DAG forward, cyclic, or missing reference"
    (decode (dag #[] "0"))
  -- A valid let and projection ensure the four-field row variants remain distinct.
  let nt := mkConst ``Nat
  let pair := mkApp4 (mkConst ``Prod.mk [0, 0]) nt nt (mkNatLit 7) (mkNatLit 9)
  let seven := mkNatLit 7
  let eqSeven := mkApp3 (mkConst ``Eq [1]) nt seven seven
  let proof := Expr.letE `p (mkApp2 (mkConst ``Prod [0, 0]) nt nt) pair
    (mkApp2 (mkConst ``Eq.refl [1]) nt (.proj ``Prod 0 (.bvar 0))) false
  let (proof, _) ← unwrap (decode (← unwrap (DAG.encodeDag proof)))
  let _ ← unwrap (checkExpr env lim eqSeven proof `EDSLGrader.Internal.dagLetProj)
  IO.println "PASS let-and-projection-kernel-reduction"
  -- Ordinary Expr equality ignores binder annotations. Interning must preserve
  -- both annotations when they occur in the same expression graph.
  let functionType := Expr.forallE `n nt nt .default
  let explicitId := Expr.lam `n nt (.bvar 0) .default
  let implicitId := Expr.lam `n nt (.bvar 0) .implicit
  let mixed := Expr.letE `f functionType explicitId
    (.letE `g functionType implicitId (mkConst ``True.intro) false) false
  let (mixedDecoded, _) ← unwrap (decode (← unwrap (DAG.encodeDag mixed)))
  require ((← unwrap (encodeExpr mixed)) == (← unwrap (encodeExpr mixedDecoded)))
    "interning discarded binder annotations"
  let _ ← unwrap (checkExpr env lim (mkConst ``True) mixedDecoded
    `EDSLGrader.Internal.dagBinderAnnotations)
  IO.println "PASS mixed-binder-annotations-preserved"
  IO.println "DAG probes complete; candidate expressions remain data."

#eval main
end GradingDAGTests
