/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export
import EDSL.Grading.Driver

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Import/producer/codec/kernel integration checks. Expected propositions come
from this controller and the fixed trusted task, never the client root type.
Run after compiling tests.fixtures.PreparedExportClient. -/
namespace PreparedExportTests
open Lean EDSLGrader EDSLGrader.Runtime

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap {α : Type} (result : Except Failure α) : IO α :=
  match result with
  | .ok value => pure value
  | .error failure => throw (IO.userError s!"unexpected failure: {failure}")

private def reject {α : Type} (kind : FailureKind) (result : Except Failure α)
    (context : String) : IO Unit :=
  match result with
  | .error failure => require (failure.kind == kind) s!"{context}: {failure}"
  | .ok _ => throw (IO.userError (context ++ ": unexpectedly accepted"))

private def hasName (packet : Export.PreparedPacket) (name : Name) : Bool :=
  packet.declarations.any fun decl => decl.getNames.contains name

private def independentEquality (n : Nat) : Expr :=
  mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) (toExpr n) (toExpr n)

private def syntaxRejected (context : String) (outcome : Export.Prepare.Outcome) : IO Unit :=
  require outcome.output.isNone (context ++ ": invalid syntax escaped preparation")

private def preparedSyntax (context : String) (outcome : Export.Prepare.Outcome) : IO Expr := do
  let some output := outcome.output
    | throw (IO.userError (context ++ ": " ++ outcome.reason))
  return output

/-- Inspect labels directly: Expr's ordinary equality ignores binder annotations.
An actual substitution below paired application parents exercises rebuilding as
well as reuse of their shared children. These are syntax, not typing, checks. -/
private def labelCases : IO Unit := do
  let prop := Expr.sort .zero
  let key := Name.mkSimple "labelReplacement"
  let c := Expr.const key []
  let table : NameMap Expr := ({} : NameMap Expr).insert key (.lit (.natVal 7))
  let labels ← preparedSyntax "binder labels below application parents"
    (Export.Prepare.rewrite {} table (.app
      (.app prop (.lam `left prop c .implicit))
      (.app prop (.lam `right prop c .default))))
  match labels with
  | .app (.app _ (.lam l _ (.lit (.natVal 7)) .implicit))
      (.app _ (.lam r _ (.lit (.natVal 7)) .default)) =>
    require (l == `left && r == `right) "memoization collapsed binder names"
  | _ => throw (IO.userError "memoization changed binder annotations or substituted bodies")
  let flags ← preparedSyntax "let labels below application parents"
    (Export.Prepare.rewrite {} table (.app
      (.app prop (.letE `left prop prop c false))
      (.app prop (.letE `right prop prop c true))))
  match flags with
  | .app (.app _ (.letE l _ _ (.lit (.natVal 7)) false))
      (.app _ (.letE r _ _ (.lit (.natVal 7)) true)) =>
    require (l == `left && r == `right) "memoization collapsed let names"
  | _ => throw (IO.userError "memoization changed let nondep flags or substituted bodies")
  -- Isolate nondep from binder-name equality so a cache key that ignores only
  -- this flag still has to retain each use's own constructor field.
  let nondep ← preparedSyntax "same-name let nondep below application parents"
    (Export.Prepare.rewrite {} table (.app
      (.app prop (.letE `same prop prop c false))
      (.app prop (.letE `same prop prop c true))))
  match nondep with
  | .app (.app _ (.letE _ _ _ (.lit (.natVal 7)) false))
      (.app _ (.letE _ _ _ (.lit (.natVal 7)) true)) => pure ()
  | _ => throw (IO.userError "memoization collapsed same-name let nondep flags")
  let mdKey := Name.mkSimple "origin"
  let mdLeft := ({} : KVMap).setString mdKey "left"
  let mdRight := ({} : KVMap).setString mdKey "right"
  let metadata ← preparedSyntax "metadata below application parents"
    (Export.Prepare.rewrite {} table (.app
      (.app prop (.mdata mdLeft c)) (.app prop (.mdata mdRight c))))
  match metadata with
  | .app (.app _ (.mdata l (.lit (.natVal 7)))) (.app _ (.mdata r (.lit (.natVal 7)))) =>
    require (l.getString mdKey == "left" && r.getString mdKey == "right")
      "memoization moved or collapsed input metadata"
  | _ => throw (IO.userError "memoization dropped metadata or substituted bodies")

private def scopeCases : IO Unit := do
  let u := Name.mkSimple "u"
  let v := Name.mkSimple "v"
  let key := Name.mkSimple "replace"
  let prop := Expr.sort .zero
  let context := Expr.sort (.param u)
  require (Export.Prepare.rewrite {} {} context [u]).complete
    "a declared universe was rejected"
  syntaxRejected "undeclared universe" (Export.Prepare.rewrite {} {} context [v])
  syntaxRejected "duplicate declared universes" (Export.Prepare.rewrite {} {} context [u, u])
  -- First prime the cache in the legal caller universe, then use that same
  -- syntax as a raw replacement RHS. It must remain independently monomorphic.
  syntaxRejected "cached RHS inherits caller universe"
    (Export.Prepare.rewrite {} (({} : NameMap Expr).insert key context)
      (.app context (.const key [])) [u])
  syntaxRejected "a binder scopes its own domain"
    (Export.Prepare.rewrite {} {} (.lam `x (.bvar 0) (.bvar 0) .default))
  syntaxRejected "cached RHS captures caller binder"
    (Export.Prepare.rewrite {} (({} : NameMap Expr).insert key (.bvar 0))
      (.lam `x prop (.app (.bvar 0) (.const key [])) .default))
  syntaxRejected "raw self cycle"
    (Export.Prepare.rewrite {} (({} : NameMap Expr).insert key (.const key [])) (.const key []))

def main : IO Unit := do
  scopeCases
  labelCases
  let (trustedEnv, clientEnv) ← Export.loadEnvironments `tests.fixtures.PreparedExportClient
  let trusted := trustedEnv.toKernelEnv
  let client := clientEnv.toKernelEnv
  require ((trusted.find? `PreparedExportFixture.datum).isNone)
    "client data entered the trusted snapshot"
  let inlineData : Export.Prepare.Preparation := {
    inlineConstants := #[(`PreparedExportFixture.Ty, mkConst ``Nat),
      (`PreparedExportFixture.datum, toExpr (37 : Nat))] }
  let expected := independentEquality 37
  for mode in [Export.Mode.reference, .body] do
    for root in [`PreparedExportFixture.root, `PreparedExportFixture.polyRoot,
        `PreparedExportFixture.headerRoot, `PreparedExportFixture.opaqueRoot] do
      let packet ← unwrap <| Export.exportTheoremPrepared trusted client root inlineData mode
      require (!(hasName packet `PreparedExportFixture.Ty) &&
        !(hasName packet `PreparedExportFixture.datum))
        "rewritten type/value dependency remained in the closure"
      require (hasName packet root == (mode == .reference)) "root mode changed"
      let checked ← unwrap <| checkPacket trusted {} expected packet.text
      require (checked.kernelChecks > 1) "fresh auxiliaries did not reach the kernel"
      if root == `PreparedExportFixture.root then
        let some (.defnInfo actual) := checked.env.find? `PreparedExportFixture.keep
          | throw (IO.userError "checked helper missing")
        require (actual.type == mkConst ``Nat) "helper type was not rewritten"
      if root == `PreparedExportFixture.headerRoot then
        require (hasName packet `PreparedExportFixture.Header.rec) "inductive recursor omitted"
      if root == `PreparedExportFixture.polyRoot then
        require (hasName packet `PreparedExportFixture.polyKeep) "polymorphic helper omitted"
      if root == `PreparedExportFixture.opaqueRoot then
        require (hasName packet `PreparedExportFixture.sealed) "opaque helper omitted"

    let redirected : Export.Prepare.Preparation := {
      definitionValues := #[(`PreparedExportFixture.keep, mkConst `PreparedExportFixture.redirected)]
      inlineConstants := #[(`PreparedExportFixture.Ty, mkConst ``Nat)] }
    let packet ← unwrap <| Export.exportTheoremPrepared trusted client
      `PreparedExportFixture.overrideRoot redirected mode
    require (hasName packet `PreparedExportFixture.redirected &&
      !(hasName packet `PreparedExportFixture.datum)) "replacement dependencies were not discovered"
    let _ ← unwrap <| checkPacket trusted {} expected packet.text

    -- This tampered packet is internally valid for a DIFFERENT proposition.
    -- Replay it successfully there, then require rejection of the fixed contract.
    let wrong : Export.Prepare.Preparation := {
      inlineConstants := #[(`PreparedExportFixture.Ty, mkConst ``Nat),
        (`PreparedExportFixture.datum, toExpr (38 : Nat))] }
    let wrongPacket ← unwrap <| Export.exportTheoremPrepared trusted client
      `PreparedExportFixture.root wrong mode
    let _ ← unwrap <| checkPacket trusted {} (independentEquality 38) wrongPacket.text
    reject .rejected (checkPacket trusted {} expected wrongPacket.text)
      "internally valid proof substituted the independent contract"

    let broken : Export.Prepare.Preparation := {
      definitionValues := #[(`PreparedExportFixture.keep, toExpr (38 : Nat))]
      inlineConstants := #[(`PreparedExportFixture.Ty, mkConst ``Nat)] }
    let brokenPacket ← unwrap <| Export.exportTheoremPrepared trusted client
      `PreparedExportFixture.overrideRoot broken mode
    reject .rejected (checkPacket trusted {} expected brokenPacket.text)
      "changed auxiliary escaped checked reconstruction"

    let some known := trusted.find? `EDSL.Grading.Known.pair
      | throw (IO.userError "fixed independent pair contract missing")
    let pairData : Export.Prepare.Preparation := {
      definitionValues := #[(`PreparedExportFixture.pairProgram, byteExpr EDSL.Pair32.bytes)] }
    let pairPacket ← unwrap <| Export.exportTheoremPrepared trusted client
      `PreparedExportFixture.pairRoot pairData mode
    require (!(hasName pairPacket `PreparedExportFixture.originalPairBytes))
      "overridden complete program retained the old data dependency"
    let _ ← unwrap <| checkPacket trusted {} known.type pairPacket.text

  for key in [``Nat, `PreparedExportFixture.root, `PreparedExportFixture.sealed,
      `PreparedExportFixture.polyKeep, `PreparedExportFixture.Header.pack,
      `EDSLGrader.Internal.reserved, `PreparedExportFixture.missing] do
    reject .unsupported (Export.discoverTheoremPrepared trusted client
      `PreparedExportFixture.root { inlineConstants := #[(key, toExpr (37 : Nat))] })
      "ineligible preparation key"
  reject .unsupported (Export.discoverTheoremPrepared trusted client
    `PreparedExportFixture.root {
      inlineConstants := #[(`PreparedExportFixture.datum, toExpr (37 : Nat)),
        (`PreparedExportFixture.datum, toExpr (38 : Nat))] }) "duplicate keys"

  -- Each half fits the same field allowance separately. Combining map-RHS
  -- validation with root preparation must consume one cumulative allowance.
  let _ ← unwrap <| Export.discoverTheoremPrepared trusted client
    `EDSL.Grading.Known.pair {} .reference {} { maxPreparedFields := 2 }
  reject .resource (Export.discoverTheoremPrepared trusted client
    `EDSL.Grading.Known.pair inlineData .reference {} { maxPreparedFields := 2 })
    "field allowance reset after map validation"
  IO.println "PreparedExport: type/value/opaque/inductive/polymorphic preparation, independent kernel replay, contract tampering and aggregate failures passed"

#eval main
end PreparedExportTests
