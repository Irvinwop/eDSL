/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Lean
import EDSL.Grading.Runtime.Checker
import EDSL.Pair32.Correctness
import EDSL.Stride32.Correctness

open Lean EDSLGrader.Runtime

namespace GradingRuntimeTests

/-! These tests check controller behavior, not new mathematical claims. Negative
fixtures exist only as Expr/Declaration data in a local checked environment. No
fixture axiom or unsafe/partial definition is added to this module, and candidate
expressions are never compiled or evaluated. The synthetic bridge-shaped axiom
tests the allow-list policy; it is not evidence for any submitted theorem. -/

def truth := mkConst ``True
def intro := mkConst ``True.intro
def nat := mkConst ``Nat
def eqNat (a b : Expr) := mkApp3 (mkConst ``Eq [1]) nat a b
def reflNat (a : Expr) := mkApp2 (mkConst ``Eq.refl [1]) nat a

def packet (decls : List Declaration) (e : Expr) : Except Failure String := encodePacket decls e

def fixtureEnvironment (base : Kernel.Environment) : IO Kernel.Environment := do
  let bridgeType := eqNat (mkNatLit 1) (mkNatLit 1)
  let fixtures : List Declaration := [
    .defnDecl {
      name := `GradingRuntimeTests.ownedUnsafe
      levelParams := []
      type := truth
      value := intro
      hints := .regular 0
      safety := .unsafe },
    .axiomDecl { name := `GradingRuntimeTests.ownedAxiom, levelParams := [], type := truth, isUnsafe := false },
    .opaqueDecl {
      name := `GradingRuntimeTests.ownedHidden
      levelParams := []
      type := truth
      value := mkConst `GradingRuntimeTests.ownedAxiom
      isUnsafe := false },
    .axiomDecl {
      name := `GradingRuntimeTests.syntheticBridgeAxiom
      levelParams := []
      type := bridgeType
      isUnsafe := false },
    .thmDecl {
      name := `GradingRuntimeTests.ownedNative
      levelParams := []
      type := bridgeType
      value := mkConst `GradingRuntimeTests.syntheticBridgeAxiom }]
  let mut env := base
  for decl in fixtures do
    match Kernel.Environment.addDeclCore env 10000000 512 decl none with
    | .ok next => env := next
    | .error e => throw <| IO.userError s!"owned fixture setup: {kernelFailure e}"
  return env

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let imported ← importModules #[{ module := `EDSL.Pair32.Correctness },
    { module := `EDSL.Stride32.Correctness }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false)
  let env ← fixtureEnvironment imported.toKernelEnv
  let lim : Limits := {}
  let assertOutcome (label : String) (wanted : Option (FailureKind × String))
      (result : Except Failure Checked) := do
    match wanted, result with
    | none, .ok got =>
      IO.println s!"PASS {label}: ACCEPT (constants={got.constants}, decoder={got.decoderSteps}, audit={got.auditSteps}, checks={got.kernelChecks})"
    | some (kind, message), .error got =>
      unless got.kind == kind && got.message == message do
        throw <| IO.userError s!"{label}: wanted {repr kind}/{message}, got {got}"
      IO.println s!"PASS {label}: REJECT {got}"
    | none, .error got => throw <| IO.userError s!"{label}: wanted ACCEPT, got {got}"
    | some _, .ok _ => throw <| IO.userError s!"{label}: wanted rejection, accepted"
  let run (label : String) (wanted : Option (FailureKind × String))
      (ty value : Expr) (ds : List Declaration := []) := do
    let encoded ← match packet ds value with
      | .ok s => pure s
      | .error e => throw <| IO.userError s!"export {label}: {e}"
    assertOutcome label wanted (checkPacket env lim ty encoded)
  run "truth-reference" none truth intro
  run "lambda-and-bound-variable" none
    (.forallE `n nat (eqNat (.bvar 0) (.bvar 0)) .default)
    (.lam `n nat (reflNat (.bvar 0)) .default)
  run "dependent-proposition-binders" none
    (.forallE `p (.sort .zero) (.forallE `h (.bvar 0) (.bvar 1) .default) .default)
    (.lam `p (.sort .zero) (.lam `h (.bvar 0) (.bvar 0) .default) .default)
  for bi in [BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
    run s!"binder-{binderJson bi |>.compress}" none
      (.forallE `h truth truth bi) (.lam `h truth (.bvar 0) bi)
  run "let" none (eqNat (mkNatLit 7) (mkNatLit 7))
    (.letE `x nat (mkNatLit 7) (reflNat (.bvar 0)) false)
  let pair := mkApp4 (mkConst ``Prod.mk [0, 0]) nat nat (mkNatLit 7) (mkNatLit 9)
  run "projection" none (eqNat (mkNatLit 7) (mkNatLit 7)) (reflNat (.proj ``Prod 0 pair))
  let text := mkStrLit "escape [\"x\"] \\ \n Ω"
  let str := mkConst ``String
  run "string-literal-json-escapes" none
    (mkApp3 (mkConst ``Eq [1]) str text text) (mkApp2 (mkConst ``Eq.refl [1]) str text)
  let bytes := toExpr ([0x90, 0xc3] : List (BitVec 8))
  let wrongBytes := toExpr ([0x90, 0x90] : List (BitVec 8))
  let byteType := toTypeExpr (List (BitVec 8))
  let byteExpected := mkApp3 (mkConst ``Eq [1]) byteType bytes bytes
  run "typed-literal-artifact" none byteExpected (mkApp2 (mkConst ``Eq.refl [1]) byteType bytes)
  run "wrong-literal-artifact-task" (some (.rejected, "kernel declTypeMismatch"))
    byteExpected (mkApp2 (mkConst ``Eq.refl [1]) byteType wrongBytes)
  run "wrong-expected-type" (some (.rejected, "kernel declTypeMismatch")) (mkConst ``False) intro
  run "only-proofs-finally-certified" (some (.rejected, "kernel thmTypeIsNotProp")) nat (mkNatLit 7)
  run "extra-hypothesis" (some (.rejected, "kernel declTypeMismatch")) truth
    (.lam `h (mkConst ``False) intro .default)
  run "unknown-constant" (some (.malformed, "unknown constant")) truth (mkConst `OwnedPacket.unknown)
  run "universe-arity" (some (.malformed, "constant universe arity")) truth (.const ``True.intro [0])
  run "loose-variable" (some (.malformed, "loose bound variable")) truth (.bvar 0)
  run "undeclared-final-universe" (some (.malformed, "undeclared universe parameter")) truth (.sort (.param `u))
  run "invalid-projection" (some (.rejected, "kernel invalidProj")) truth (.proj ``True 0 intro)
  run "illtyped-let" (some (.rejected, "kernel letTypeMismatch")) truth (.letE `x nat intro intro false)
  run "non-function" (some (.rejected, "kernel funExpected")) truth (.app intro intro)
  run "unsafe-owned-data" (some (.audit, "unsafe dependency")) truth (mkConst `GradingRuntimeTests.ownedUnsafe)
  run "unsafeCast-data-only" (some (.audit, "unsafe dependency")) truth
    (mkApp3 (mkConst ``unsafeCast [0, 0]) truth truth intro)
  run "sorryAx-data-only" (some (.audit, "unapproved axiom")) truth
    (mkApp2 (mkConst ``sorryAx [0]) truth (mkConst ``Bool.false))
  run "transitive-opaque-axiom" (some (.audit, "unapproved axiom")) truth (mkConst `GradingRuntimeTests.ownedHidden)
  let some ni := env.find? `GradingRuntimeTests.ownedNative | throw <| IO.userError s!"native fixture missing"
  run "native-bridge-data-only" (some (.audit, "unapproved axiom")) ni.type (mkConst `GradingRuntimeTests.ownedNative)
  for thmName in [``EDSL.Pair32.resource_sound, ``EDSL.Stride32.resource_sound, ``Nat.add_comm] do
    let some info := env.find? thmName | throw <| IO.userError s!"theorem missing {thmName}"
    run s!"reference-{thmName}" none info.type (mkConst thmName)
    let some body := info.value? (allowOpaque := true) | throw <| IO.userError s!"body missing {thmName}"
    run s!"body-{thmName}" none info.type body

  let u := Level.param `u
  let idTy := Expr.forallE `α (.sort u) (.forallE `x (.bvar 0) (.bvar 1) .default) .implicit
  let idVal := Expr.lam `α (.sort u) (.lam `x (.bvar 0) (.bvar 0) .default) .implicit
  let idDecl := Declaration.defnDecl {
    name := `OwnedPacket.id
    levelParams := [`u]
    type := idTy
    value := idVal
    hints := .regular 0
    safety := .safe }
  let opaqueDecl := Declaration.opaqueDecl {
    name := `OwnedPacket.hidden
    levelParams := []
    type := truth
    value := mkApp2 (mkConst `OwnedPacket.id [0]) truth intro
    isUnsafe := false }
  let helper := Declaration.thmDecl {
    name := `OwnedPacket.helper
    levelParams := []
    type := truth
    value := mkConst `OwnedPacket.hidden }
  run "fresh-def-opaque-theorem-chain" none truth (mkConst `OwnedPacket.helper)
    [idDecl, opaqueDecl, helper]
  let unapproved := Declaration.thmDecl {
    name := `OwnedPacket.unused
    levelParams := []
    type := truth
    value := mkConst `GradingRuntimeTests.ownedHidden }
  run "unused-helper-still-audited" (some (.audit, "unapproved axiom")) truth intro [unapproved]
  let shadow := Declaration.thmDecl { name := ``True.intro, levelParams := [], type := truth, value := intro }
  run "trusted-name-shadow" (some (.rejected, "declaration name collision")) truth intro [shadow]
  let simpleHelper := Declaration.thmDecl {
    name := `OwnedPacket.helper
    levelParams := []
    type := truth
    value := intro }
  run "packet-duplicate" (some (.rejected, "declaration name collision")) truth intro [simpleHelper, simpleHelper]
  let reserved := Declaration.thmDecl {
    name := `EDSLGrader.Internal.owned
    levelParams := []
    type := truth
    value := intro }
  run "reserved-certification-prefix" (some (.rejected, "reserved certification name")) truth intro [reserved]
  let undeclared := Declaration.thmDecl {
    name := `OwnedPacket.univ
    levelParams := []
    type := Expr.forallE `p (.sort (.param `u)) truth .default
    value := Expr.lam `p (.sort (.param `u)) intro .default }
  run "undeclared-helper-universe" (some (.malformed, "undeclared universe parameter")) truth intro [undeclared]
  let duplicateParams := Declaration.defnDecl {
    name := `OwnedPacket.badParams
    levelParams := [`u, `u]
    type := idTy
    value := idVal
    hints := .regular 0
    safety := .safe }
  run "duplicate-universe-parameter" (some (.malformed, "duplicate or anonymous universe parameter"))
    truth intro [duplicateParams]
  let numericName := Name.num `OwnedPacket 3
  let stringName := Name.str `OwnedPacket "3"
  let numericDecl := Declaration.thmDecl { name := numericName, levelParams := [], type := truth, value := intro }
  let stringDecl := Declaration.thmDecl { name := stringName, levelParams := [], type := truth, value := intro }
  run "name-num-string-distinction" none truth (mkConst numericName) [numericDecl, stringDecl]

  let flagName := `OwnedPacket.Flag
  let flag := mkConst flagName
  let flagCtor := flagName ++ `on
  let flagDecl := Declaration.inductDecl [] 0 [{
    name := flagName
    type := .sort 0
    ctors := [{ name := flagCtor, type := flag }] }] false
  let flagValue := Expr.letE `w flag (mkConst flagCtor) intro false
  run "fresh-simple-proposition-inductive" none truth flagValue [flagDecl]
  let flagBody ← match packet [flagDecl] flagValue with
    | .ok s => pure s
    | .error e => throw <| IO.userError s!"flag export {e}"
  let result := checkPacket env lim truth flagBody
  let .ok checked := result | throw <| IO.userError s!"flag packet unexpectedly failed"
  let some (.recInfo recursor) := checked.env.find? (flagName ++ `rec)
    | throw <| IO.userError s!"generated recursor missing"
  let some (.inductInfo indInfo) := checked.env.find? flagName
    | throw <| IO.userError s!"inductive metadata missing"
  IO.println s!"PROBE simple inductive generated: recursor-levels={recursor.levelParams}, rules={recursor.rules.length}, numNested={indInfo.numNested}"
  unless checked.env.find? (certificationPrefix ++ `proof) |>.isNone do
    throw <| IO.userError s!"scratch certification leaked into return environment"
  unless env.find? flagName |>.isNone do throw <| IO.userError s!"input environment mutated"
  assertOutcome "no-cross-packet-state" (some (.malformed, "unknown constant"))
    (checkPacket env lim truth (← match packet [] flagValue with | .ok x => pure x | .error e => throw <| IO.userError s!"{e}"))
  let recCollision := Declaration.thmDecl {
    name := flagName ++ `rec
    levelParams := []
    type := truth
    value := intro }
  let .ok recCollisionEnv := Kernel.Environment.addDeclCore env 10000000 512 recCollision none
    | throw <| IO.userError s!"owned recursor collision precondition rejected"
  match Kernel.Environment.addDeclCore recCollisionEnv 10000000 512 flagDecl none with
  | .error (.alreadyDeclared _ name) =>
    unless name == flagName ++ `rec do throw <| IO.userError s!"wrong generated name collision {name}"
    IO.println "PASS direct-kernel-generated-recursor-collision: alreadyDeclared"
  | .error e => throw <| IO.userError s!"unexpected generated name collision: {kernelFailure e}"
  | .ok _ => throw <| IO.userError s!"generated name collision unexpectedly accepted"
  run "generated-rec-name-shadow" (some (.rejected, "declaration name collision")) truth intro [recCollision, flagDecl]
  let sameCtor := Declaration.inductDecl [] 0 [{
    name := flagName, type := .sort 0
    ctors := [{ name := flagName ++ `rec, type := flag }] }] false
  run "constructor-generated-rec-collision" (some (.rejected, "declaration name collision")) truth intro [sameCtor]
  let ctorShadow := Declaration.inductDecl [] 0 [{
    name := flagName, type := .sort 0
    ctors := [{ name := ``True.intro, type := flag }] }] false
  run "constructor-trusted-shadow" (some (.rejected, "declaration name collision")) truth intro [ctorShadow]

  let a := mkConst `OwnedPacket.A
  let b := mkConst `OwnedPacket.B
  let mutualDecl := Declaration.inductDecl [] 0 [
    { name := `OwnedPacket.A, type := .sort 1, ctors := [
      { name := `OwnedPacket.A.mk, type := .forallE `b b a .default }] },
    { name := `OwnedPacket.B, type := .sort 1, ctors := [
      { name := `OwnedPacket.B.base, type := b },
      { name := `OwnedPacket.B.step, type := .forallE `a a b .default }] }] false
  let av := mkApp (mkConst `OwnedPacket.A.mk) (mkConst `OwnedPacket.B.base)
  run "fresh-mutual-inductive" none truth (.letE `a a av intro false) [mutualDecl]
  let badInd := Declaration.inductDecl [] 0 [{
    name := flagName, type := .sort 0
    ctors := [{ name := flagCtor, type := .forallE `f (.forallE `x flag (mkConst ``False) .default) flag .default }] }] false
  run "negative-inductive-positivity" (some (.rejected, "kernel declaration rejected")) truth intro [badInd]

  let h := mkConst `OwnedPacket.Header
  let headerDecl := Declaration.inductDecl [] 0 [{
    name := `OwnedPacket.Header
    type := .sort 1
    ctors := [{ name := `OwnedPacket.Header.mk, type := .forallE `tag nat h .default }] }] false
  let header := mkApp (mkConst `OwnedPacket.Header.mk) (mkNatLit 7)
  run "fresh-header-witness" none truth (.letE `h h header intro false) [headerDecl]
  let headerRead := mkApp3 (mkConst `OwnedPacket.Header.rec [1])
    (.lam `h h nat .default) (.lam `tag nat (.bvar 0) .default) header
  run "fresh-header-recursor-reduction" none (eqNat (mkNatLit 7) (mkNatLit 7))
    (reflNat headerRead) [headerDecl]

  let boxN := `OwnedPacket.Box
  let box := mkConst boxN [u]
  let boxDecl := Declaration.inductDecl [`u] 1 [{
    name := boxN
    type := .forallE `α (.sort u) (.sort u) .default
    ctors := [{
      name := boxN ++ `mk
      type := .forallE `α (.sort u)
        (.forallE `x (.bvar 0) (.app box (.bvar 1)) .default) .implicit }] }] false
  let boxedNat := mkApp (mkConst boxN [1]) nat
  let boxed7 := mkApp2 (mkConst (boxN ++ `mk) [1]) nat (mkNatLit 7)
  run "parameterized-universe-inductive" none truth (.letE `b boxedNat boxed7 intro false) [boxDecl]
  let nestedN := `OwnedPacket.Nested
  let nested := mkConst nestedN
  let nestedDecl := Declaration.inductDecl [] 0 [{
    name := nestedN
    type := .sort 1
    ctors := [{ name := nestedN ++ `leaf, type := nested }, {
      name := nestedN ++ `node
      type := .forallE `xs (mkApp (mkConst ``List [0]) nested) nested .default }] }] false
  run "nested-group-unsupported" (some (.unsupported, "nested inductive group")) truth intro [nestedDecl]

  let small ← match packet [] intro with | .ok x => pure x | .error e => throw <| IO.userError s!"{e}"
  let checkRaw (label : String) (want : FailureKind × String) (s : String) :=
    assertOutcome label (some want) (checkPacket env lim truth s)
  checkRaw "no-bare-expression" (.malformed, "packet shape or version") "[\"const\",[\"True\",\"intro\"],[]]"
  checkRaw "no-object-fields" (.malformed, "JSON token") "{}"
  checkRaw "no-number-token" (.malformed, "JSON token") "[\"edsl-proof-v1\",[],[\"nat\",1e100000000]]"
  checkRaw "no-extra-expected-type" (.malformed, "packet shape or version")
    "[\"edsl-proof-v1\",[],[\"const\",[\"True\",\"intro\"],[]],\"True\"]"
  checkRaw "fvar-payload" (.malformed, "free variable") "[\"edsl-proof-v1\",[],[\"fvar\",\"x\"]]"
  checkRaw "mvar-payload" (.malformed, "expression metavariable") "[\"edsl-proof-v1\",[],[\"mvar\",\"x\"]]"
  checkRaw "level-mvar" (.malformed, "universe metavariable") "[\"edsl-proof-v1\",[],[\"sort\",[\"mvar\",\"x\"]]]"
  checkRaw "invalid-decimal" (.malformed, "decimal string") "[\"edsl-proof-v1\",[],[\"nat\",\"1e9\"]]"
  checkRaw "axiom-payload-unsupported" (.unsupported, "declaration kind")
    "[\"edsl-proof-v1\",[[\"axiom\",[],[],[],[]]],[\"const\",[\"True\",\"intro\"],[]]]"
  checkRaw "no-mutual-definitions" (.unsupported, "declaration kind")
    "[\"edsl-proof-v1\",[[\"mutual-def\",[]]],[\"const\",[\"True\",\"intro\"],[]]]"
  checkRaw "malformed-known-declaration" (.malformed, "declaration shape")
    "[\"edsl-proof-v1\",[[\"theorem\",[]]],[\"const\",[\"True\",\"intro\"],[]]]"
  assertOutcome "input-byte-limit" (some (.resource, "input bytes"))
    (checkPacket env { lim with maxInputBytes := 2 } truth small)
  assertOutcome "JSON-depth-limit" (some (.resource, "JSON depth"))
    (checkPacket env { lim with maxJsonDepth := 1 } truth small)
  assertOutcome "decoder-step-limit" (some (.resource, "decoder steps"))
    (checkPacket env { lim with maxNodes := 1 } truth small)
  assertOutcome "audit-step-limit" (some (.resource, "audit steps"))
    (checkPacket env { lim with maxAuditSteps := 1 } truth small)
  assertOutcome "declaration-count-limit" (some (.resource, "declaration entries"))
    (checkPacket env { lim with maxDeclarations := 0 } truth flagBody)
  assertOutcome "generated-name-count-limit" (some (.resource, "declared constant names"))
    (checkPacket env { lim with maxDeclarations := 2 } truth flagBody)
  assertOutcome "zero-heartbeat-budget" (some (.resource, "kernel budget per check"))
    (checkPacket env { lim with kernelHeartbeats := 0 } truth small)
  assertOutcome "zero-recdepth-budget" (some (.resource, "kernel budget per check"))
    (checkPacket env { lim with kernelRecDepth := 0 } truth small)
  assertOutcome "kernel-heartbeat-resource" (some (.resource, "kernel heartbeat limit"))
    (checkPacket env { lim with kernelHeartbeats := 1 } truth small)
  let some pairInfo := env.find? ``EDSL.Pair32.resource_sound | throw <| IO.userError s!"pair theorem missing"
  let some pairBody := pairInfo.value? (allowOpaque := true) | throw <| IO.userError s!"pair proof body missing"
  assertOutcome "kernel-recursion-resource" (some (.resource, "kernel recursion limit"))
    (checkExpr env { lim with kernelRecDepth := 1 } pairInfo.type pairBody `EDSLGrader.Internal.depthTest)
  let chain ← match packet [idDecl, opaqueDecl, helper] (mkConst `OwnedPacket.helper) with
    | .ok x => pure x
    | .error e => throw <| IO.userError s!"{e}"
  assertOutcome "aggregate-decoder-budget" (some (.resource, "decoder steps"))
    (checkPacket env { lim with maxNodes := 40 } truth chain)
  assertOutcome "aggregate-audit-budget" (some (.resource, "audit steps"))
    (checkPacket env { lim with maxAuditSteps := 12 } truth chain)
  assertOutcome "aggregate-kernel-budget" (some (.resource, "kernel budget per check"))
    (checkPacket env { lim with kernelHeartbeats := 3 } truth chain)
  assertOutcome "aggregate-name-budget" (some (.resource, "declared constant names"))
    (checkPacket env { lim with maxDeclarations := 3 } truth
      (← match packet [idDecl, flagDecl] intro with | .ok x => pure x | .error e => throw <| IO.userError s!"{e}"))
  assertOutcome "expression-depth-budget" (some (.resource, "expression depth"))
    (checkPacket env { lim with maxExprDepth := 1 } truth
      (← match packet [] (.lam `h truth intro .default) with | .ok x => pure x | .error e => throw <| IO.userError s!"{e}"))
  let longLiteral := mkStrLit (String.ofList (List.replicate 4097 'x'))
  assertOutcome "decoded-string-budget" (some (.resource, "string bytes"))
    (checkPacket env lim truth
      (← match packet [] longLiteral with | .ok x => pure x | .error e => throw <| IO.userError s!"{e}"))
  let rawHuge := "[\"edsl-proof-v1\",[],[\"str\",\"" ++ String.ofList (List.replicate 24579 'x') ++ "\"]]"
  assertOutcome "raw-string-preflight-budget" (some (.resource, "raw string bytes"))
    (checkPacket env lim truth rawHuge)
  let giantDecimal := "[\"edsl-proof-v1\",[],[\"nat\",\"" ++ String.ofList (List.replicate 129 '9') ++ "\"]]"
  assertOutcome "decimal-digit-budget" (some (.resource, "decimal digits"))
    (checkPacket env lim truth giantDecimal)

  let trustedCheck := checkExpr env lim truth intro `EDSLGrader.Internal.ownedTest
  assertOutcome "trusted-wrapper-checkExpr" none trustedCheck
  assertOutcome "checkExpr-open-guard" (some (.malformed, "expression metavariable"))
    (checkExpr env lim truth (.mvar ⟨`x⟩) `EDSLGrader.Internal.ownedTest)
  let partialDecl := Declaration.defnDecl {
    name := `GradingRuntimeTests.partialMetadata
    levelParams := []
    type := nat
    value := mkNatLit 7
    hints := .regular 0
    safety := .partial }
  let .ok partialEnv := Kernel.Environment.addDeclCore env 10000000 512 partialDecl none
    | throw <| IO.userError s!"owned partial metadata insertion rejected"
  assertOutcome "actual-partial-metadata" (some (.audit, "partial dependency metadata"))
    (checkExpr partialEnv lim truth (.letE `x nat (mkConst `GradingRuntimeTests.partialMetadata) intro false)
      `EDSLGrader.Internal.ownedTest)
  IO.println "Runtime probes complete; no candidate Expr compiled or evaluated."

#eval main

-- Execute with the actual elaborator option enabled. The trusted runtime API
-- still rejects the ill-typed value because its kernel boundary takes no Options.
set_option debug.skipKernelTC true in
run_cmd do
  unless debug.skipKernelTC.get (← getOptions) do throwError "option probe setup"
  match checkExpr (← getEnv).toKernelEnv {} (mkConst ``False) intro
      `EDSLGrader.Internal.optionTest with
  | .error failure =>
    unless failure.kind == .rejected && failure.message == "kernel declTypeMismatch" do
      throwError "skipKernelTC test: unexpected failure {failure}"
    logInfo "PASS skipKernelTC-ineffective: kernel declTypeMismatch"
  | .ok _ => throwError "skipKernelTC unexpectedly bypassed the checker"

end GradingRuntimeTests
