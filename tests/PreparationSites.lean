/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export.Core
import EDSL.Grading.Runtime.Checker
import Lean

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Exercise real checked synthetic declarations. Small roots lead to a larger
helper or constructor; diagnostics must identify the field that actually stops.
No candidate is installed unchecked, and no failure yields a usable closure. -/
namespace PreparationSiteTests
open Lean EDSLGrader EDSLGrader.Runtime

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap {α : Type} (result : Except Failure α) : IO α :=
  match result with
  | .ok value => pure value
  | .error failure => throw (IO.userError s!"unexpected failure: {failure}")

private def add (env : Kernel.Environment) (decl : Declaration) : IO Kernel.Environment :=
  unwrap (forceDeclaration env 10000000 1024 decl)

private def definition (name : Name) (type value : Expr) : Declaration :=
  .defnDecl {
    name := name
    levelParams := []
    type := type
    value := value
    hints := .abbrev
    safety := .safe
    all := [name] }

private def theoremDecl (name : Name) (type value : Expr) : Declaration :=
  .thmDecl { name, levelParams := [], type, value }

private def equality (value : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) value value

private def reflexivity (value : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) value

private def successors (value : Expr) : Expr :=
  (List.range 128).foldl (fun value _ => mkApp (mkConst ``Nat.succ) value) value

private def slowProof : Expr :=
  (List.range 128).foldl (fun body _ =>
    .letE `h (mkConst ``True) (mkConst ``True.intro) body true) (mkConst ``True.intro)

private def slowType : Expr :=
  (List.range 128).foldl (fun body _ =>
    .letE `T (.sort 1) (mkConst ``Nat) body true) (mkConst ``Nat)

private def expectFailureAt {α : Type} (result : Except Failure α)
    (kind : FailureKind) (reason site owner : String) :
    IO Failure := do
  match result with
  | .ok _ => throw (IO.userError s!"expected bounded failure at {site}/{owner}")
  | .error failure =>
    require (failure.kind == kind) s!"wrong failure category: {failure}"
    for text in [reason, "site=" ++ site ++ ";", "name=" ++ owner ++ ";"] do
      require ((failure.message.splitOn text).length > 1) s!"missing '{text}': {failure}"
    return failure

private def expectSite {α : Type} (result : Except Failure α) (site owner : String) :
    IO Failure := expectFailureAt result .unsupported "expression work bound" site owner

private def numberField (failure : Failure) (key : String) : IO Nat := do
  let parts := failure.message.splitOn (key ++ "=")
  let some suffix := parts[1]? | throw (IO.userError s!"missing diagnostic {key}: {failure}")
  let some digits := (suffix.splitOn ";").head? | throw (IO.userError "missing diagnostic digits")
  let some value := digits.toNat? | throw (IO.userError s!"invalid diagnostic {key}: {failure}")
  return value

private def contains (text part : String) : Bool := (text.splitOn part).length > 1

private def limited : Export.PreparedLimits := { expression := { maxSteps := 128 } }

private def baseCases (trusted : Kernel.Environment) : IO Kernel.Environment := do
  let helper := `SyntheticSites.helper
  let root := `SyntheticSites.smallRoot
  let functionType : Expr := .forallE .anonymous (mkConst ``Nat) (mkConst ``Nat) .default
  let functionValue := Expr.lam `n (mkConst ``Nat) (successors (.bvar 0)) .default
  let client ← add trusted (definition helper functionType functionValue)
  let applied := mkApp (mkConst helper) (toExpr (0 : Nat))
  let client ← add client (theoremDecl root (equality applied) (reflexivity applied))
  -- Well-typed metadata and an ordinary successful preview rule out an
  -- unrelated reconstruction failure as the source of the bounded rejection.
  let _ ← unwrap <| Export.discoverTheoremPrepared trusted client root
  for mode in [Export.Mode.reference, .body] do
    let failure ← expectSite
      (Export.discoverTheoremPrepared trusted client root {} mode {} limited)
      "declaration value" "SyntheticSites.helper"
    require ((← numberField failure "effectiveSteps") == 128)
      "the failing helper received the wrong configured allowance"

  return client

private def statementCase (trusted client : Kernel.Environment) : IO Kernel.Environment := do
  let rootType := `SyntheticSites.largeStatement
  let term := successors (toExpr (0 : Nat))
  let statementClient ← add client (theoremDecl rootType (equality term) (reflexivity term))
  let _ ← unwrap <| Export.discoverTheoremPrepared trusted statementClient rootType
  let _ ← expectSite
    (Export.discoverTheoremPrepared trusted statementClient rootType {} .reference {} limited)
    "root type" "SyntheticSites.largeStatement"

  return statementClient

private def proofCases (trusted client : Kernel.Environment) : IO Unit := do
  let rootValue := `SyntheticSites.largeProof
  let proofClient ← add client (theoremDecl rootValue (mkConst ``True) slowProof)
  let _ ← unwrap <| Export.discoverTheoremPrepared trusted proofClient rootValue
  let _ ← expectSite
    (Export.discoverTheoremPrepared trusted proofClient rootValue {} .body {} limited)
    "root value" "SyntheticSites.largeProof"
  let _ ← expectSite
    (Export.discoverTheoremPrepared trusted proofClient rootValue {} .reference {} limited)
    "declaration value" "SyntheticSites.largeProof"

  pure ()

private def headerCase (trusted client : Kernel.Environment) : IO Unit := do
  let header := `SyntheticSites.Header
  let constructor := `SyntheticSites.Header.pack
  let headerClient ← add client (.inductDecl [] 0 [{
    name := header, type := .sort 1, ctors := [{
      name := constructor, type := .forallE `payload slowType (mkConst header) .default }]
    }] false)
  let headerRoot := `SyntheticSites.headerRoot
  let headerType := mkApp (mkConst ``Nonempty [1]) (mkConst header)
  let headerProof := mkApp2 (mkConst ``Nonempty.intro [1]) (mkConst header)
    (mkApp (mkConst constructor) (toExpr (0 : Nat)))
  let headerClient ← add headerClient (theoremDecl headerRoot headerType headerProof)
  let _ ← unwrap <| Export.discoverTheoremPrepared trusted headerClient headerRoot
  let _ ← expectSite
    (Export.discoverTheoremPrepared trusted headerClient headerRoot {} .reference {} limited)
    "constructor header" "SyntheticSites.Header.pack"

  pure ()

private def rhsCases (trusted client : Kernel.Environment) : IO Unit := do
  let helper := `SyntheticSites.helper
  let root := `SyntheticSites.smallRoot
  let functionValue := Expr.lam `n (mkConst ``Nat) (successors (.bvar 0)) .default
  for (preparation, slot) in [
      (({ definitionValues := #[(helper, functionValue)] } : Export.Prepare.Preparation),
        "definition-value RHS"),
      (({ inlineConstants := #[(helper, functionValue)] } : Export.Prepare.Preparation),
        "inline RHS")] do
    let _ ← expectSite
      (Export.discoverTheoremPrepared trusted client root preparation .reference {} limited)
      slot "SyntheticSites.helper"

  pure ()

private def aggregateCases (trusted client : Kernel.Environment) : IO Kernel.Environment := do
  let statementClient := client
  let rootType := `SyntheticSites.largeStatement
  -- Map validation spends some of the aggregate allowance before the first
  -- root field. The failing walk must report that smaller actual remainder.
  let tiny := `SyntheticSites.tiny
  let aggregateClient ← add statementClient (definition tiny (mkConst ``Nat) (toExpr (1 : Nat)))
  let preparation : Export.Prepare.Preparation := {
    inlineConstants := #[(tiny, toExpr (1 : Nat))] }
  let aggregate : Export.PreparedLimits := {
    expression := { maxSteps := 128 }, maxPreparationSteps := 64 }
  let failure ← expectSite (Export.discoverTheoremPrepared trusted aggregateClient
    rootType preparation .reference {} aggregate) "root type" "SyntheticSites.largeStatement"
  let previous ← numberField failure "previousSteps"
  let effective ← numberField failure "effectiveSteps"
  require (previous > 0 && effective > 0 && effective < 64)
    "reported allowance ignored work already spent validating the map"
  let more : Export.PreparedLimits := { aggregate with maxPreparationSteps := 65 }
  let next ← expectSite (Export.discoverTheoremPrepared trusted aggregateClient
    rootType preparation .reference {} more) "root type" "SyntheticSites.largeStatement"
  require ((← numberField next "previousSteps") == previous &&
    (← numberField next "effectiveSteps") == effective + 1 &&
    (← numberField failure "walkSteps") == effective &&
    (← numberField next "walkSteps") == effective + 1)
    "one extra aggregate step was not reflected in the exhausted field"

  return aggregateClient

private def dependencyCases (trusted client : Kernel.Environment) : IO Unit := do
  let aggregateClient := client
  let root := `SyntheticSites.smallRoot
  let tiny := `SyntheticSites.tiny
  -- The reported owner is the requesting RHS, not the referenced dependency.
  let keep := `SyntheticSites.keep
  let dependencyClient ← add aggregateClient (definition keep (mkConst ``Nat) (mkConst tiny))
  for (request, slot) in [
      (({ definitionValues := #[(tiny, toExpr (1 : Nat)), (keep, mkConst tiny)] } :
        Export.Prepare.Preparation), "definition-value RHS"),
      (({ inlineConstants := #[(tiny, toExpr (1 : Nat)), (keep, mkConst tiny)] } :
        Export.Prepare.Preparation), "inline RHS")] do
    let _ ← expectFailureAt (Export.discoverTheoremPrepared trusted dependencyClient root request)
      .unsupported "unsupported replacement dependency" slot "SyntheticSites.keep"

  pure ()

private def guardCase (trusted client : Kernel.Environment) : IO Unit := do
  let root := `SyntheticSites.smallRoot
  let stopped ← expectFailureAt (Export.discoverTheoremPrepared trusted client root
    {} .reference {} { maxPreparedFields := 0 })
    .resource "client preparation fields" "root type" "SyntheticSites.smallRoot"
  require (!contains stopped.message "walkSteps=") "a pre-walk guard reported a completed walk"

  pure ()

private def nameBudgetCase (trusted client : Kernel.Environment) : IO Unit := do
  let aggregateClient := client
  let preparation : Export.Prepare.Preparation := {
    inlineConstants := #[(`SyntheticSites.tiny, toExpr (1 : Nat))] }
  -- Spend name fuel before reaching a longer constant name in the root type.
  let longName := (List.range 48).foldl (fun n _ => Name.str n "part") Name.anonymous
  let nameClient ← add aggregateClient (definition longName (mkConst ``Nat) (toExpr (0 : Nat)))
  let nameRoot := `SyntheticSites.nameRoot
  let nameClient ← add nameClient (theoremDecl nameRoot
    (equality (mkConst longName)) (reflexivity (mkConst longName)))
  let _ ← unwrap <| Export.discoverTheoremPrepared trusted nameClient nameRoot
  let nameBudget : Export.PreparedLimits := {
    expression := { maxNameWork := 128 }, maxPreparationNameWork := 32 }
  let firstName ← expectFailureAt (Export.discoverTheoremPrepared trusted nameClient nameRoot
    preparation .reference {} nameBudget)
    .unsupported "name-component work bound" "root type" "SyntheticSites.nameRoot"
  let nextName ← expectFailureAt (Export.discoverTheoremPrepared trusted nameClient nameRoot
    preparation .reference {} { nameBudget with maxPreparationNameWork := 33 })
    .unsupported "name-component work bound" "root type" "SyntheticSites.nameRoot"
  let nameBefore ← numberField firstName "previousNameWork"
  let nameAllowance ← numberField firstName "effectiveNameWork"
  require (nameBefore > 0 && nameAllowance > 0 && nameAllowance < 32 &&
    (← numberField nextName "previousNameWork") == nameBefore &&
    (← numberField nextName "effectiveNameWork") == nameAllowance + 1 &&
    (← numberField firstName "walkNameWork") == nameAllowance &&
    (← numberField nextName "walkNameWork") == nameAllowance + 1)
    "diagnostic name allowance ignored the shared aggregate budget"

  pure ()

private def labelCases (trusted client : Kernel.Environment) : IO Unit := do
  let root := `SyntheticSites.smallRoot
  -- Arbitrary client names must not turn rejection into unbounded/multiline
  -- diagnostic output. No direct formatter fixture assertions are used.
  for key in [Name.str .anonymous (String.ofList (List.replicate 5000 'x') ++ "\nλ"),
      Name.num `SyntheticSites (2 ^ 4096), Name.str .anonymous "visible\nλ"] do
    match Export.discoverTheoremPrepared trusted client root
        { inlineConstants := #[(key, toExpr (1 : Nat))] } with
    | .ok _ => throw (IO.userError "ineligible key was accepted")
    | .error failure =>
      require (failure.kind == .unsupported && failure.message.length < 2048 &&
        !contains failure.message "\n" && !contains failure.message "\r" &&
        failure.message.toList.all (fun c => c.toNat < 128))
        "diagnostic name rendering escaped its bounded single-line representation"
  pure ()

private def runCases (trusted : Kernel.Environment) : IO Unit := do
  let client ← baseCases trusted
  let statement ← statementCase trusted client
  proofCases trusted client
  headerCase trusted client
  rhsCases trusted client
  let aggregate ← aggregateCases trusted statement
  dependencyCases trusted aggregate
  guardCase trusted client
  nameBudgetCase trusted aggregate
  labelCases trusted client

run_cmd do
  let _ ← runCases (← getEnv).toKernelEnv
  logInfo "PreparationSites: checked metadata, exact failure fields, remaining aggregate budget and bounded labels passed"
end PreparationSiteTests
