/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.GradingLogical64
open X86 X86.Sequential Grading Logical64

/-- The current code domain includes the full artifact limit, independently
of the smaller CFG importer profile and of byte decoding. -/
theorem maximum_span_last_byte (byte : Byte) :
    fetchByte (Logical64.Domain.initial (List.replicate 4096 byte) 0 1).memory
      8191 = .ok byte := by
  have pre := Logical64.Domain.resource_pre (List.replicate 4096 byte)
    (by rw [List.length_replicate]; decide)
    (by rw [List.length_replicate]; exact Nat.le_refl _) 0 1
  exact pre.machine.code.2 4095 byte (by rw [List.getElem?_replicate]; rfl)

/-- Truncated FF group code remains currently admitted. Future execution success
must not be inserted into the raw or resource precondition to hide a fault. -/
theorem unsupported_domains :
    Nonvacuous (registered .intersection64) [0xff] ∧
      Nonvacuous (registered .union64) [0xff] ∧
      Nonvacuous (registered .symmetricDifference64) [0xff] :=
  ⟨domain_nonvacuous .intersection64 [0xff] (by decide) (by decide),
    domain_nonvacuous .union64 [0xff] (by decide) (by decide),
    domain_nonvacuous .symmetricDifference64 [0xff] (by decide) (by decide)⟩

/-- Actual execution faults on the admitted current input, refuting a total
claim. Missing proofs and timeouts play no role in this counterexample. -/
theorem unsupported_not_semantic (operation : Operation) :
    ¬SemanticClaim (Task.logicalTask operation) [0xff] := by
  intro claim
  have pre := Logical64.Domain.resource_pre [0xff] (by decide) (by decide) 0 1
  have total := (claim.machine (resourceInput (Logical64.Domain.resource [0xff] 0 1))
    (Logical64.Domain.initial [0xff] 0 1) pre.machine).1
  have fault : step false (Logical64.Domain.initial [0xff] 0 1) =
      .error (.inaccessibleInstruction 4097) := rfl
  have impossible := total.no_fault_prefix (fun _ => false)
    (Sequential.run_fault (choices := fun _ => false) (fuel := 0) fault)
  cases impossible

theorem unsupported_not_claims :
    ¬Claim .intersection64 [0xff] ∧ ¬Claim .union64 [0xff] ∧
      ¬Claim .symmetricDifference64 [0xff] :=
  ⟨fun claim => unsupported_not_semantic .intersection claim.1,
    fun claim => unsupported_not_semantic .union claim.1,
    fun claim => unsupported_not_semantic .symmetricDifference claim.1⟩

end EDSL.Tests.GradingLogical64

open Lean EDSL EDSL.Grading EDSLGrader EDSLGrader.Runtime

-- Exercise the public parser, quotation and kernel expected type together.
-- Swapping two mathematical tasks must fail even though their ABI is shared.
run_cmd do
  let env := (← getEnv).toKernelEnv
  let cases : List (String × Name × Name) := [
    ("intersection64", ``TaskID.intersection64, ``Logical64.Operation.intersection),
    ("union64", ``TaskID.union64, ``Logical64.Operation.union),
    ("symmetricDifference64", ``TaskID.symmetricDifference64, ``Logical64.Operation.symmetricDifference)]
  for (spelling, idName, operation) in cases do
    let some id := taskID spelling | throwError "task spelling rejected: {spelling}"
    unless (registered id).profile == .sequentialReadOnlyX86CallableV1 do
      throwError "wrong callable profile for {spelling}"
    let idType := mkConst ``TaskID
    let literalID := mkConst idName
    let idEquality := mkApp3 (mkConst ``Eq [1]) idType (taskExpr id) literalID
    let idProof := mkApp2 (mkConst ``Eq.refl [1]) idType literalID
    match checkExpr env {} idEquality idProof `EDSLGrader.Internal.logicalIDTest with
    | .error failure => throwError "wrong task ID for {spelling}: {failure}"
    | .ok _ => pure ()
    let taskType := mkConst ``Grading.Task
    let actual := mkApp (mkConst ``registered) (taskExpr id)
    let specification := mkApp (mkConst ``ofReadOnly)
      (mkApp (mkConst ``Logical64.readOnlyTask) (mkConst operation))
    let equality := mkApp3 (mkConst ``Eq [2]) taskType actual specification
    let proof := mkApp2 (mkConst ``Eq.refl [2]) taskType specification
    match checkExpr env {} equality proof `EDSLGrader.Internal.logicalRegistrationTest with
    | .error failure => throwError "wrong set specification for {spelling}: {failure}"
    | .ok _ => pure ()
  for spelling in ["Intersection64", "union64 ", "symmetricdifference64", "bitAnd64"] do
    unless (taskID spelling).isNone do
      throwError "unregistered spelling accepted: {spelling}"
  logInfo "Logical task spellings, quotations, mathematical registrations and profiles checked"

/-- The real trusted snapshot must include generic domain evidence and exclude
compiler-client proofs, which are supplied only as checked serialized data. -/
def checkLogicalTrustedBoundary : IO Unit := do
  initSearchPath (← findSysroot)
  let trusted ← importModules #[{ module := `EDSL.Grading.Known },
    { module := `EDSL.Grading.Artifact },
    { module := `EDSL.Grading.CallStack.Artifact },
    { module := `EDSL.Grading.CallMemory64.Artifact },
    { module := `EDSL.Grading.CallMemoryLoop64.Artifact },
    { module := `EDSL.Grading.AtomicLogical64.Artifact },
    { module := `EDSL.Grading.AtomicSet64.Artifact }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  unless (trusted.find? `EDSL.Logical64.Domain.nonvacuous).isSome do
    throw (IO.userError "independent logical domain missing from trusted snapshot")
  for (name, _) in trusted.constants.toList do
    if (`EDSL.Logical64.Client).isPrefixOf name then
      throw (IO.userError s!"logical client imported into trusted snapshot: {name}")
  IO.println "PASS logical trusted snapshot contains independent domain and excludes client proofs"

#eval checkLogicalTrustedBoundary

#print axioms EDSL.Logical64.MathematicalResult.unique
#print axioms EDSL.Logical64.Domain.nonvacuous
#print axioms EDSL.Tests.GradingLogical64.unsupported_not_claims
#audit_edsl
