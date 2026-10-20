/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.GradingComparison64
open X86 X86.Sequential Grading Comparison64

/-- Current admission covers every full64 argument pair, including equality,
with any incoming result register and flags. Useful witnesses do not narrow it. -/
theorem arbitrary_inputs (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (left right incomingRax flags : Word) :
    ∃ resource initial, ResourcePre bytes resource initial ∧
      (resourceInput resource).left = left ∧ (resourceInput resource).right = right ∧
      initial.registers .rax = incomingRax ∧ initial.flags = flags := by
  exact ⟨Comparison64.Domain.resource bytes left right,
    Comparison64.Domain.initial bytes left right (fun _ => incomingRax) flags,
    Comparison64.Domain.resource_pre bytes positive bound left right (fun _ => incomingRax) flags,
    rfl, rfl, rfl, rfl⟩

/-- The upper artifact boundary still admits its last arbitrary executable
byte; the resource domain does not inherit a smaller decoder/importer cap. -/
theorem maximum_span_last_byte (byte : Byte) :
    fetchByte (Comparison64.Domain.initial (List.replicate 4096 byte) 0 1).memory
      8191 = .ok byte := by
  have pre := Comparison64.Domain.resource_pre (List.replicate 4096 byte)
    (by rw [List.length_replicate]; decide)
    (by rw [List.length_replicate]; exact Nat.le_refl _) 0 1
  exact pre.machine.code.2 4095 byte (by rw [List.getElem?_replicate]; rfl)

/-- Truncated FF group bytes have useful current and raw domains for all three
registrations. This is independent of their failing execution below. -/
theorem unsupported_domains :
    Nonvacuous (registered .maximum64) [0xff] ∧
      Nonvacuous (registered .minimum64) [0xff] ∧
      Nonvacuous (registered .signedMaximum64) [0xff] :=
  ⟨domain_nonvacuous .maximum64 [0xff] (by decide) (by decide),
    domain_nonvacuous .minimum64 [0xff] (by decide) (by decide),
    domain_nonvacuous .signedMaximum64 [0xff] (by decide) (by decide)⟩

/-- Refutation uses the actual sequential executor's fault on an admitted
input, rather than a missing proof, a timeout or proof-packet rejection. -/
theorem unsupported_not_semantic (operation : Operation) :
    ¬SemanticClaim (Task.comparisonTask operation) [0xff] := by
  intro claim
  have pre := Comparison64.Domain.resource_pre [0xff] (by decide) (by decide) 0 1
  have total := (claim.machine (resourceInput (Comparison64.Domain.resource [0xff] 0 1))
    (Comparison64.Domain.initial [0xff] 0 1) pre.machine).1
  have fault : step false (Comparison64.Domain.initial [0xff] 0 1) =
      .error (.inaccessibleInstruction 4097) := rfl
  have impossible := total.no_fault_prefix (fun _ => false)
    (Sequential.run_fault (choices := fun _ => false) (fuel := 0) fault)
  cases impossible

theorem unsupported_not_claims :
    ¬Claim .maximum64 [0xff] ∧ ¬Claim .minimum64 [0xff] ∧ ¬Claim .signedMaximum64 [0xff] :=
  ⟨fun claim => unsupported_not_semantic .unsignedMaximum claim.1,
    fun claim => unsupported_not_semantic .unsignedMinimum claim.1,
    fun claim => unsupported_not_semantic .signedMaximum claim.1⟩

theorem task_ids_distinct :
    (TaskID.maximum64 ≠ .minimum64) ∧ (TaskID.maximum64 ≠ .signedMaximum64) ∧
      (TaskID.minimum64 ≠ .signedMaximum64) := by decide

end EDSL.Tests.GradingComparison64

open Lean EDSL EDSL.Grading EDSLGrader EDSLGrader.Runtime

-- Check parser, quotation and registration together against independent
-- operation constants. A swapped signed/unsigned or max/min task must fail
-- kernel conversion even though all three retain the same callable profile.
run_cmd do
  let env := (← getEnv).toKernelEnv
  let cases : List (String × Name × Name) := [
    ("maximum64", ``TaskID.maximum64, ``Comparison64.Operation.unsignedMaximum),
    ("minimum64", ``TaskID.minimum64, ``Comparison64.Operation.unsignedMinimum),
    ("signedMaximum64", ``TaskID.signedMaximum64, ``Comparison64.Operation.signedMaximum)]
  for (spelling, idName, operation) in cases do
    let some id := taskID spelling | throwError "task spelling rejected: {spelling}"
    unless (registered id).profile == .sequentialReadOnlyX86CallableV1 do
      throwError "wrong callable profile for {spelling}"
    let idType := mkConst ``TaskID
    let literalID := mkConst idName
    let idEquality := mkApp3 (mkConst ``Eq [1]) idType (taskExpr id) literalID
    let idProof := mkApp2 (mkConst ``Eq.refl [1]) idType literalID
    match checkExpr env {} idEquality idProof `EDSLGrader.Internal.comparisonIDTest with
    | .error failure => throwError "wrong task ID for {spelling}: {failure}"
    | .ok _ => pure ()
    let taskType := mkConst ``Grading.Task
    let actual := mkApp (mkConst ``registered) (taskExpr id)
    let specification := mkApp (mkConst ``ofReadOnly)
      (mkApp (mkConst ``Comparison64.readOnlyTask) (mkConst operation))
    let equality := mkApp3 (mkConst ``Eq [2]) taskType actual specification
    let proof := mkApp2 (mkConst ``Eq.refl [2]) taskType specification
    match checkExpr env {} equality proof `EDSLGrader.Internal.comparisonRegistrationTest with
    | .error failure => throwError "wrong order specification for {spelling}: {failure}"
    | .ok _ => pure ()
  for spelling in ["Maximum64", "minimum64 ", "signedmaximum64", "unsignedMaximum64"] do
    unless (taskID spelling).isNone do
      throwError "unregistered spelling accepted: {spelling}"
  logInfo "All comparison spellings, quotations, mathematical registrations and profiles checked"

/-- Re-import the actual trusted module set without candidate modules. This
checks the import boundary even when client proofs exist in the shared tree. -/
def checkComparisonTrustedBoundary : IO Unit := do
  initSearchPath (← findSysroot)
  let trusted ← importModules #[{ module := `EDSL.Grading.Known },
    { module := `EDSL.Grading.Artifact },
    { module := `EDSL.Grading.CallStack.Artifact },
    { module := `EDSL.Grading.CallMemory64.Artifact },
    { module := `EDSL.Grading.CallMemoryLoop64.Artifact },
    { module := `EDSL.Grading.AtomicLogical64.Artifact },
    { module := `EDSL.Grading.AtomicSet64.Artifact }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  unless (trusted.find? `EDSL.Comparison64.Domain.nonvacuous).isSome do
    throw (IO.userError "independent comparison domain missing from trusted snapshot")
  for (name, _) in trusted.constants.toList do
    if (`EDSL.Comparison64.Client).isPrefixOf name then
      throw (IO.userError s!"comparison client imported into trusted snapshot: {name}")
  IO.println "PASS comparison trusted snapshot contains independent domain and excludes client proofs"

#eval checkComparisonTrustedBoundary

#print axioms EDSL.Comparison64.Domain.contract
#print axioms EDSL.Comparison64.Domain.resource_pre
#print axioms EDSL.Comparison64.Domain.nonvacuous
#print axioms EDSL.Grading.domain_nonvacuous
#print axioms EDSL.Tests.GradingComparison64.arbitrary_inputs
#print axioms EDSL.Tests.GradingComparison64.maximum_span_last_byte
#print axioms EDSL.Tests.GradingComparison64.unsupported_not_claims
#audit_edsl
