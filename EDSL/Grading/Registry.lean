/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.TaskFor
import EDSL.Arithmetic64.Multiply

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading
open X86 X86.Sequential

/-- Trusted additive task identifiers. The legacy branch retains the original
registry unchanged; new tasks can fix a distinct production execution model. -/
inductive RegistryID where
  | legacy (id : TaskID)
  | multiplyModulo64
  deriving DecidableEq, Repr

/-- Registration fixes both the production execution model and the complete
mathematical/resource task. Candidate bytes and proof terms select neither. -/
structure RegisteredTask where
  execution : ExecutionModel
  task : Task

/-- A closed trusted lookup. Existing tasks retain their original Bool claims;
full64 modular multiplication uses independent status-flag choices throughout
its execution and current-resource policies. -/
def registry : RegistryID → RegisteredTask
  | .legacy id => ⟨.bool, registered id⟩
  | .multiplyModulo64 =>
      ⟨.flags, ofReadOnlyFor .flags (PureCall.readOnlyTask Arithmetic64.multiplyModulo)⟩

/-- The trusted identifier fixes semantic quantification and task policies.
Useful raw/resource admission remains the original separate nonvacuity claim. -/
def RegisteredClaim (id : RegistryID) (bytes : List Byte) : Prop :=
  SemanticClaimFor (registry id).execution (registry id).task bytes ∧
    Nonvacuous (registry id).task bytes

theorem registry_legacy_execution (id : TaskID) :
    (registry (.legacy id)).execution = .bool := rfl

theorem registry_legacy_task (id : TaskID) :
    (registry (.legacy id)).task = registered id := rfl

theorem registry_multiplyModulo64_execution :
    (registry .multiplyModulo64).execution = .flags := rfl

theorem registry_multiplyModulo64_task :
    (registry .multiplyModulo64).task =
      ofReadOnlyFor .flags (PureCall.readOnlyTask Arithmetic64.multiplyModulo) := rfl

/-- Every original task claim has exactly its original semantics, policies,
resource return hook and useful-domain witnesses under the additive registry. -/
theorem registeredClaim_legacy_iff (id : TaskID) (bytes : List Byte) :
    RegisteredClaim (.legacy id) bytes ↔ Claim id bytes :=
  and_congr (SemanticClaimFor.bool (registered id) bytes) Iff.rfl

/-- Registered multiplication semantics are exactly the shared read-only
callable contract quantified over independent status-flag choice streams. -/
theorem registered_multiplyModulo64_semanticClaim_iff (bytes : List Byte) :
    SemanticClaimFor (registry .multiplyModulo64).execution
        (registry .multiplyModulo64).task bytes ↔
      ReadOnlySemanticClaimFor .flags (PureCall.readOnlyTask Arithmetic64.multiplyModulo) bytes :=
  ofReadOnlyFor_semanticClaim_iff .flags (PureCall.readOnlyTask Arithmetic64.multiplyModulo) bytes

/-- Registration retains the same useful raw and current-resource witnesses.
No cost, execution result or extra domain premise is added to admission. -/
theorem registered_multiplyModulo64_nonvacuous_iff (bytes : List Byte) :
    Nonvacuous (registry .multiplyModulo64).task bytes ↔
      ReadOnlyNonvacuous (PureCall.readOnlyTask Arithmetic64.multiplyModulo) bytes :=
  ofReadOnlyFor_nonvacuous_iff .flags (PureCall.readOnlyTask Arithmetic64.multiplyModulo) bytes

/-- Complete multiplication registration, including separate nonvacuity. -/
theorem registeredClaim_multiplyModulo64_iff (bytes : List Byte) :
    RegisteredClaim .multiplyModulo64 bytes ↔
      (ReadOnlySemanticClaimFor .flags (PureCall.readOnlyTask Arithmetic64.multiplyModulo) bytes ∧
        ReadOnlyNonvacuous (PureCall.readOnlyTask Arithmetic64.multiplyModulo) bytes) :=
  and_congr (registered_multiplyModulo64_semanticClaim_iff bytes)
    (registered_multiplyModulo64_nonvacuous_iff bytes)

end EDSL.Grading
