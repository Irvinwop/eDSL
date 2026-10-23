/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.TaskFor
import EDSL.Arithmetic64.Multiply
import EDSL.Scalar32.Signum

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Grading
open X86 X86.Sequential

/-- Trusted additive task identifiers. The legacy branch retains the original
registry unchanged; new tasks can fix a distinct production execution model. -/
inductive RegistryID where
  | legacy (id : TaskID)
  | multiplyModulo64
  | signumSigned32
  deriving DecidableEq, Repr

/-- Registration fixes both the production execution model and the complete
mathematical/resource task. Candidate bytes and proof terms select neither. -/
structure RegisteredTask where
  execution : ExecutionModel
  task : Task

/-- A closed trusted lookup. Existing tasks retain their original Bool claims;
full64 modular multiplication and signed low32 signum use independent
status-flag choices throughout execution and current-resource policies. -/
def registry : RegistryID → RegisteredTask
  | .legacy id => ⟨.bool, registered id⟩
  | .multiplyModulo64 =>
      ⟨.flags, ofReadOnlyFor .flags (PureCall.readOnlyTask Arithmetic64.multiplyModulo)⟩
  | .signumSigned32 =>
      ⟨.flags, ofReadOnlyFor .flags (PureCall.readOnlyTask Scalar32.signumSigned)⟩

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

theorem registry_signumSigned32_execution :
    (registry .signumSigned32).execution = .flags := rfl

theorem registry_signumSigned32_task :
    (registry .signumSigned32).task =
      ofReadOnlyFor .flags (PureCall.readOnlyTask Scalar32.signumSigned) := rfl

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

/-- Registered signum semantics use the independent integer-order contract on
every admitted raw and resource input, for every status-flag choice stream. -/
theorem registered_signumSigned32_semanticClaim_iff (bytes : List Byte) :
    SemanticClaimFor (registry .signumSigned32).execution
        (registry .signumSigned32).task bytes ↔
      ReadOnlySemanticClaimFor .flags (PureCall.readOnlyTask Scalar32.signumSigned) bytes :=
  ofReadOnlyFor_semanticClaim_iff .flags (PureCall.readOnlyTask Scalar32.signumSigned) bytes

/-- Signum retains the complete raw and current-resource admission domains
and their separate useful witnesses, without an execution or cost premise. -/
theorem registered_signumSigned32_nonvacuous_iff (bytes : List Byte) :
    Nonvacuous (registry .signumSigned32).task bytes ↔
      ReadOnlyNonvacuous (PureCall.readOnlyTask Scalar32.signumSigned) bytes :=
  ofReadOnlyFor_nonvacuous_iff .flags (PureCall.readOnlyTask Scalar32.signumSigned) bytes

/-- Complete signed low32 signum registration, including separate nonvacuity. -/
theorem registeredClaim_signumSigned32_iff (bytes : List Byte) :
    RegisteredClaim .signumSigned32 bytes ↔
      (ReadOnlySemanticClaimFor .flags (PureCall.readOnlyTask Scalar32.signumSigned) bytes ∧
        ReadOnlyNonvacuous (PureCall.readOnlyTask Scalar32.signumSigned) bytes) :=
  and_congr (registered_signumSigned32_semanticClaim_iff bytes)
    (registered_signumSigned32_nonvacuous_iff bytes)

end EDSL.Grading
