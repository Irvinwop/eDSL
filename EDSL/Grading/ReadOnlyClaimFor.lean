/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ReadOnlyTask.Core
import EDSL.Grading.PolicyFor

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading
open X86 X86.Sequential

/-- The original mathematical and resource domains, quantified over every
choice stream of a closed production model. The task's original `Resource`,
admission predicates and mathematical postcondition are retained. Current
resources hold at every continuing prefix and at return in the resource
domain. No extra task premise, registration or certificate support is added.
The callable environmental assumptions documented by `Profile` still apply;
choice streams supply undefined flag values, not a hardware scheduler. -/
structure ReadOnlySemanticClaimFor (model : ExecutionModel) (task : ReadOnlyTask)
    (bytes : List Byte) : Prop where
  machine : ∀ input initial, task.pre bytes input initial →
    Engine.AllExecutions model.transition initial (fun result => task.post input initial result.state) ∧
      ReadOnlyPolicyFor model initial (fun _ => True) (fun _ _ => True)
  resource : ∀ resource initial, task.resourcePre bytes resource initial →
    Engine.AllExecutions model.transition initial (fun result =>
      task.post (task.input resource) initial result.state ∧ task.current resource result.state) ∧
      ReadOnlyPolicyFor model initial (task.current resource) (task.permission resource)

/-- An existing Bool claim retains both complete universal domains. -/
theorem ReadOnlySemanticClaimFor.ofBool {task : ReadOnlyTask} {bytes : List Byte}
    (claim : ReadOnlySemanticClaim task bytes) :
    ReadOnlySemanticClaimFor .bool task bytes :=
  ⟨claim.machine, claim.resource⟩

/-- Bool specialization recovers the original claim without additional
premises or changes to either postcondition. -/
theorem ReadOnlySemanticClaimFor.toBool {task : ReadOnlyTask} {bytes : List Byte}
    (claim : ReadOnlySemanticClaimFor .bool task bytes) :
    ReadOnlySemanticClaim task bytes :=
  ⟨claim.machine, claim.resource⟩

/-- Exact compatibility with the original semantic claim. Nonvacuity remains
the separate unchanged `ReadOnlyNonvacuous` obligation. -/
theorem ReadOnlySemanticClaimFor.bool (task : ReadOnlyTask) (bytes : List Byte) :
    ReadOnlySemanticClaimFor .bool task bytes ↔ ReadOnlySemanticClaim task bytes :=
  ⟨ReadOnlySemanticClaimFor.toBool, ReadOnlySemanticClaimFor.ofBool⟩

end EDSL.Grading
