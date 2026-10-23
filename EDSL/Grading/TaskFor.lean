/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Task
import EDSL.Grading.ReadOnlyClaimFor

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading
open X86 X86.Sequential

/-- The original task claim with only its execution quantifiers indexed by a
closed production model. Both universal admission domains and the task's fixed
machine and resource policies are unchanged. The return hook receives the
actual execution result and initial state, including for mutable resource
histories. Useful-input evidence remains separate from semantic correctness.
The task remains model-independent; selecting an execution domain establishes
no correspondence with native execution or discharge of the environmental
assumptions documented by `Profile`. -/
structure SemanticClaimFor (model : ExecutionModel) (task : Task) (bytes : List Byte) : Prop where
  machine : ∀ input initial, task.pre bytes input initial →
    Engine.AllExecutions model.transition initial (fun result => task.post input initial result.state) ∧
      task.machinePolicy bytes input initial
  resource : ∀ resource initial, task.resourcePre bytes resource initial →
    Engine.AllExecutions model.transition initial (fun result =>
      task.post (task.input resource) initial result.state ∧
        task.resourceReturn bytes resource initial result) ∧
      task.resourcePolicy bytes resource initial

/-- Every original task claim specializes directly to the Bool model,
retaining its policies and actual-result resource return predicate. -/
theorem SemanticClaimFor.ofBool {task : Task} {bytes : List Byte}
    (claim : SemanticClaim task bytes) : SemanticClaimFor .bool task bytes :=
  ⟨claim.machine, claim.resource⟩

/-- Bool specialization recovers the original claim for an arbitrary task,
including tasks whose return hook depends on the actual lifted history. -/
theorem SemanticClaimFor.toBool {task : Task} {bytes : List Byte}
    (claim : SemanticClaimFor .bool task bytes) : SemanticClaim task bytes :=
  ⟨claim.machine, claim.resource⟩

/-- Exact Bool compatibility on both full admission domains, with no change
to the registered policies or resource return hook. -/
theorem SemanticClaimFor.bool (task : Task) (bytes : List Byte) :
    SemanticClaimFor .bool task bytes ↔ SemanticClaim task bytes :=
  ⟨SemanticClaimFor.toBool, SemanticClaimFor.ofBool⟩

/-- The original read-only adapter with policies closed over the selected
execution model. As in `ofReadOnly`, the profile is exactly
`Profile.sequentialReadOnlyX86CallableV1`; all admission, mathematical, useful
and resource fields, including current authority at the actual return, are
retained. Model selection concerns the modeled execution domain and makes no
native correspondence claim. `Task` has no model field; its policies are fixed
closures. This opt-in adapter adds no registry or candidate model selection. -/
def ofReadOnlyFor (model : ExecutionModel) (old : ReadOnlyTask) : Task where
  profile := .sequentialReadOnlyX86CallableV1
  Input := old.Input
  pre := old.pre
  post := old.post
  useful := old.useful
  Resource := old.Resource
  input := old.input
  resourcePre := old.resourcePre
  machinePolicy _ _ initial := ReadOnlyPolicyFor model initial (fun _ => True) (fun _ _ => True)
  resourcePolicy _ resource initial :=
    ReadOnlyPolicyFor model initial (old.current resource) (old.permission resource)
  resourceReturn _ resource _ result := old.current resource result.state

/-- Bool selection is definitionally the complete original adapter, including
its fixed profile, policies and actual-result resource return predicate. -/
theorem ofReadOnlyFor_bool (old : ReadOnlyTask) :
    ofReadOnlyFor .bool old = ofReadOnly old :=
  rfl

/-- The generic read-only adapter retains exactly the execution-indexed
read-only contract on every original raw and resource input/state. -/
theorem ofReadOnlyFor_semanticClaim_iff (model : ExecutionModel) (old : ReadOnlyTask)
    (bytes : List Byte) :
    SemanticClaimFor model (ofReadOnlyFor model old) bytes ↔
      ReadOnlySemanticClaimFor model old bytes := by
  constructor
  · intro claim
    exact ⟨claim.machine, claim.resource⟩
  · intro claim
    exact ⟨claim.machine, claim.resource⟩

/-- Nonvacuity uses the very same machine and resource witnesses as the
original read-only task, without execution, cost or extra domain assumptions. -/
theorem ofReadOnlyFor_nonvacuous_iff (model : ExecutionModel) (old : ReadOnlyTask)
    (bytes : List Byte) :
    Nonvacuous (ofReadOnlyFor model old) bytes ↔ ReadOnlyNonvacuous old bytes := by
  constructor
  · intro claim
    exact ⟨claim.machine, claim.resource⟩
  · intro claim
    exact ⟨claim.machine, claim.resource⟩

/-- Full read-only adapter equivalence, including independent useful-domain
evidence without restricting either universal semantic domain. -/
theorem ofReadOnlyFor_claim_iff (model : ExecutionModel) (old : ReadOnlyTask)
    (bytes : List Byte) :
    (SemanticClaimFor model (ofReadOnlyFor model old) bytes ∧
      Nonvacuous (ofReadOnlyFor model old) bytes) ↔
      (ReadOnlySemanticClaimFor model old bytes ∧ ReadOnlyNonvacuous old bytes) := by
  exact and_congr (ofReadOnlyFor_semanticClaim_iff model old bytes)
    (ofReadOnlyFor_nonvacuous_iff model old bytes)

end EDSL.Grading
