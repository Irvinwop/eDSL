/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Resources
import EDSL.Grading.ReadOnlyClaimFor

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.PureCall
open X86 X86.Sequential

/-- The original raw policy over a closed production execution model. Every
actual continuing prefix retains complete initial memory; operand permission
remains tied to the original caller slot by `RawRead`. Stable ordinary RAM and
absence of asynchronous interference remain sequential target assumptions.
Logical ownership comes from the separately supplied resource admission. -/
def RawPolicyFor (model : ExecutionModel) (initial : State) : Prop :=
  Grading.ReadOnlyPolicyFor model initial (fun before => before.memory = initial.memory)
    (fun _ read => RawRead initial read)

/-- Bool selection retains the original raw memory and caller-slot policy. -/
theorem RawPolicyFor.bool (initial : State) :
    RawPolicyFor .bool initial ↔ RawPolicy initial :=
  Iff.rfl

/-- Lift raw correctness and policy for every selected-model choice stream to
the unchanged raw and resource domains. Whole-memory equality transports the
same supplied OS world, including original code/caller loans, owners, epochs
and permissions, at every actual continuing prefix and at return. Resource
admission supplies logical ownership; readable RAM alone grants no authority.
No successful future execution is added to admission.

The callable profile assumes stable ordinary RAM and no asynchronous
interference. Native loading, physical CPU/OS correspondence and enforcement
of these environmental assumptions are outside this modeled resource bridge. -/
theorem semantics_of_rawFor (model : ExecutionModel) {spec : Spec} {bytes : List Byte}
    (raw : ∀ input initial, Pre spec bytes input initial →
      Engine.AllExecutions model.transition initial
        (fun result => Post spec input initial result.state) ∧ RawPolicyFor model initial) :
    Grading.ReadOnlySemanticClaimFor model (readOnlyTask spec) bytes := by
  constructor
  · intro input initial pre
    obtain ⟨executions, policy⟩ := raw input initial pre
    exact ⟨executions, policy.mono (by intros; trivial) (by intros; trivial)⟩
  · intro resource initial pre
    obtain ⟨executions, policy⟩ := raw (resourceInput resource) initial pre.machine
    refine ⟨?_, policy.mono ?_ ?_⟩
    · intro choices
      obtain ⟨result, execution, post⟩ := executions choices
      exact ⟨result, execution, post, pre.current.sameMemory post.memory⟩
    · intro before memory
      exact pre.current.sameMemory memory
    · intro before read allowed
      exact pre.read_permission allowed

end EDSL.PureCall
