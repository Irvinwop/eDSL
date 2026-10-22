/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Policy
import EDSL.X86.Sequential.ExecutionModel

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading
open X86 X86.Sequential

/-- The original read-only policy over a closed production execution model.
Every actual continuing prefix retains `Current` and decodes an instruction
in the unchanged read-only whitelist. Every choice must succeed; every
observed operand read must be permitted and succeed in that pre-state.
Continuing and returning steps preserve the complete memory, including its
accessibility, executability and writability maps. Atomic and syscall outcomes
are excluded. Instruction fetches remain checked by actual decoding. -/
def ReadOnlyPolicyFor (model : ExecutionModel) (initial : State)
    (Current : State → Prop) (AllowedRead : State → Read → Prop) : Prop :=
  ∀ before, Engine.Reachable model.transition initial before →
    Current before ∧ DecodesReadOnly before ∧
      ∀ choice, ∃ observation, model.transition choice before = .ok observation ∧
        (∀ read ∈ observation.reads, AllowedRead before read ∧ OperandReadSucceeds before read) ∧
        match observation.result with
        | .next after | .returned after => after.memory = before.memory
        | .atomic _ _ | .syscall _ => False

theorem ReadOnlyPolicyFor.mono {model : ExecutionModel} {initial : State}
    {Current NewCurrent : State → Prop} {AllowedRead NewAllowedRead : State → Read → Prop}
    (policy : ReadOnlyPolicyFor model initial Current AllowedRead)
    (current : ∀ before, Current before → NewCurrent before)
    (permission : ∀ before read, AllowedRead before read → NewAllowedRead before read) :
    ReadOnlyPolicyFor model initial NewCurrent NewAllowedRead := by
  intro before reachable
  obtain ⟨present, decoded, enabled⟩ := policy before reachable
  refine ⟨current before present, decoded, ?_⟩
  intro choice
  obtain ⟨observation, actual, reads, after⟩ := enabled choice
  exact ⟨observation, actual,
    fun read member => ⟨permission before read (reads read member).1, (reads read member).2⟩, after⟩

/-- Each read in an actual returning execution originates at a continuing
prefix with current resources, read permission and successful access. Duplicate
read records need not select distinct occurrences. -/
theorem ReadOnlyPolicyFor.read_origin {model : ExecutionModel} {initial : State}
    {Current : State → Prop} {AllowedRead : State → Read → Prop}
    (policy : ReadOnlyPolicyFor model initial Current AllowedRead)
    {choices : ChoiceStream model.Choice} {result : Result}
    (execution : Engine.Executes model.transition choices initial result)
    {read : Read} (member : read ∈ result.reads) :
    ∃ count before priorReads observation, count < result.instructions ∧
      Engine.Block model.transition choices initial before count priorReads ∧
      model.transition (choices count) before = .ok observation ∧ read ∈ observation.reads ∧
      Current before ∧ AllowedRead before read ∧ OperandReadSucceeds before read := by
  obtain ⟨count, before, priorReads, observation, bound, block, actual, present⟩ :=
    Engine.Executes.read_origin model.transition execution member
  have reachable : Engine.Reachable model.transition initial before :=
    ⟨choices, count, priorReads, block⟩
  obtain ⟨current, _, enabled⟩ := policy before reachable
  obtain ⟨expected, chosen, reads, _⟩ := enabled (choices count)
  have same := Except.ok.inj (chosen.symm.trans actual)
  cases same
  exact ⟨count, before, priorReads, observation, bound, block, actual, present,
    current, (reads read present).1, (reads read present).2⟩

/-- Actual reachable decoding of a forbidden instruction contradicts the
policy, even if a store would preserve or later restore all memory values. -/
theorem ReadOnlyPolicyFor.rejects_instruction {model : ExecutionModel}
    {initial before : State} {Current : State → Prop} {AllowedRead : State → Read → Prop}
    (policy : ReadOnlyPolicyFor model initial Current AllowedRead)
    (reachable : Engine.Reachable model.transition initial before)
    {instruction : Sequential.Instruction}
    (decoded : Sequential.decodeAt before = .ok instruction)
    (forbidden : CFG.readOnly instruction = false) : False := by
  obtain ⟨_, ⟨expected, actual, allowed⟩, _⟩ := policy before reachable
  have same := Except.ok.inj (actual.symm.trans decoded)
  cases same
  rw [forbidden] at allowed
  cases allowed

/-- Exact compatibility: Bool selection reduces to the original policy with
the same reachability, whitelist, permissions and memory/effect obligations. -/
theorem ReadOnlyPolicyFor.bool (initial : State) (Current : State → Prop)
    (AllowedRead : State → Read → Prop) :
    ReadOnlyPolicyFor .bool initial Current AllowedRead ↔
      ReadOnlyPolicy initial Current AllowedRead :=
  Iff.rfl

end EDSL.Grading
