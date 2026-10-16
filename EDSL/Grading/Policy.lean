/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGVerification

namespace EDSL.Grading
open X86 X86.Sequential

/-- Authority of the instruction decoded from the current executable memory.
The whitelist excludes stores even when they write the existing value, as well
as locked instructions, atomics, and syscalls. -/
def DecodesReadOnly (before : State) : Prop :=
  ∃ instruction, Sequential.decodeAt before = .ok instruction ∧ CFG.readOnly instruction = true

/-- Every actual continuing prefix retains the current resource contract.
Both AF choices must enable an actual step; every observed operand read must
be permitted and succeed in that pre-state. Each step preserves the complete
memory, including accessibility, executability, and writability maps.

This semantic policy has no CFG, trace order, instruction cost, or proof-shape
parameter. Instruction-fetch success is part of the actual decode/step;
`AllowedRead` governs the executor's explicit data and stack operands. -/
def ReadOnlyPolicy (initial : State) (Current : State → Prop)
    (AllowedRead : State → Read → Prop) : Prop :=
  ∀ before, Reachable initial before →
    Current before ∧ DecodesReadOnly before ∧
      ∀ af, ∃ observation, step af before = .ok observation ∧
        (∀ read ∈ observation.reads, AllowedRead before read ∧ OperandReadSucceeds before read) ∧
        match observation.result with
        | .next after | .returned after => after.memory = before.memory
        | .atomic _ _ | .syscall _ => False

theorem ReadOnlyPolicy.mono {initial : State} {Current NewCurrent : State → Prop}
    {AllowedRead NewAllowedRead : State → Read → Prop}
    (policy : ReadOnlyPolicy initial Current AllowedRead)
    (current : ∀ before, Current before → NewCurrent before)
    (permission : ∀ before read, AllowedRead before read → NewAllowedRead before read) :
    ReadOnlyPolicy initial NewCurrent NewAllowedRead := by
  intro before reachable
  obtain ⟨present, decoded, enabled⟩ := policy before reachable
  refine ⟨current before present, decoded, ?_⟩
  intro af
  obtain ⟨observation, actual, reads, after⟩ := enabled af
  exact ⟨observation, actual,
    fun read member => ⟨permission before read (reads read member).1, (reads read member).2⟩, after⟩

/-- Any actual returning execution has current-resource origins for its reads,
without a CFG premise. Membership yields an existential origin; identical
duplicate records need not select distinct occurrences. -/
theorem ReadOnlyPolicy.read_origin {initial : State} {Current : State → Prop}
    {AllowedRead : State → Read → Prop} (policy : ReadOnlyPolicy initial Current AllowedRead)
    {choices : Choices} {result : Result} (execution : Executes choices initial result)
    {read : Read} (member : read ∈ result.reads) :
    ∃ count before priorReads observation, count < result.instructions ∧
      Block choices initial before count priorReads ∧
      step (choices count) before = .ok observation ∧ read ∈ observation.reads ∧
      Current before ∧ AllowedRead before read ∧ OperandReadSucceeds before read := by
  obtain ⟨count, before, priorReads, observation, bound, block, actual, present⟩ :=
    execution.read_origin member
  have reachable : Reachable initial before := ⟨choices, count, priorReads, block⟩
  obtain ⟨current, _, enabled⟩ := policy before reachable
  obtain ⟨expected, chosen, reads, _⟩ := enabled (choices count)
  have same := Except.ok.inj (chosen.symm.trans actual)
  cases same
  exact ⟨count, before, priorReads, observation, bound, block, actual, present,
    current, (reads read present).1, (reads read present).2⟩

/-- Reusable proof route from byte-bound annotations. `Valid` is separately
proved evidence for this adapter, never a task precondition. The current-state
argument uses local invariants rather than an assumed future execution. -/
theorem annotations_policy {bytes : List Byte} {graph : CFG.Graph} {base : Word}
    {Post : State → Prop} {AllowedRead : State → Read → Prop}
    (annotations : CFG.Annotations bytes graph base Post AllowedRead)
    (valid : CFG.Valid bytes graph) {initial : State}
    (admitted : annotations.Inv valid.entry initial) (Current : State → Prop)
    (current : ∀ source budget node before,
      annotations.Interior source budget node before → Current before) :
    ReadOnlyPolicy initial Current AllowedRead := by
  intro before reachable
  let certificate := annotations.certificate valid
  have start := certificate.ghost_start valid.entry_cutpoint admitted
  obtain ⟨source, budget, node, inside⟩ := certificate.reachable_ghost start reachable
  obtain ⟨code, pc⟩ := annotations.binding source budget node before inside
  have decoded := valid.decoded code node before rfl pc
  have allowed := (valid.nodes node).2.2.1
  refine ⟨current source budget node before inside,
    ⟨(graph.node node).instruction, decoded, allowed⟩, ?_⟩
  intro af
  obtain ⟨observation, actual, reads, _⟩ := certificate.localVC source budget node before inside af
  have effect : execute before (graph.node node).instruction af = .ok observation := by
    rw [← step_eq_execute af decoded]
    exact actual
  refine ⟨observation, actual, ?_, ?_⟩
  · intro read member
    exact ⟨reads read member, observed_reads_succeed actual read member⟩
  · obtain ⟨after, next | ⟨returned, _⟩⟩ := CFG.execute_result allowed effect
    · rw [next]
      exact CFG.execute_next_memory allowed effect next
    · rw [returned]
      exact CFG.execute_returned_memory allowed effect returned

/-- A forbidden instruction at any actual reachable pre-state contradicts the
policy, regardless of final memory equality or later restoration. -/
theorem ReadOnlyPolicy.rejects_instruction {initial before : State}
    {Current : State → Prop} {AllowedRead : State → Read → Prop}
    (policy : ReadOnlyPolicy initial Current AllowedRead) (reachable : Reachable initial before)
    {instruction : Sequential.Instruction} (decoded : Sequential.decodeAt before = .ok instruction)
    (forbidden : CFG.readOnly instruction = false) : False := by
  obtain ⟨_, ⟨expected, actual, allowed⟩, _⟩ := policy before reachable
  have same := Except.ok.inj (actual.symm.trans decoded)
  cases same
  rw [forbidden] at allowed
  cases allowed

/-- A store is rejected even when it would write back the same value. -/
theorem policy_rejects_store {initial : State} {Current : State → Prop}
    {AllowedRead : State → Read → Prop} (policy : ReadOnlyPolicy initial Current AllowedRead)
    (store : Sequential.decodeAt initial = .ok (.legacy .storeEsiRdi)) : False :=
  policy.rejects_instruction ⟨fun _ => false, 0, [], Block.nil⟩ store rfl

end EDSL.Grading
