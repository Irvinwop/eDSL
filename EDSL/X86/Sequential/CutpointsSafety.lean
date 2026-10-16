/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Cutpoints

namespace EDSL.X86.Sequential.Cutpoints

variable {Location : Type u} {flow : Layout Location} {Post : State → Prop}
  {AllowedRead : State → Read → Prop}

/-- Reachability retains a segment's ghost context. At a cutpoint successor the
context resets using `start`; at other successors the local VC preserves it. -/
def Ghost (cert : Certificate flow Post AllowedRead) (state : State) : Prop :=
  ∃ source budget node, cert.Interior source budget node state

theorem Certificate.ghost_start (cert : Certificate flow Post AllowedRead)
    {entry : Location} {initial : State} (isCut : flow.cutpoint entry = true)
    (valid : cert.Inv entry initial) : Ghost cert initial :=
  ⟨entry, cert.rank entry initial, entry, cert.start entry initial isCut valid⟩

/-- Preservation follows a given actual continuing transition, including the
negative fact that an atomic outcome cannot satisfy this read-only profile. -/
theorem Certificate.continues_ghost (cert : Certificate flow Post AllowedRead)
    {initial final : State} (valid : Ghost cert initial) {af : Bool}
    {outcome : StepResult} {reads : List Read}
    (chosen : Sequential.step af initial = .ok ⟨outcome, reads⟩)
    (next : nextState outcome = some final) : Ghost cert final := by
  obtain ⟨source, budget, node, interior⟩ := valid
  obtain ⟨observation, actual, _, after⟩ := cert.localVC source budget node initial interior af
  have same := Except.ok.inj (actual.symm.trans chosen)
  cases same
  cases outcome with
  | returned state | syscall request => cases next
  | atomic event middle => exact False.elim after
  | next middle =>
    simp only [nextState, Option.some.injEq] at next
    subst final
    obtain ⟨dest, _, cut | within⟩ := after
    · obtain ⟨isCut, invariant, _⟩ := cut
      exact cert.ghost_start isCut invariant
    · exact ⟨source, budget, dest, within.2⟩

/-- Every finite continuing trace of the actual machine preserves the local
certificate, independently of its choices or its eventual return behavior. -/
theorem Certificate.block_ghost (cert : Certificate flow Post AllowedRead)
    {initial final : State} (valid : Ghost cert initial) {choices : Choices}
    {count : Nat} {reads : List Read} (block : Block choices initial final count reads) :
    Ghost cert final := by
  induction block with
  | nil => exact valid
  | next step tail induction | atomic step tail induction =>
    exact induction (cert.continues_ghost valid step rfl)

theorem Certificate.reachable_ghost (cert : Certificate flow Post AllowedRead)
    {initial before : State} (valid : Ghost cert initial) (reachable : Reachable initial before) :
    Ghost cert before := by
  obtain ⟨_, _, _, block⟩ := reachable
  exact cert.block_ghost valid block

/-- Local read authorization is tied to the observation of a given actual
successful transition and to that transition's current pre-instruction state. -/
theorem Certificate.observed_reads_allowed (cert : Certificate flow Post AllowedRead)
    {initial : State} (valid : Ghost cert initial) {af : Bool} {observation : Observation}
    (chosen : Sequential.step af initial = .ok observation) :
    ∀ read ∈ observation.reads, AllowedRead initial read := by
  obtain ⟨source, budget, node, interior⟩ := valid
  obtain ⟨expected, actual, allowed, _⟩ := cert.localVC source budget node initial interior af
  have same := Except.ok.inj (actual.symm.trans chosen)
  cases same
  exact allowed

/-- At every reachable pre-state both AF choices are enabled and cannot cross a
syscall boundary. This separate prefix proof retains the interior ghost rather
than pretending a cutpoint invariant holds at every instruction. -/
theorem Certificate.safe_from_ghost (cert : Certificate flow Post AllowedRead)
    {initial : State} (valid : Ghost cert initial) : Safe initial := by
  intro before reachable af
  obtain ⟨source, budget, node, interior⟩ := cert.reachable_ghost valid reachable
  obtain ⟨observation, actual, _, after⟩ := cert.localVC source budget node before interior af
  refine ⟨observation, actual, ?_⟩
  intro request same
  rw [same] at after
  exact after

theorem Certificate.safe (cert : Certificate flow Post AllowedRead)
    {entry : Location} {initial : State} (isCut : flow.cutpoint entry = true)
    (valid : cert.Inv entry initial) : Safe initial :=
  cert.safe_from_ghost (cert.ghost_start isCut valid)

/-- Every accumulated read has an exact actual origin, a preserved interior
certificate there, permission in that current state, and successful current-RAM
access. This includes every byte of a successful RET operand read. -/
theorem Certificate.execution_read_origin (cert : Certificate flow Post AllowedRead)
    {initial : State} (valid : Ghost cert initial) {choices : Choices} {result : Result}
    (execution : Executes choices initial result) {read : Read} (member : read ∈ result.reads) :
    ∃ count before priorReads observation, count < result.instructions ∧
      Block choices initial before count priorReads ∧
        Sequential.step (choices count) before = .ok observation ∧ read ∈ observation.reads ∧
          Ghost cert before ∧ AllowedRead before read ∧ OperandReadSucceeds before read := by
  obtain ⟨count, before, priorReads, observation, bound, block, actual, present⟩ :=
    execution.read_origin member
  have ghost := cert.block_ghost valid block
  exact ⟨count, before, priorReads, observation, bound, block, actual, present, ghost,
    cert.observed_reads_allowed ghost actual read present, observed_reads_succeed actual read present⟩

theorem Certificate.block_read_origin (cert : Certificate flow Post AllowedRead)
    {initial final : State} (valid : Ghost cert initial) {choices : Choices}
    {count : Nat} {reads : List Read} (block : Block choices initial final count reads)
    {read : Read} (member : read ∈ reads) :
    ∃ index before priorReads observation, index < count ∧
      Block choices initial before index priorReads ∧
        Sequential.step (choices index) before = .ok observation ∧ read ∈ observation.reads ∧
          Ghost cert before ∧ AllowedRead before read ∧ OperandReadSucceeds before read := by
  obtain ⟨index, before, priorReads, observation, bound, priorBlock, actual, present⟩ :=
    block.read_origin member
  have ghost := cert.block_ghost valid priorBlock
  exact ⟨index, before, priorReads, observation, bound, priorBlock, actual, present, ghost,
    cert.observed_reads_allowed ghost actual read present, observed_reads_succeed actual read present⟩

theorem Certificate.run_read_origin (cert : Certificate flow Post AllowedRead)
    {initial : State} (valid : Ghost cert initial) {choices : Choices} {result : Result} {fuel : Nat}
    (success : run choices fuel initial = .ok result) {read : Read} (member : read ∈ result.reads) :
    ∃ count before priorReads observation, count < result.instructions ∧
      Block choices initial before count priorReads ∧
        Sequential.step (choices count) before = .ok observation ∧ read ∈ observation.reads ∧
          Ghost cert before ∧ AllowedRead before read ∧ OperandReadSucceeds before read :=
  cert.execution_read_origin valid (run_sound success) member

end EDSL.X86.Sequential.Cutpoints
