/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicSet64.Execution
import EDSL.AtomicSet64Domain

namespace EDSL.Grading.AtomicSet64
open X86 OS.AddressSpace

/-- A bit whose independently requested membership must change. Admission
still includes all zero, equal and unchanged inputs. -/
def UsefulBits : Logical64.Operation → Word → Word → Prop
  | .intersection, old, mask => ∃ index : Fin 64, Logical64.HasBit old index ∧ ¬Logical64.HasBit mask index
  | .union, old, mask => ∃ index : Fin 64, ¬Logical64.HasBit old index ∧ Logical64.HasBit mask index
  | .symmetricDifference, _, mask => ∃ index : Fin 64, Logical64.HasBit mask index

/-- Usefulness concerns the actual initial RAM read and original RSI. -/
def Useful (desired : Logical64.Operation) (initial : X86.State) : Prop :=
  ∃ old, loadQWord initial.memory (initial.registers .rdi) = .ok old ∧
    UsefulBits desired old (initial.registers .rsi)

theorem UsefulBits.changes {desired old mask final}
    (useful : UsefulBits desired old mask)
    (mathematical : Logical64.MathematicalResult desired old mask final) : final ≠ old := by
  intro equal
  subst final
  cases desired with
  | intersection =>
    obtain ⟨index, present, absent⟩ := useful
    exact absent ((mathematical index).mp present).2
  | union =>
    obtain ⟨index, absent, present⟩ := useful
    exact absent ((mathematical index).mpr (Or.inr present))
  | symmetricDifference =>
    obtain ⟨index, present⟩ := useful
    by_cases oldBit : Logical64.HasBit old index
    · rcases (mathematical index).mp oldBit with left | right
      · exact left.2 present
      · exact right.2 oldBit
    · exact oldBit ((mathematical index).mpr (Or.inr ⟨present, oldBit⟩))

/-- Closed resource-first uninterrupted callable set task for arbitrary bytes.
Admission is exactly the existing present-resource Pre, without decoder, opcode,
length, instruction count, event count or future-execution requirements.
Every AF stream must return through actual covered CPU/OS transitions. -/
def SemanticClaim (desired : Logical64.Operation) (candidate : List Byte) : Prop :=
  ∀ input shared initial, EDSL.AtomicSet64.Pre candidate input shared initial →
    ∀ choices, ∃ evolved result,
      CoveredExecution (frame candidate input shared initial) choices shared initial evolved result ∧
      Post desired (frame candidate input shared initial) shared initial evolved result.state

def Nonvacuous (desired : Logical64.Operation) (candidate : List Byte) : Prop :=
  ∃ input shared initial, EDSL.AtomicSet64.Pre candidate input shared initial ∧ Useful desired initial

def Claim (desired : Logical64.Operation) (candidate : List Byte) : Prop := SemanticClaim desired candidate ∧ Nonvacuous desired candidate

/-- Arbitrary byte spans have checked current-resource witnesses, including
unsupported/RET-only bytes. This reuses the existing domain constructor. -/
theorem nonvacuous_bytes (desired : Logical64.Operation) (candidate : List Byte)
    (positive : 0 < candidate.length) (bound : candidate.length ≤ 4096) :
    Nonvacuous desired candidate := by
  cases desired with
  | intersection =>
    exact ⟨EDSL.AtomicSet64.Domain.input, _, _,
      EDSL.AtomicSet64.Domain.admitted_bytes candidate positive bound 0x8000000000000000 0,
      0x8000000000000000, AtomicLogical64.Domain.old_read candidate bound _ _,
      ⟨63, by decide⟩, by unfold Logical64.HasBit; decide,
      by change ¬Logical64.HasBit (0 : Word) ⟨63, by decide⟩; unfold Logical64.HasBit; decide⟩
  | union =>
    exact ⟨EDSL.AtomicSet64.Domain.input, _, _,
      EDSL.AtomicSet64.Domain.admitted_bytes candidate positive bound 0 0x8000000000000000,
      0, AtomicLogical64.Domain.old_read candidate bound _ _,
      ⟨63, by decide⟩, by unfold Logical64.HasBit; decide,
      by change Logical64.HasBit (0x8000000000000000 : Word) ⟨63, by decide⟩; unfold Logical64.HasBit; decide⟩
  | symmetricDifference =>
    exact ⟨EDSL.AtomicSet64.Domain.input, _, _,
      EDSL.AtomicSet64.Domain.admitted_bytes candidate positive bound 0x8000000000000000 0x8000000000000000,
      0x8000000000000000, AtomicLogical64.Domain.old_read candidate bound _ _,
      ⟨63, by decide⟩,
      by change Logical64.HasBit (0x8000000000000000 : Word) ⟨63, by decide⟩; unfold Logical64.HasBit; decide⟩

/-- The endpoint is the world of the same real covered execution. Its current
authority and resource frame are derived from steps, never an unrelated witness. -/
structure Returned (desired : Logical64.Operation) (descriptor : Frame) (seed : Shared) (initial : X86.State)
    (choices : Choices) (evolved : Shared) (result : Result) : Prop where
  covered : CoveredExecution descriptor choices seed initial evolved result
  current : Current descriptor evolved result.state
  preservation : Preservation seed evolved
  post : Post desired descriptor seed initial evolved result.state

theorem Returned.of_covered {desired candidate input shared initial choices evolved result}
    (pre : EDSL.AtomicSet64.Pre candidate input shared initial)
    (covered : CoveredExecution (frame candidate input shared initial) choices shared initial evolved result)
    (post : Post desired (frame candidate input shared initial) shared initial evolved result.state) :
    Returned desired (frame candidate input shared initial) shared initial choices evolved result :=
  ⟨covered, covered.current (Current.of_pre pre), covered.preserves (Current.of_pre pre), post⟩

/-- Fuel is obtained from the actual trace; it is neither task input nor an
admission bound. The callable result retains all real full64 atomic labels. -/
theorem SemanticClaim.run {desired candidate} (claim : SemanticClaim desired candidate)
    {input shared initial} (pre : EDSL.AtomicSet64.Pre candidate input shared initial)
    (choices : Choices) :
    ∃ evolved result, LockedSet64.run choices result.instructions initial = .ok result ∧
      Returned desired (frame candidate input shared initial) shared initial choices evolved result := by
  obtain ⟨evolved, result, covered, post⟩ := claim input shared initial pre choices
  exact ⟨evolved, result, LockedSet64.run_complete covered.machine (Nat.le_refl _),
    Returned.of_covered pre covered post⟩

/-- Fixed-choice determinism binds every real returning result, including all
labels/accesses/counts, to the resource-certified result. -/
theorem SemanticClaim.all_results {desired candidate} (claim : SemanticClaim desired candidate)
    {input shared initial choices result} (pre : EDSL.AtomicSet64.Pre candidate input shared initial)
    (actual : LockedSet64.Executes choices initial result) :
    ∃ evolved, Returned desired (frame candidate input shared initial) shared initial choices evolved result := by
  obtain ⟨evolved, expected, covered, post⟩ := claim input shared initial pre choices
  have same := LockedSet64.Executes.fixed_choices_unique covered.machine actual
  subst expected
  exact ⟨evolved, Returned.of_covered pre covered post⟩

theorem SemanticClaim.actual {desired candidate} (claim : SemanticClaim desired candidate)
    {input shared initial choices fuel result} (pre : EDSL.AtomicSet64.Pre candidate input shared initial)
    (actual : LockedSet64.run choices fuel initial = .ok result) :
    ∃ evolved, Returned desired (frame candidate input shared initial) shared initial choices evolved result :=
  claim.all_results pre (LockedSet64.run_sound actual)

theorem Claim.run {desired candidate} (claim : Claim desired candidate)
    {input shared initial} (pre : EDSL.AtomicSet64.Pre candidate input shared initial) (choices : Choices) :
    ∃ evolved result, LockedSet64.run choices result.instructions initial = .ok result ∧
      Returned desired (frame candidate input shared initial) shared initial choices evolved result := claim.1.run pre choices

theorem Claim.all_results {desired candidate} (claim : Claim desired candidate)
    {input shared initial choices result} (pre : EDSL.AtomicSet64.Pre candidate input shared initial)
    (actual : LockedSet64.Executes choices initial result) :
    ∃ evolved, Returned desired (frame candidate input shared initial) shared initial choices evolved result :=
  claim.1.all_results pre actual

theorem Claim.actual {desired candidate} (claim : Claim desired candidate)
    {input shared initial choices fuel result} (pre : EDSL.AtomicSet64.Pre candidate input shared initial)
    (actual : LockedSet64.run choices fuel initial = .ok result) :
    ∃ evolved, Returned desired (frame candidate input shared initial) shared initial choices evolved result :=
  claim.1.actual pre actual

/-- The true OS event sequence and its value chain are conclusions of the
registered execution. Cost/event accounting remains separate from Post. -/
theorem Returned.events {desired descriptor seed initial choices evolved result}
    (returned : Returned desired descriptor seed initial choices evolved result)
    (entryCurrent : Current descriptor seed initial) :
    ∃ cell events, OS.Atomics64.LogicalTrace descriptor.cell cell seed events evolved ∧
      events.map OS.Atomics64.Event.logical = result.events := returned.covered.logicalTrace entryCurrent

/-- Total certified execution excludes every real non-fuel machine fault,
including decoding faults. Unsupported bytes still have resource admission. -/
theorem SemanticClaim.no_fault_prefix {desired candidate} (claim : SemanticClaim desired candidate)
    {input shared initial choices fuel fault} (pre : EDSL.AtomicSet64.Pre candidate input shared initial)
    (actual : LockedSet64.run choices fuel initial = .error fault) : fault = .exhaustedFuel := by
  obtain ⟨_, _, covered, _⟩ := claim input shared initial pre choices
  exact covered.machine.no_fault_prefix actual

theorem Claim.no_fault_prefix {desired candidate} (claim : Claim desired candidate)
    {input shared initial choices fuel fault} (pre : EDSL.AtomicSet64.Pre candidate input shared initial)
    (actual : LockedSet64.run choices fuel initial = .error fault) : fault = .exhaustedFuel :=
  claim.1.no_fault_prefix pre actual

end EDSL.Grading.AtomicSet64
