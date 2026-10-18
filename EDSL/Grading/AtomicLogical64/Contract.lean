/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicLogical64.Execution

namespace EDSL.Grading.AtomicLogical64
open X86 OS.AddressSpace

/-- A request is useful when a requested natural-number bit is absent from
the actual initial target read. Zero/already-set masks remain admitted by Pre. -/
def Useful (initial : X86.State) : Prop :=
  ∃ old, loadQWord initial.memory (initial.registers .rdi) = .ok old ∧
    ∃ index : Fin 64, ¬Logical64.HasBit old index ∧ Logical64.HasBit (initial.registers .rsi) index

/-- Closed resource-first callable union task for arbitrary literal bytes.
Admission is exactly the existing present-resource Pre, without decoder, opcode,
length, instruction count, event count or future-execution requirements.
Every AF stream must return through actual covered CPU/OS transitions. -/
def SemanticClaim (candidate : List Byte) : Prop :=
  ∀ input shared initial, EDSL.AtomicLogical64.Pre candidate input shared initial →
    ∀ choices, ∃ evolved result,
      CoveredExecution (frame candidate input shared initial) choices shared initial evolved result ∧
      Post (frame candidate input shared initial) shared initial evolved result.state

def Nonvacuous (candidate : List Byte) : Prop :=
  ∃ input shared initial, EDSL.AtomicLogical64.Pre candidate input shared initial ∧ Useful initial

def Claim (candidate : List Byte) : Prop := SemanticClaim candidate ∧ Nonvacuous candidate

/-- The endpoint is the world of the same real covered execution. Its current
authority and resource frame are derived from steps, never an unrelated witness. -/
structure Returned (descriptor : Frame) (seed : Shared) (initial : X86.State)
    (choices : Choices) (evolved : Shared) (result : Result) : Prop where
  covered : CoveredExecution descriptor choices seed initial evolved result
  current : Current descriptor evolved result.state
  preservation : Preservation seed evolved
  post : Post descriptor seed initial evolved result.state

theorem Returned.of_covered {candidate input shared initial choices evolved result}
    (pre : EDSL.AtomicLogical64.Pre candidate input shared initial)
    (covered : CoveredExecution (frame candidate input shared initial) choices shared initial evolved result)
    (post : Post (frame candidate input shared initial) shared initial evolved result.state) :
    Returned (frame candidate input shared initial) shared initial choices evolved result :=
  ⟨covered, covered.current (Current.of_pre pre), covered.preserves (Current.of_pre pre), post⟩

/-- Fuel is obtained from the actual trace; it is neither task input nor an
admission bound. The callable result retains all real full64 atomic labels. -/
theorem SemanticClaim.run {candidate} (claim : SemanticClaim candidate)
    {input shared initial} (pre : EDSL.AtomicLogical64.Pre candidate input shared initial)
    (choices : Choices) :
    ∃ evolved result, LockedLogical64.run choices result.instructions initial = .ok result ∧
      Returned (frame candidate input shared initial) shared initial choices evolved result := by
  obtain ⟨evolved, result, covered, post⟩ := claim input shared initial pre choices
  exact ⟨evolved, result, LockedLogical64.run_complete covered.machine (Nat.le_refl _),
    Returned.of_covered pre covered post⟩

/-- Fixed-choice determinism binds every real returning result, including all
labels/accesses/counts, to the resource-certified result. -/
theorem SemanticClaim.all_results {candidate} (claim : SemanticClaim candidate)
    {input shared initial choices result} (pre : EDSL.AtomicLogical64.Pre candidate input shared initial)
    (actual : LockedLogical64.Executes choices initial result) :
    ∃ evolved, Returned (frame candidate input shared initial) shared initial choices evolved result := by
  obtain ⟨evolved, expected, covered, post⟩ := claim input shared initial pre choices
  have same := LockedLogical64.Executes.fixed_choices_unique covered.machine actual
  subst expected
  exact ⟨evolved, Returned.of_covered pre covered post⟩

theorem SemanticClaim.actual {candidate} (claim : SemanticClaim candidate)
    {input shared initial choices fuel result} (pre : EDSL.AtomicLogical64.Pre candidate input shared initial)
    (actual : LockedLogical64.run choices fuel initial = .ok result) :
    ∃ evolved, Returned (frame candidate input shared initial) shared initial choices evolved result :=
  claim.all_results pre (LockedLogical64.run_sound actual)

theorem Claim.run {candidate} (claim : Claim candidate)
    {input shared initial} (pre : EDSL.AtomicLogical64.Pre candidate input shared initial) (choices : Choices) :
    ∃ evolved result, LockedLogical64.run choices result.instructions initial = .ok result ∧
      Returned (frame candidate input shared initial) shared initial choices evolved result := claim.1.run pre choices

theorem Claim.all_results {candidate} (claim : Claim candidate)
    {input shared initial choices result} (pre : EDSL.AtomicLogical64.Pre candidate input shared initial)
    (actual : LockedLogical64.Executes choices initial result) :
    ∃ evolved, Returned (frame candidate input shared initial) shared initial choices evolved result :=
  claim.1.all_results pre actual

theorem Claim.actual {candidate} (claim : Claim candidate)
    {input shared initial choices fuel result} (pre : EDSL.AtomicLogical64.Pre candidate input shared initial)
    (actual : LockedLogical64.run choices fuel initial = .ok result) :
    ∃ evolved, Returned (frame candidate input shared initial) shared initial choices evolved result :=
  claim.1.actual pre actual

/-- The true OS event sequence and its value chain are conclusions of the
registered execution. Cost/event accounting remains separate from Post. -/
theorem Returned.events {descriptor seed initial choices evolved result}
    (returned : Returned descriptor seed initial choices evolved result)
    (entryCurrent : Current descriptor seed initial) :
    ∃ cell events, OS.Atomics64.OrTrace descriptor.cell cell seed events evolved ∧
      events.map OS.Atomics64.Event.logical = result.events := returned.covered.orTrace entryCurrent

/-- Total certified execution excludes every real non-fuel machine fault,
including decoding faults. Unsupported bytes still have resource admission. -/
theorem SemanticClaim.no_fault_prefix {candidate} (claim : SemanticClaim candidate)
    {input shared initial choices fuel fault} (pre : EDSL.AtomicLogical64.Pre candidate input shared initial)
    (actual : LockedLogical64.run choices fuel initial = .error fault) : fault = .exhaustedFuel := by
  obtain ⟨_, _, covered, _⟩ := claim input shared initial pre choices
  exact covered.machine.no_fault_prefix actual

theorem Claim.no_fault_prefix {candidate} (claim : Claim candidate)
    {input shared initial choices fuel fault} (pre : EDSL.AtomicLogical64.Pre candidate input shared initial)
    (actual : LockedLogical64.run choices fuel initial = .error fault) : fault = .exhaustedFuel :=
  claim.1.no_fault_prefix pre actual

end EDSL.Grading.AtomicLogical64
