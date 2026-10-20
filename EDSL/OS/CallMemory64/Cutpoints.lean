/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallMemory64.Coverage
import EDSL.X86.Sequential.Cutpoints

set_option warningAsError true

namespace EDSL.OS.CallMemory64.Cutpoints
open X86
open Sequential.Cutpoints (Layout)

/-! Cutpoint composition for the ordinary mixed DATA8/private-stack machine.
The descriptor, including its original caller-slot boundary, stays fixed across
all segments. The shared OS world and the completely coupled CPU RAM evolve
together. This profile supplies no syscall, atomic or concurrency rule.
Physical interpretation inherits CallReturn's ordinary RAM/four-level canonical
address profile with AC/CET disabled and no asynchronous interference; these
theorems establish execution in that model, without kernel refinement.

`Post` is an independent world/CPU predicate. A client can close it over its
initial state, input or other immutable context. Neither it nor the invariants
need to mention an evaluator, a future execution or a future resource history.
-/

/-- Local progress for every AF choice. Current ownership, permissions and
complete RAM coupling are explicit premises, and each successor obligation uses
the world produced by this actual instruction. Static depth decreases inside a
segment; dynamic rank decreases on entry to its next cutpoint. -/
structure Certificate {Location : Type u} (flow : Layout Location)
    (descriptor : Descriptor) (Post : Shared → State → Prop) where
  Inv : Location → Shared → State → Prop
  rank : Location → Shared → State → Nat
  Interior : Location → Nat → Location → Shared → State → Prop
  start : ∀ cut shared state, flow.cutpoint cut = true → Inv cut shared state →
    Interior cut (rank cut shared state) cut shared state
  localVC : ∀ source budget node shared before,
    Interior source budget node shared before → Current descriptor shared before → ∀ af,
    ∃ evolved after observation,
      CPU.Step descriptor shared evolved before after af observation ∧
      EDSL.CallStack.FetchWithin descriptor.frame before ∧
      match observation.result with
      | .returned final => Post evolved final
      | .next middle => ∃ dest, flow.Edge node dest ∧
          ((flow.cutpoint dest = true ∧ Inv dest evolved middle ∧
              rank dest evolved middle < budget) ∨
           (flow.cutpoint dest = false ∧ Interior source budget dest evolved middle))
      | .atomic _ _ | .syscall _ => False

variable {Location : Type u} {flow : Layout Location} {descriptor : Descriptor}
  {Post : Shared → State → Prop}

/-- A nonempty actual segment returns through the original caller slot or
reaches its next cutpoint. Both alternatives retain the evolved OS world and
complete instruction fetch footprints. -/
def Segment (cert : Certificate flow descriptor Post) (_source : Location) (budget : Nat)
    (node : Location) (choices : CallReturn.Choices) (shared : Shared) (initial : State) : Prop :=
  (∃ evolved result, CoveredExecution descriptor choices shared initial evolved result ∧
      Post evolved result.state ∧ result.instructions ≤ flow.depth node + 1) ∨
  (∃ dest evolved middle count reads,
      CoveredHistory descriptor choices shared initial evolved middle count reads ∧
      0 < count ∧ count ≤ flow.depth node + 1 ∧ flow.cutpoint dest = true ∧
      cert.Inv dest evolved middle ∧ cert.rank dest evolved middle < budget)

/-- Static-depth induction composes only actual local instructions. In
particular, a private RET that resumes the caller remains a continuing step;
only RET at the descriptor's frozen original slot can finish the segment. -/
theorem Certificate.segment (cert : Certificate flow descriptor Post)
    {source : Location} {budget : Nat} {node : Location} {shared : Shared} {initial : State}
    (valid : cert.Interior source budget node shared initial)
    (current : Current descriptor shared initial) (choices : CallReturn.Choices) :
    Segment cert source budget node choices shared initial := by
  have compose : ∀ depth, ∀ node, flow.depth node = depth → ∀ shared initial,
      cert.Interior source budget node shared initial → Current descriptor shared initial →
      ∀ choices, Segment cert source budget node choices shared initial := by
    intro depth
    induction depth using Nat.strongRecOn with
    | ind depth induction =>
      intro node value shared initial valid current choices
      obtain ⟨evolved, after, ⟨outcome, reads⟩, step, fetch, next⟩ :=
        cert.localVC source budget node shared initial valid current (choices 0)
      have endpoint := step.cpu
      cases outcome with
      | returned final =>
        have same : final = after := Option.some.inj endpoint
        subst after
        exact .inl ⟨evolved, ⟨final, 1, reads⟩, .ret step fetch, next, by simp⟩
      | atomic event middle => exact False.elim next
      | syscall request => exact False.elim next
      | next middle =>
        have same : middle = after := Option.some.inj endpoint
        subst after
        obtain ⟨dest, edge, cut | interior⟩ := next
        · obtain ⟨isCut, invariant, decreased⟩ := cut
          exact .inr ⟨dest, evolved, middle, 1, reads,
            by simpa using CoveredHistory.next step fetch CoveredHistory.nil,
            by omega, by omega, isCut, invariant, decreased⟩
        · obtain ⟨notCut, nextValid⟩ := interior
          have smaller := flow.depth_decrease edge notCut
          have tail := induction (flow.depth dest) (by omega) dest rfl evolved middle
            nextValid (step.current current) (choices.drop 1)
          rcases tail with ⟨final, result, execution, post, bound⟩ |
            ⟨last, final, state, count, rest, history, positive, bound, isCut, invariant, decreased⟩
          · exact .inl ⟨final, result.prepend 1 reads, .next step fetch execution, post,
              by simp only [Sequential.Result.prepend]; omega⟩
          · exact .inr ⟨last, final, state, count + 1, reads ++ rest,
              .next step fetch history, by omega, by omega, isCut, invariant, decreased⟩
  exact compose (flow.depth node) node rfl shared initial valid current choices

/-- Affine instruction bound: the first segment uses its own static depth;
each unit of dynamic rank permits at most one further maximum-depth segment.
This bounds model instructions, not elapsed time or hardware micro-operations. -/
def Certificate.instructionBound (cert : Certificate flow descriptor Post)
    (entry : Location) (shared : Shared) (initial : State) : Nat :=
  flow.depth entry + 1 + (flow.maxDepth + 1) * cert.rank entry shared initial

/-- Dynamic-rank induction joins finite covered segments. The remaining AF
stream drops by each segment's actual instruction count, and every join uses
the actual evolved world with the same descriptor and original return slot. -/
theorem Certificate.execution (cert : Certificate flow descriptor Post)
    {entry : Location} {shared : Shared} {initial : State}
    (isCut : flow.cutpoint entry = true) (valid : cert.Inv entry shared initial)
    (current : Current descriptor shared initial) (choices : CallReturn.Choices) :
    ∃ evolved result, CoveredExecution descriptor choices shared initial evolved result ∧
      Post evolved result.state ∧
      result.instructions ≤ cert.instructionBound entry shared initial := by
  have compose : ∀ budget, ∀ entry shared initial, cert.rank entry shared initial = budget →
      flow.cutpoint entry = true → cert.Inv entry shared initial →
      Current descriptor shared initial → ∀ choices,
      ∃ evolved result, CoveredExecution descriptor choices shared initial evolved result ∧
        Post evolved result.state ∧
        result.instructions ≤ flow.depth entry + 1 + (flow.maxDepth + 1) * budget := by
    intro budget
    induction budget using Nat.strongRecOn with
    | ind budget induction =>
      intro entry shared initial value isCut valid current choices
      rcases cert.segment (cert.start entry shared initial isCut valid) current choices with
        ⟨evolved, result, execution, post, bound⟩ |
        ⟨dest, evolved, middle, count, reads, history, _, bound, destCut, invariant, decreased⟩
      · exact ⟨evolved, result, execution, post, by omega⟩
      · obtain ⟨final, result, execution, post, cost⟩ :=
          induction (cert.rank dest evolved middle) (by omega) dest evolved middle rfl
            destCut invariant (history.current current) (choices.drop count)
        refine ⟨final, result.prepend count reads, history.then_execution execution, post, ?_⟩
        have staticBound := flow.depth_bound dest
        have rankBound : cert.rank dest evolved middle + 1 ≤ budget := by omega
        have multiply := Nat.mul_le_mul_left (flow.maxDepth + 1) rankBound
        simp only [Nat.mul_add, Nat.mul_one] at multiply
        simp only [Sequential.Result.prepend]
        omega
  exact compose (cert.rank entry shared initial) entry shared initial rfl isCut valid current choices

/-- The sharper affine bound also implies the usual uniform segment bound. -/
theorem Certificate.instructionBound_le (cert : Certificate flow descriptor Post)
    (entry : Location) (shared : Shared) (initial : State) :
    cert.instructionBound entry shared initial ≤
      (flow.maxDepth + 1) * (cert.rank entry shared initial + 1) := by
  have staticBound := flow.depth_bound entry
  simp only [instructionBound, Nat.mul_add, Nat.mul_one]
  omega

/-- Evaluator totality for every AF stream at the proved bound. The returned
covered witness also supplies `.current current`, `.mixedHistory`, `.preserves`,
`.memory_frame current`, and `.prefix_current current` from existing machinery.
The evaluator always retains `descriptor.frame.top`, even after private CALLs. -/
theorem Certificate.total (cert : Certificate flow descriptor Post)
    {entry : Location} {shared : Shared} {initial : State}
    (isCut : flow.cutpoint entry = true) (valid : cert.Inv entry shared initial)
    (current : Current descriptor shared initial) (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.runFrom descriptor.frame.top choices
        (cert.instructionBound entry shared initial) initial = .ok result ∧
      CoveredExecution descriptor choices shared initial evolved result ∧
      Post evolved result.state ∧
      result.instructions ≤ cert.instructionBound entry shared initial := by
  obtain ⟨evolved, result, execution, post, bound⟩ := cert.execution isCut valid current choices
  exact ⟨evolved, result, execution.run bound, execution, post, bound⟩

/-- Any successful evaluator result with the same frozen boundary and AF
stream has the certified contract and resource evidence, regardless of fuel.
Determinism is used only to identify it with the constructed execution. -/
theorem Certificate.actual (cert : Certificate flow descriptor Post)
    {entry : Location} {shared : Shared} {initial : State}
    (isCut : flow.cutpoint entry = true) (valid : cert.Inv entry shared initial)
    (current : Current descriptor shared initial) {choices : CallReturn.Choices}
    {fuel : Nat} {result : CallReturn.Result}
    (actual : CallReturn.runFrom descriptor.frame.top choices fuel initial = .ok result) :
    ∃ evolved, CoveredExecution descriptor choices shared initial evolved result ∧
      Post evolved result.state ∧
      result.instructions ≤ cert.instructionBound entry shared initial := by
  obtain ⟨evolved, expected, execution, post, bound⟩ := cert.execution isCut valid current choices
  have same := CallReturn.ExecutesFrom.fixed_choices_unique execution.machine
    (CallReturn.runFrom_sound actual)
  subst expected
  exact ⟨evolved, execution, post, bound⟩

/-- Resume a certificate after an independently checked prefix. This rule
threads the prefix's evolved world and drops the full choice stream by its
actual count. The mutable footprint remains the union of DATA and private
stack, by the resulting covered execution's memory-frame theorem. -/
theorem Certificate.after_history (cert : Certificate flow descriptor Post)
    {entry : Location} {shared evolved : Shared} {initial middle : State}
    {choices : CallReturn.Choices} {count : Nat} {reads : List CallReturn.Read}
    (history : CoveredHistory descriptor choices shared initial evolved middle count reads)
    (isCut : flow.cutpoint entry = true) (valid : cert.Inv entry evolved middle)
    (current : Current descriptor shared initial) :
    ∃ final result, CoveredExecution descriptor choices shared initial final result ∧
      Post final result.state ∧
      result.instructions ≤ count + cert.instructionBound entry evolved middle := by
  obtain ⟨final, result, execution, post, bound⟩ :=
    cert.execution isCut valid (history.current current) (choices.drop count)
  exact ⟨final, result.prepend count reads, history.then_execution execution, post,
    by simp only [Sequential.Result.prepend]; omega⟩

end EDSL.OS.CallMemory64.Cutpoints
