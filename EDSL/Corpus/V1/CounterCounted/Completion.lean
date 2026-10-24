/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterCounted.Post
import EDSL.Corpus.V1.CounterCounted.Progress

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Compose proved prefix safety with ranked completion and the independent full
output contract. The bound is selected before future AF choices and offsets.
The chosen suffix starts at the exact original prefix's cut ghosts; choices
advance by each thread's own original issue count. No constraint is imposed on
past choices. These upper bounds on modeled issues imply neither fairness nor
minimum operations, wall-clock termination or physical machine refinement.
-/

namespace EDSL.Corpus.V1.CounterCounted
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation
open Grading.ConcurrentTask.Counted64 (SafePrefix Post)

variable {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
  {cell : Atomics64.Cell} {before cut : TSO64.State}
  {requests : Spec.Requests before} {prior : List Action}
  {observations : List Observation}

/-- Safety is an independently proved candidate obligation, used here to
package the constructed completed execution. It is not part of entry Pre. -/
theorem completion_of_safety
    (pre : Spec.Pre (image compiler) target cell before requests)
    (safety : ∀ actions actual, schedule before actions .ownedOnly .arithmetic = .ok actual →
      SafePrefix (image compiler) target cell before requests actual)
    (actual : schedule before prior .ownedOnly .arithmetic = .ok (cut, observations)) :
    ∃ bound : Nat, ∀ (choices : Nat → Nat → Bool) (offset : Nat → Nat),
    ∃ suffix finished,
      Mixed.ChoiceTrace.ChosenFrom choices
        (fun tid => offset tid + Mixed.ChoiceTrace.issues tid prior) suffix ∧
      schedule cut suffix .ownedOnly .arithmetic = .ok finished ∧
      Finished finished.1 ∧ suffix.length ≤ bound ∧
      schedule before (prior ++ suffix) .ownedOnly .arithmetic =
        .ok (finished.1, observations ++ finished.2) ∧
      (Mixed.ChoiceTrace.ChosenFrom choices offset prior →
        Mixed.ChoiceTrace.ChosenFrom choices offset (prior ++ suffix)) ∧
      Nonempty (Post (image compiler) target cell before requests (prior ++ suffix)
        (finished.1, observations ++ finished.2)) := by
  refine ⟨(cohort pre).potential (ghosts pre), ?_⟩
  intro choices offset
  obtain ⟨atCut, _cutCurrent, lifted, suffix, whole, _wholeLifted⟩ :=
    completion_after_prefix pre actual choices offset
  have potentialBound : (cohort pre).potential atCut ≤ (cohort pre).potential (ghosts pre) := by
    apply Mixed.RankedPotential.indexedSum_le
    intro slot
    have budget := (cohort pre).own_issue_budget_of_schedule rfl (current pre)
      pre.empty actual lifted slot
    exact Nat.le_trans (Nat.le_add_left _ _) budget
  have post := post_of_safe pre whole (safety _ _ whole) suffix.returned
  refine ⟨suffix.actions, (suffix.final, suffix.observations), suffix.chosen,
    suffix.actual, ⟨suffix.returned, suffix.quiescent⟩,
    Nat.le_trans suffix.issue_upper_bound potentialBound, whole, ?_, post⟩
  intro chosen
  exact Mixed.ChoiceTrace.chosen_append chosen suffix.chosen

#print axioms completion_of_safety

end EDSL.Corpus.V1.CounterCounted

#audit_edsl
