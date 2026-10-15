/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Suspend.Frontier
import EDSL.OS.Suspend.Invariant

namespace EDSL.OS.Suspend
open X86

/-- Completing a valid pending call consumes its identity across every worker,
including every peer's retained invocation. -/
theorem resume_absent {state after : State} (valid : WellFormed state)
    {identifier invocation : Nat} {raw flags rcx r11 : Word}
    (success : resume state identifier invocation raw flags rcx r11 = .ok after) :
    InvocationAbsent after invocation ∧ invocation < after.nextCall := by
  obtain ⟨worker, saved, live, running, pending, sameId, owner, empty, shape⟩ :=
    resume_ok _ _ _ _ _ _ _ _ success
  have allocated := (valid.pending identifier saved pending).allocated
  refine ⟨?_, ?_⟩
  · intro query current found equal
    rw [shape] at found
    by_cases own : query = identifier
    · simp [own] at found
    · have prior : state.pending query = some current := by simpa only [own, ↓reduceIte] using found
      have same := valid.distinct query identifier current saved prior pending (equal.trans sameId.symm)
      exact own same
  · rw [resume_nextCall success]
    simpa only [sameId] using allocated

/-- No successful future schedule can revive a completed invocation. This
quantifies actual physical wrapper actions, including arbitrary peer activity. -/
theorem consumed_identity_never_resumes {state after : State} (valid : WellFormed state)
    {identifier invocation : Nat} {raw flags rcx r11 : Word}
    (completed : resume state identifier invocation raw flags rcx r11 = .ok after)
    {actions : List Action} {result : State × List Observation}
    (success : schedule after actions = .ok result) (query : Nat) (value choices savedRcx savedR11 : Word) :
    ¬ ∃ finalState, resume result.1 query invocation value choices savedRcx savedR11 = .ok finalState := by
  obtain ⟨absent, older⟩ := resume_absent valid completed
  have preserved := schedule_preserves_absent absent older success
  rintro ⟨finalState, resumed⟩
  obtain ⟨_, saved, _, _, pending, sameId, _, _, _⟩ := resume_ok _ _ _ _ _ _ _ _ resumed
  exact preserved query saved pending sameId

end EDSL.OS.Suspend
