/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Execution
import EDSL.X86.Sequential.MachineChoices
import EDSL.X86.Sequential.ChoiceRefinementOn

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.Sequential

/-- The complete vector ISA, including independently undefined IMUL flags. -/
abbrev runWith := Engine.run stepWith
abbrev ExecutesWith := Engine.Executes stepWith
abbrev BlockWith := Engine.Block stepWith
abbrev AllExecutionsWith := Engine.AllExecutions stepWith

/-- Bool prefix safety excludes reaching an instruction rejected by that
profile. This is derived from actual old execution, not assumed byte metadata. -/
theorem boolChoiceProfile_of_safe_reachable {initial before : State}
    (safe : Safe initial) (reachable : Reachable initial before) : BoolChoiceProfile before := by
  obtain ⟨observation, actual, _⟩ := safe before reachable false
  exact boolChoiceProfile_of_step_success actual

/-- At old-safe reachable states, every complete vector outcome has an equal
Bool outcome. There is no global Bool simulation for the extended ISA. -/
theorem stepWith_simulates_step_on_safe {initial : State} (safe : Safe initial) :
    Engine.SimulatesOn (Reachable initial) stepWith step := by
  intro choices before reachable
  obtain ⟨value, same⟩ :=
    stepWith_exists_bool before choices (boolChoiceProfile_of_safe_reachable safe reachable)
  exact ⟨value, same.symm⟩

theorem step_simulates_stepWith_on_safe {initial : State} (safe : Safe initial) :
    Engine.SimulatesOn (Reachable initial) step stepWith := by
  intro value before reachable
  exact step_existsWith before value (boolChoiceProfile_of_safe_reachable safe reachable)

/-- The same old-reachability invariant is retained by a matching vector
continuation. All state components, reads and atomic events are equal. -/
theorem boolReachable_continuesWith {initial : State} (safe : Safe initial) :
    Engine.ContinuesClosed (Reachable initial) stepWith := by
  intro choices before observation reachable actual middle continued
  obtain ⟨value, same⟩ :=
    stepWith_exists_bool before choices (boolChoiceProfile_of_safe_reachable safe reachable)
  exact Engine.Reachable.continues step reachable (same.symm.trans actual) continued

/-- The possible bounded outcomes agree on an old-safe program. A program
using IMUL can have vector outcomes without any Bool outcome, so the prefix
safety premise is essential. Errors retain the evaluator's Error-only payload. -/
theorem runWith_outcome_iff (fuel : Nat) (initial : State) (outcome : Except Error Result)
    (safe : Safe initial) :
    (∃ choices, runWith choices fuel initial = outcome) ↔
      ∃ choices, run choices fuel initial = outcome := by
  constructor
  · rintro ⟨choices, actual⟩
    obtain ⟨oldChoices, same⟩ :=
      (stepWith_simulates_step_on_safe safe).run (Engine.Reachable.continuesClosed step initial)
        fuel choices initial (Engine.Reachable.refl step false initial)
    exact ⟨oldChoices, same.trans actual⟩
  · rintro ⟨oldChoices, actual⟩
    obtain ⟨choices, same⟩ :=
      (step_simulates_stepWith_on_safe safe).run (boolReachable_continuesWith safe)
        fuel oldChoices initial (Engine.Reachable.refl step false initial)
    exact ⟨choices, same.trans actual⟩

/-- Equality of complete returning behavior under the same explicit old-prefix
safety premise; final flags, memory/permissions, cost and reads are retained. -/
theorem nondet_executesWith_iff (initial : State) (result : Result) (safe : Safe initial) :
    (∃ choices, ExecutesWith choices initial result) ↔ NondetExecutes initial result := by
  constructor
  · rintro ⟨choices, execution⟩
    have returned : ∃ choices, runWith choices result.instructions initial = .ok result :=
      ⟨choices, Engine.run_complete stepWith execution (Nat.le_refl _)⟩
    obtain ⟨oldChoices, actual⟩ := (runWith_outcome_iff _ _ _ safe).mp returned
    exact ⟨oldChoices, run_sound actual⟩
  · rintro ⟨oldChoices, execution⟩
    have returned : ∃ choices, run choices result.instructions initial = .ok result :=
      ⟨oldChoices, run_complete execution (Nat.le_refl _)⟩
    obtain ⟨choices, actual⟩ := (runWith_outcome_iff _ _ _ safe).mpr returned
    exact ⟨choices, Engine.run_sound stepWith actual⟩

/-- Existing uniformly bounded Bool proofs cover every vector stream. Old
universal totality supplies the prefix safety needed for restricted simulation;
no separate assumption about a proposed instruction list is added. -/
theorem allExecutionsWith_of_bounded {initial : State} {Post : Result → Prop} {fuel : Nat}
    (correct : ∀ choices, ∃ result, run choices fuel initial = .ok result ∧ Post result) :
    AllExecutionsWith initial (fun result => Post result ∧ result.instructions ≤ fuel) := by
  have total : AllExecutions initial Post := by
    intro choices
    obtain ⟨result, actual, post⟩ := correct choices
    exact ⟨result, run_sound actual, post⟩
  have safe := total.safe
  intro choices
  obtain ⟨oldChoices, same⟩ :=
    (stepWith_simulates_step_on_safe safe).run (Engine.Reachable.continuesClosed step initial)
      fuel choices initial (Engine.Reachable.refl step false initial)
  obtain ⟨result, success, post⟩ := correct oldChoices
  have actual : runWith choices fuel initial = .ok result := same.symm.trans success
  exact ⟨result, Engine.run_sound stepWith actual, post, Engine.run_instructions_le stepWith actual⟩

/-- Reuse a bounded existing certificate through the common engine. New
IMUL certificates are instead proved directly with the complete vector VCG. -/
theorem allExecutionsWith_of_allExecutions {initial : State} {Post : Result → Prop} {fuel : Nat}
    (correct : AllExecutions initial (fun result => Post result ∧ result.instructions ≤ fuel)) :
    AllExecutionsWith initial (fun result => Post result ∧ result.instructions ≤ fuel) := by
  apply allExecutionsWith_of_bounded
  intro choices
  obtain ⟨result, execution, post, bound⟩ := correct choices
  exact ⟨result, run_complete execution bound, post⟩

end EDSL.X86.Sequential
