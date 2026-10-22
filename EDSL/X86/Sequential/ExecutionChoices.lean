/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Execution
import EDSL.X86.Sequential.MachineChoices
import EDSL.X86.Sequential.ChoiceRefinement

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.Sequential

/-- Full-status-vector execution of the current production instruction profile.
This interface adds independent choice components, not additional opcodes. -/
abbrev runWith := Engine.run stepWith
abbrev ExecutesWith := Engine.Executes stepWith
abbrev BlockWith := Engine.Block stepWith
abbrev AllExecutionsWith := Engine.AllExecutions stepWith

/-- The vector adapter and Bool machine have exactly the same possible complete
single-step outcomes in the current opcode profile. -/
theorem stepWith_simulates_step : Engine.Simulates stepWith step := by
  intro choices state
  obtain ⟨value, same⟩ := stepWith_exists_bool state choices
  exact ⟨value, same.symm⟩

theorem step_simulates_stepWith : Engine.Simulates step stepWith := by
  intro value state
  exact step_existsWith state value

/-- Equality of finite returning behaviors includes final flags, memory,
permissions, costs and operand reads, not only a returned register. -/
theorem nondet_executesWith_iff (initial : State) (result : Result) :
    (∃ choices, ExecutesWith choices initial result) ↔ NondetExecutes initial result :=
  Engine.Simulates.nondet_executes_iff stepWith_simulates_step step_simulates_stepWith initial result

/-- Full equality of possible bounded outcomes, including faults and exhaustion. -/
theorem runWith_outcome_iff (fuel : Nat) (initial : State) (outcome : Except Error Result) :
    (∃ choices, runWith choices fuel initial = outcome) ↔
      ∃ choices, run choices fuel initial = outcome :=
  Engine.Simulates.run_outcome_iff stepWith_simulates_step step_simulates_stepWith fuel initial outcome

/-- An existing uniformly bounded Bool proof covers every vector stream in the
current profile. The bound is a premise: finite simulation alone is not an
unbounded termination theorem. -/
theorem allExecutionsWith_of_bounded {initial : State} {Post : Result → Prop} {fuel : Nat}
    (correct : ∀ choices, ∃ result, run choices fuel initial = .ok result ∧ Post result) :
    AllExecutionsWith initial (fun result => Post result ∧ result.instructions ≤ fuel) := by
  intro choices
  obtain ⟨oldChoices, same⟩ := stepWith_simulates_step.run fuel choices initial
  obtain ⟨result, success, post⟩ := correct oldChoices
  have actual : runWith choices fuel initial = .ok result := same.symm.trans success
  exact ⟨result, Engine.run_sound stepWith actual, post, Engine.run_instructions_le stepWith actual⟩

/-- Uniformly bounded existing total-correctness certificates can be reused
without proving a separate vector execution for each program. -/
theorem allExecutionsWith_of_allExecutions {initial : State} {Post : Result → Prop} {fuel : Nat}
    (correct : AllExecutions initial (fun result => Post result ∧ result.instructions ≤ fuel)) :
    AllExecutionsWith initial (fun result => Post result ∧ result.instructions ≤ fuel) := by
  apply allExecutionsWith_of_bounded
  intro choices
  obtain ⟨result, execution, post, bound⟩ := correct choices
  exact ⟨result, run_complete execution bound, post⟩

end EDSL.X86.Sequential
