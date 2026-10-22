/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ExecutionTotal

namespace EDSL.X86.Sequential.Engine

variable {Choice : Type} (transition : Choice → State → Except Error Observation)

theorem run_choices_congr {left right : ChoiceStream Choice} {fuel : Nat} {initial : State}
    (agree : left.Agree right fuel) : run transition left fuel initial = run transition right fuel initial := by
  induction fuel generalizing left right initial with
  | zero => rfl
  | succ fuel induction =>
    have head := agree 0 (by omega)
    cases step : transition (right 0) initial with
    | error fault => simp [run, head, step]
    | ok observation =>
      rcases observation with ⟨outcome, reads⟩
      cases outcome with
      | returned final => simp [run, head, step]
      | syscall request => simp [run, head, step]
      | next middle | atomic event middle =>
        simp only [run, head, step, ok_bind]
        rw [induction agree.drop]

/-- Each accumulated read belongs to an actual observation at a continuing
prefix. This records the pre-instruction state and its exact stream index. -/
theorem Executes.read_origin {choices : ChoiceStream Choice} {initial : State} {result : Result}
    (execution : Executes transition choices initial result) {read : Read}
    (member : read ∈ result.reads) :
    ∃ count before priorReads observation, count < result.instructions ∧
      Block transition choices initial before count priorReads ∧
        transition (choices count) before = .ok observation ∧ read ∈ observation.reads := by
  induction execution with
  | @ret choices initial final reads step =>
    exact ⟨0, initial, [], ⟨.returned final, reads⟩, by simp, .nil, step, member⟩
  | @next choices initial middle result reads step tail induction =>
    rcases List.mem_append.mp member with first | later
    · exact ⟨0, initial, [], ⟨.next middle, reads⟩, by simp only [Result.prepend]; omega, .nil, step, first⟩
    · obtain ⟨count, before, priorReads, observation, bound, block, actual, present⟩ := induction later
      refine ⟨count + 1, before, reads ++ priorReads, observation, by simp only [Result.prepend]; omega,
        .next step block, ?_, present⟩
      simpa [ChoiceStream.drop, Nat.add_comm] using actual
  | @atomic choices initial middle result reads event step tail induction =>
    rcases List.mem_append.mp member with first | later
    · exact ⟨0, initial, [], ⟨.atomic event middle, reads⟩, by simp only [Result.prepend]; omega,
        .nil, step, first⟩
    · obtain ⟨count, before, priorReads, observation, bound, block, actual, present⟩ := induction later
      refine ⟨count + 1, before, reads ++ priorReads, observation, by simp only [Result.prepend]; omega,
        .atomic step block, ?_, present⟩
      simpa [ChoiceStream.drop, Nat.add_comm] using actual

theorem Block.read_origin {choices : ChoiceStream Choice} {initial final : State} {count : Nat} {reads : List Read}
    (execution : Block transition choices initial final count reads) {read : Read}
    (member : read ∈ reads) :
    ∃ index before priorReads observation, index < count ∧
      Block transition choices initial before index priorReads ∧
        transition (choices index) before = .ok observation ∧ read ∈ observation.reads := by
  induction execution with
  | nil => cases member
  | @next choices initial middle final count reads rest step tail induction =>
    rcases List.mem_append.mp member with first | later
    · exact ⟨0, initial, [], ⟨.next middle, reads⟩, by omega, .nil, step, first⟩
    · obtain ⟨index, before, priorReads, observation, bound, block, actual, present⟩ := induction later
      refine ⟨index + 1, before, reads ++ priorReads, observation, by omega, .next step block, ?_, present⟩
      simpa [ChoiceStream.drop, Nat.add_comm] using actual
  | @atomic choices initial middle final count reads rest event step tail induction =>
    rcases List.mem_append.mp member with first | later
    · exact ⟨0, initial, [], ⟨.atomic event middle, reads⟩, by omega, .nil, step, first⟩
    · obtain ⟨index, before, priorReads, observation, bound, block, actual, present⟩ := induction later
      refine ⟨index + 1, before, reads ++ priorReads, observation, by omega, .atomic step block, ?_, present⟩
      simpa [ChoiceStream.drop, Nat.add_comm] using actual

theorem Block.run_error_append {choices : ChoiceStream Choice} {initial middle : State} {count fuel : Nat}
    {reads : List Read} {error : Error}
    (block : Block transition choices initial middle count reads)
    (tail : run transition (choices.drop count) fuel middle = .error error) :
    run transition choices (count + fuel) initial = .error error := by
  induction block with
  | nil => simpa using tail
  | @next choices initial next middle count reads rest step block induction =>
    have finish := induction (by simpa [Nat.add_comm] using tail)
    rw [show count + 1 + fuel = (count + fuel) + 1 by omega, run_next transition step, finish]
    rfl
  | @atomic choices initial next middle count reads rest event step block induction =>
    have finish := induction (by simpa [Nat.add_comm] using tail)
    rw [show count + 1 + fuel = (count + fuel) + 1 by omega, run_atomic transition step, finish]
    rfl

/-- A transition error, or a syscall boundary rejected by this evaluator. The
evaluator's zero-fuel case is separate because it takes no machine step. -/
def FaultAt (af : Choice) (initial : State) (error : Error) : Prop :=
  transition af initial = .error error ∨
    error = .syscallBoundary ∧ ∃ request reads, transition af initial = .ok ⟨.syscall request, reads⟩

def FaultTrace (choices : ChoiceStream Choice) (initial : State) (error : Error)
    (count : Nat) (reads : List Read) : Prop :=
  ∃ before, Block transition choices initial before count reads ∧ FaultAt transition (choices count) before error

theorem FaultTrace.run {choices : ChoiceStream Choice} {initial : State} {error : Error} {count fuel : Nat}
    {reads : List Read} (trace : FaultTrace transition choices initial error count reads)
    (enough : count < fuel) : run transition choices fuel initial = .error error := by
  obtain ⟨before, block, fault⟩ := trace
  have remaining : ∃ rest, fuel = count + (rest + 1) := ⟨fuel - count - 1, by omega⟩
  obtain ⟨rest, rfl⟩ := remaining
  apply block.run_error_append transition
  rcases fault with error | ⟨rfl, request, reads, syscall⟩
  · exact run_fault transition (by simpa [ChoiceStream.drop] using error)
  · exact run_syscall transition (by simpa [ChoiceStream.drop] using syscall)

theorem run_error_sound {choices : ChoiceStream Choice} {fuel : Nat} {initial : State} {error : Error}
    (fault : run transition choices fuel initial = .error error) :
    error = .exhaustedFuel ∨ ∃ count reads, count < fuel ∧ FaultTrace transition choices initial error count reads := by
  induction fuel generalizing choices initial with
  | zero =>
    exact .inl ((Except.error.inj fault).symm)
  | succ fuel induction =>
    cases step : transition (choices 0) initial with
    | error machineError =>
      have same : machineError = error := Except.error.inj ((run_fault transition step).symm.trans fault)
      subst machineError
      exact .inr ⟨0, [], by omega, initial, .nil, .inl step⟩
    | ok observation =>
      rcases observation with ⟨outcome, reads⟩
      cases outcome with
      | returned final => rw [run_return transition step] at fault; cases fault
      | syscall request =>
        have same : Error.syscallBoundary = error := Except.error.inj ((run_syscall transition step).symm.trans fault)
        exact .inr ⟨0, [], by omega, initial, .nil, .inr ⟨same.symm, request, reads, step⟩⟩
      | next middle =>
        cases tail : run transition (choices.drop 1) fuel middle with
        | ok result => rw [run_next transition step, tail] at fault; cases fault
        | error machineError =>
          have same : machineError = error := by
            simpa only [run_next transition step, tail, Except.map, Except.error.injEq] using fault
          subst machineError
          rcases induction tail with exhausted | ⟨count, priorReads, bound, before, block, actual⟩
          · exact .inl exhausted
          · refine .inr ⟨count + 1, reads ++ priorReads, by omega, before, .next step block, ?_⟩
            simpa [ChoiceStream.drop, Nat.add_comm] using actual
      | atomic event middle =>
        cases tail : run transition (choices.drop 1) fuel middle with
        | ok result => rw [run_atomic transition step, tail] at fault; cases fault
        | error machineError =>
          have same : machineError = error := by
            simpa only [run_atomic transition step, tail, Except.map, Except.error.injEq] using fault
          subst machineError
          rcases induction tail with exhausted | ⟨count, priorReads, bound, before, block, actual⟩
          · exact .inl exhausted
          · refine .inr ⟨count + 1, reads ++ priorReads, by omega, before, .atomic step block, ?_⟩
            simpa [ChoiceStream.drop, Nat.add_comm] using actual

theorem AllExecutions.no_fault_trace {initial : State} {contract : Result → Prop}
    (correct : AllExecutions transition initial contract) {choices : ChoiceStream Choice} {error : Error}
    {count : Nat} {reads : List Read} : ¬ FaultTrace transition choices initial error count reads := by
  intro fault
  obtain ⟨result, execution, _⟩ := correct choices
  have success := run_complete transition execution (fuel := result.instructions + count + 1) (by omega)
  have failed := fault.run transition (fuel := result.instructions + count + 1) (by omega)
  rw [success] at failed
  cases failed

theorem AllExecutions.safe {initial : State} {contract : Result → Prop}
    (correct : AllExecutions transition initial contract) : Safe transition initial := by
  intro before reachable af
  obtain ⟨choices, count, reads, block⟩ := reachable
  let extension : ChoiceStream Choice := fun index => if index < count then choices index else af
  have agree : choices.Agree extension count := by
    intro index bound
    simp [extension, bound]
  have block := block.restrict_choices transition agree
  have nextChoice : extension count = af := by simp [extension]
  cases chosen : transition af before with
  | error fault =>
    exact False.elim (correct.no_fault_trace transition
      ⟨before, block, .inl (by simpa [nextChoice] using chosen)⟩)
  | ok observation =>
    rcases observation with ⟨outcome, accesses⟩
    refine ⟨⟨outcome, accesses⟩, rfl, ?_⟩
    intro request same
    change outcome = .syscall request at same
    subst outcome
    exact correct.no_fault_trace transition
      ⟨before, block, .inr ⟨rfl, request, accesses, by simpa [nextChoice] using chosen⟩⟩

theorem run_instructions_le {choices : ChoiceStream Choice} {fuel : Nat} {initial : State} {result : Result}
    (success : run transition choices fuel initial = .ok result) : result.instructions ≤ fuel := by
  have execution := run_sound transition success
  by_cases enough : result.instructions ≤ fuel
  · exact enough
  · have failed := execution.exhausted transition (by omega : fuel < result.instructions)
    rw [success] at failed
    cases failed

end EDSL.X86.Sequential.Engine
