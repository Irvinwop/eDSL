/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Model

namespace EDSL.X86.Sequential

/-- One choice value for each retired instruction. The choice domain can encode
several independent undefined flags. Positions are never reused for a later
instruction; a transition may ignore choices that do not affect it. -/
abbrev ChoiceStream (Choice : Type) := Nat → Choice

def ChoiceStream.drop {Choice : Type} (choices : ChoiceStream Choice) (count : Nat) : ChoiceStream Choice :=
  fun index => choices (count + index)

@[simp] theorem ChoiceStream.drop_zero {Choice : Type} (choices : ChoiceStream Choice) : choices.drop 0 = choices := by
  funext index
  simp [ChoiceStream.drop]

@[simp] theorem ChoiceStream.drop_drop {Choice : Type} (choices : ChoiceStream Choice) (left right : Nat) :
    (choices.drop left).drop right = choices.drop (left + right) := by
  funext index
  simp [ChoiceStream.drop, Nat.add_assoc]

/-- Only a finite prefix matters to a finite execution. -/
def ChoiceStream.Agree {Choice : Type} (left right : ChoiceStream Choice) (count : Nat) : Prop :=
  ∀ index, index < count → left index = right index

theorem ChoiceStream.Agree.refl {Choice : Type} (choices : ChoiceStream Choice) (count : Nat) : choices.Agree choices count :=
  fun _ _ => rfl

theorem ChoiceStream.Agree.mono {Choice : Type} {left right : ChoiceStream Choice} {short long : Nat}
    (agree : left.Agree right long) (bound : short ≤ long) : left.Agree right short :=
  fun index before => agree index (by omega)

theorem ChoiceStream.Agree.drop {Choice : Type} {left right : ChoiceStream Choice} {count : Nat}
    (agree : left.Agree right (count + 1)) :
    (left.drop 1).Agree (right.drop 1) count := by
  intro index before
  exact agree (1 + index) (by omega)

/-- The existing single-bit machine interface. Its metadata names AF or OF;
instructions with several independent undefined flags need a larger choice
domain and are not represented by this Bool schedule. -/
abbrev Choices := ChoiceStream Bool

abbrev Choices.drop (choices : Choices) (count : Nat) : Choices :=
  ChoiceStream.drop choices count

theorem Choices.drop_zero (choices : Choices) : choices.drop 0 = choices :=
  ChoiceStream.drop_zero choices

theorem Choices.drop_drop (choices : Choices) (left right : Nat) :
    (choices.drop left).drop right = choices.drop (left + right) :=
  ChoiceStream.drop_drop choices left right

abbrev Choices.Agree (left right : Choices) (count : Nat) : Prop :=
  ChoiceStream.Agree left right count

theorem Choices.Agree.refl (choices : Choices) (count : Nat) : choices.Agree choices count :=
  ChoiceStream.Agree.refl choices count

theorem Choices.Agree.mono {left right : Choices} {short long : Nat}
    (agree : left.Agree right long) (bound : short ≤ long) : left.Agree right short :=
  ChoiceStream.Agree.mono agree bound

theorem Choices.Agree.drop {left right : Choices} {count : Nat}
    (agree : left.Agree right (count + 1)) :
    (left.drop 1).Agree (right.drop 1) count :=
  ChoiceStream.Agree.drop agree

structure Result where
  state : State
  instructions : Nat
  reads : List Read

/-- Prefix a continuing block's exact cost and successful operand reads. -/
def Result.prepend (count : Nat) (reads : List Read) (result : Result) : Result :=
  ⟨result.state, count + result.instructions, reads ++ result.reads⟩

@[simp] theorem Result.prepend_zero (result : Result) : result.prepend 0 [] = result := by
  cases result
  simp [Result.prepend]

@[simp] theorem Result.prepend_prepend (result : Result) (left right : Nat)
    (leftReads rightReads : List Read) :
    (result.prepend right rightReads).prepend left leftReads =
      result.prepend (left + right) (leftReads ++ rightReads) := by
  simp [Result.prepend, Nat.add_assoc, List.append_assoc]

/- Generic proofs over an observation-producing transition. The public machine
API in `Execution.lean` instantiates this parameter with the actual decoder and
executor, rather than a client-provided opcode or program-counter gate. -/
namespace Engine

variable {Choice : Type} (transition : Choice → State → Except Error Observation)

def run (choices : ChoiceStream Choice) : Nat → State → Except Error Result
  | 0, _ => .error .exhaustedFuel
  | fuel + 1, state => do
    let observation ← transition (choices 0) state
    match observation.result with
    | .returned final => return ⟨final, 1, observation.reads⟩
    | .syscall _ => throw .syscallBoundary
    | .next middle | .atomic _ middle =>
      let result ← run (choices.drop 1) fuel middle
      return result.prepend 1 observation.reads

@[simp] theorem run_zero (choices : ChoiceStream Choice) (state : State) :
    run transition choices 0 state = .error .exhaustedFuel := rfl

theorem run_return {choices : ChoiceStream Choice} {fuel : Nat} {initial final : State} {reads : List Read}
    (step : transition (choices 0) initial = .ok ⟨.returned final, reads⟩) :
    run transition choices (fuel + 1) initial = .ok ⟨final, 1, reads⟩ := by
  simp [run, step]

theorem run_next {choices : ChoiceStream Choice} {fuel : Nat} {initial middle : State} {reads : List Read}
    (step : transition (choices 0) initial = .ok ⟨.next middle, reads⟩) :
    run transition choices (fuel + 1) initial =
      (run transition (choices.drop 1) fuel middle).map (Result.prepend 1 reads) := by
  simp [run, step]
  cases run transition (choices.drop 1) fuel middle <;> rfl

theorem run_atomic {choices : ChoiceStream Choice} {fuel : Nat} {initial middle : State}
    {event : AtomicEvent} {reads : List Read}
    (step : transition (choices 0) initial = .ok ⟨.atomic event middle, reads⟩) :
    run transition choices (fuel + 1) initial =
      (run transition (choices.drop 1) fuel middle).map (Result.prepend 1 reads) := by
  simp [run, step]
  cases run transition (choices.drop 1) fuel middle <;> rfl

theorem run_fault {choices : ChoiceStream Choice} {fuel : Nat} {initial : State} {error : Error}
    (step : transition (choices 0) initial = .error error) :
    run transition choices (fuel + 1) initial = .error error := by
  simp [run, step]

theorem run_syscall {choices : ChoiceStream Choice} {fuel : Nat} {initial : State}
    {request : SyscallRequest} {reads : List Read}
    (step : transition (choices 0) initial = .ok ⟨.syscall request, reads⟩) :
    run transition choices (fuel + 1) initial = .error .syscallBoundary := by
  simp [run, step]

/-- Finite returning executions preserve their choices, complete final state,
exact retired instruction count and actual successful operand-read trace. -/
inductive Executes : ChoiceStream Choice → State → Result → Prop where
  | ret {choices initial final reads}
      (step : transition (choices 0) initial = .ok ⟨.returned final, reads⟩) :
      Executes choices initial ⟨final, 1, reads⟩
  | next {choices initial middle result reads}
      (step : transition (choices 0) initial = .ok ⟨.next middle, reads⟩)
      (tail : Executes (choices.drop 1) middle result) :
      Executes choices initial (result.prepend 1 reads)
  | atomic {choices initial middle result reads event}
      (step : transition (choices 0) initial = .ok ⟨.atomic event middle, reads⟩)
      (tail : Executes (choices.drop 1) middle result) :
      Executes choices initial (result.prepend 1 reads)

/-- Finite continuing traces, including the empty trace. Return and syscall are
boundaries, so neither is a continuing block instruction. -/
inductive Block : ChoiceStream Choice → State → State → Nat → List Read → Prop where
  | nil {choices state} : Block choices state state 0 []
  | next {choices initial middle final count reads rest}
      (step : transition (choices 0) initial = .ok ⟨.next middle, reads⟩)
      (tail : Block (choices.drop 1) middle final count rest) :
      Block choices initial final (count + 1) (reads ++ rest)
  | atomic {choices initial middle final count reads rest event}
      (step : transition (choices 0) initial = .ok ⟨.atomic event middle, reads⟩)
      (tail : Block (choices.drop 1) middle final count rest) :
      Block choices initial final (count + 1) (reads ++ rest)

theorem run_sound {choices : ChoiceStream Choice} {fuel : Nat} {initial : State} {result : Result}
    (success : run transition choices fuel initial = .ok result) :
    Executes transition choices initial result := by
  induction fuel generalizing choices initial result with
  | zero => simp [run] at success
  | succ fuel induction =>
    cases step : transition (choices 0) initial with
    | error fault => simp [run, step] at success
    | ok observation =>
      rcases observation with ⟨outcome, reads⟩
      cases outcome with
      | syscall request => simp [run, step] at success
      | returned final =>
        simp [run, step] at success
        cases success
        exact .ret step
      | next middle =>
        cases tail : run transition (choices.drop 1) fuel middle with
        | error fault => simp [run, step, tail] at success
        | ok rest =>
          simp [run, step, tail] at success
          cases success
          exact .next step (induction tail)
      | atomic event middle =>
        cases tail : run transition (choices.drop 1) fuel middle with
        | error fault => simp [run, step, tail] at success
        | ok rest =>
          simp [run, step, tail] at success
          cases success
          exact .atomic step (induction tail)

theorem Executes.positive {choices : ChoiceStream Choice} {initial : State} {result : Result}
    (execution : Executes transition choices initial result) : 0 < result.instructions := by
  cases execution <;> simp only [Result.prepend] <;> omega

theorem run_complete {choices : ChoiceStream Choice} {initial : State} {result : Result} {fuel : Nat}
    (execution : Executes transition choices initial result) (enough : result.instructions ≤ fuel) :
    run transition choices fuel initial = .ok result := by
  induction execution generalizing fuel with
  | ret step =>
    cases fuel with
    | zero => simp at enough
    | succ fuel => exact run_return transition step
  | @next choices initial middle result reads step tail induction =>
    cases fuel with
    | zero => simp [Result.prepend] at enough
    | succ fuel =>
      have bound : result.instructions ≤ fuel := by
        simp only [Result.prepend] at enough
        omega
      simp [run_next transition step, induction bound, Except.map]
  | @atomic choices initial middle result reads event step tail induction =>
    cases fuel with
    | zero => simp [Result.prepend] at enough
    | succ fuel =>
      have bound : result.instructions ≤ fuel := by
        simp only [Result.prepend] at enough
        omega
      simp [run_atomic transition step, induction bound, Except.map]

theorem Executes.exhausted {choices : ChoiceStream Choice} {initial : State} {result : Result} {fuel : Nat}
    (execution : Executes transition choices initial result) (short : fuel < result.instructions) :
    run transition choices fuel initial = .error .exhaustedFuel := by
  induction execution generalizing fuel with
  | ret step =>
    have : fuel = 0 := by simpa using short
    subst fuel
    rfl
  | @next choices initial middle result reads step tail induction =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      have bound : fuel < result.instructions := by
        simp only [Result.prepend] at short
        omega
      simp [run_next transition step, induction bound, Except.map]
  | @atomic choices initial middle result reads event step tail induction =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      have bound : fuel < result.instructions := by
        simp only [Result.prepend] at short
        omega
      simp [run_atomic transition step, induction bound, Except.map]

theorem Executes.run_eq {choices : ChoiceStream Choice} {initial : State} {result : Result} (fuel : Nat)
    (execution : Executes transition choices initial result) :
    run transition choices fuel initial =
      if result.instructions ≤ fuel then .ok result else .error .exhaustedFuel := by
  split
  · exact run_complete transition execution ‹_›
  · exact execution.exhausted _ (by omega)

theorem Executes.no_fault_prefix {choices : ChoiceStream Choice} {initial : State} {result : Result}
    (execution : Executes transition choices initial result) {fuel : Nat} {error : Error}
    (fault : run transition choices fuel initial = .error error) : error = .exhaustedFuel := by
  rw [execution.run_eq transition fuel] at fault
  split at fault
  · cases fault
  · exact (Except.error.inj fault).symm

/-- Determinism only after fixing the complete choice stream. -/
theorem Executes.fixed_choices_unique {choices : ChoiceStream Choice} {initial : State} {left right : Result}
    (first : Executes transition choices initial left)
    (second : Executes transition choices initial right) : left = right := by
  have leftRun := run_complete transition first (fuel := left.instructions + right.instructions) (by omega)
  have rightRun := run_complete transition second (fuel := left.instructions + right.instructions) (by omega)
  exact Except.ok.inj (leftRun.symm.trans rightRun)

theorem Executes.restrict_choices {choices other : ChoiceStream Choice} {initial : State} {result : Result}
    (execution : Executes transition choices initial result)
    (agree : choices.Agree other result.instructions) : Executes transition other initial result := by
  induction execution generalizing other with
  | ret step =>
    have head := agree 0 (by simp)
    exact .ret (by simpa [head] using step)
  | @next choices initial middle result reads step tail induction =>
    have head := agree 0 (by simp only [Result.prepend]; omega)
    exact .next (by simpa [head] using step) (induction ((by simpa [Result.prepend, Nat.add_comm] using agree : choices.Agree other (result.instructions + 1)).drop))
  | @atomic choices initial middle result reads event step tail induction =>
    have head := agree 0 (by simp only [Result.prepend]; omega)
    exact .atomic (by simpa [head] using step) (induction ((by simpa [Result.prepend, Nat.add_comm] using agree : choices.Agree other (result.instructions + 1)).drop))

theorem run_complete_prefix {choices other : ChoiceStream Choice} {initial : State} {result : Result} {fuel : Nat}
    (execution : Executes transition choices initial result)
    (agree : choices.Agree other result.instructions) (enough : result.instructions ≤ fuel) :
    run transition other fuel initial = .ok result :=
  run_complete transition (execution.restrict_choices transition agree) enough

theorem Block.append {choices : ChoiceStream Choice} {initial middle final : State} {left right : Nat}
    {leftReads rightReads : List Read}
    (first : Block transition choices initial middle left leftReads)
    (second : Block transition (choices.drop left) middle final right rightReads) :
    Block transition choices initial final (left + right) (leftReads ++ rightReads) := by
  induction first with
  | nil => simpa using second
  | @next choices initial next middle count reads rest step tail induction =>
    have rest := induction (by simpa [Nat.add_comm] using second)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc] using Block.next step rest
  | @atomic choices initial next middle count reads rest event step tail induction =>
    have rest := induction (by simpa [Nat.add_comm] using second)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc] using Block.atomic step rest

theorem Block.then_executes {choices : ChoiceStream Choice} {initial middle : State} {count : Nat}
    {reads : List Read} {result : Result}
    (block : Block transition choices initial middle count reads)
    (tail : Executes transition (choices.drop count) middle result) :
    Executes transition choices initial (result.prepend count reads) := by
  induction block with
  | nil => simpa using tail
  | @next choices initial next middle count reads rest step block induction =>
    have finish := induction (by simpa [Nat.add_comm] using tail)
    simpa [Nat.add_comm] using Executes.next step finish
  | @atomic choices initial next middle count reads rest event step block induction =>
    have finish := induction (by simpa [Nat.add_comm] using tail)
    simpa [Nat.add_comm] using Executes.atomic step finish

theorem Block.run_append {choices : ChoiceStream Choice} {initial middle : State} {count fuel : Nat}
    {reads : List Read} {result : Result}
    (block : Block transition choices initial middle count reads)
    (tail : run transition (choices.drop count) fuel middle = .ok result) :
    run transition choices (count + fuel) initial = .ok (result.prepend count reads) := by
  induction block with
  | nil => simpa using tail
  | @next choices initial next middle count reads rest step block induction =>
    have finish := induction (by simpa [Nat.add_comm] using tail)
    rw [show count + 1 + fuel = (count + fuel) + 1 by omega, run_next transition step, finish]
    simp [Except.map, Nat.add_comm]
  | @atomic choices initial next middle count reads rest event step block induction =>
    have finish := induction (by simpa [Nat.add_comm] using tail)
    rw [show count + 1 + fuel = (count + fuel) + 1 by omega, run_atomic transition step, finish]
    simp [Except.map, Nat.add_comm]

theorem Block.restrict_choices {choices other : ChoiceStream Choice} {initial final : State} {count : Nat}
    {reads : List Read} (block : Block transition choices initial final count reads)
    (agree : choices.Agree other count) : Block transition other initial final count reads := by
  induction block generalizing other with
  | nil => exact .nil
  | next step tail induction =>
    have head := agree 0 (by omega)
    exact .next (by simpa [head] using step) (induction agree.drop)
  | atomic step tail induction =>
    have head := agree 0 (by omega)
    exact .atomic (by simpa [head] using step) (induction agree.drop)

end Engine
end EDSL.X86.Sequential
