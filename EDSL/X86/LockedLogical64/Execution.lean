/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedLogical64.Machine

namespace EDSL.X86.LockedLogical64

/-- One AF choice for each successful retired instruction. Failed steps do not
advance this stream. RET ignores its choice. This engine models one uninterrupted
CPU execution; peer scheduling belongs to the separate OS transition relation. -/
abbrev Choices := Nat → Bool

def Choices.drop (choices : Choices) (count : Nat) : Choices :=
  fun index => choices (count + index)

@[simp] theorem Choices.drop_zero (choices : Choices) : choices.drop 0 = choices := by
  funext index
  simp [Choices.drop]

@[simp] theorem Choices.drop_drop (choices : Choices) (left right : Nat) :
    (choices.drop left).drop right = choices.drop (left + right) := by
  funext index
  simp [Choices.drop, Nat.add_assoc]

def Choices.Agree (left right : Choices) (count : Nat) : Prop :=
  ∀ index, index < count → left index = right index

theorem Choices.Agree.drop {left right : Choices} {count : Nat}
    (agree : left.Agree right (count + 1)) :
    (left.drop 1).Agree (right.drop 1) count := by
  intro index before
  exact agree (1 + index) (by omega)

/-- Exact returned CPU, retired count, ordered full64 RMW labels and ordered
operand footprints. RET has a stack footprint and no RMW label. -/
structure Result where
  state : State
  instructions : Nat
  events : List LogicalEvent64
  accesses : List Access

def Result.prepend (count : Nat) (events : List LogicalEvent64)
    (accesses : List Access) (result : Result) : Result :=
  ⟨result.state, count + result.instructions, events ++ result.events,
    accesses ++ result.accesses⟩

@[simp] theorem Result.prepend_zero (result : Result) :
    result.prepend 0 [] [] = result := by
  cases result
  simp [Result.prepend]

@[simp] theorem Result.prepend_prepend (result : Result) (left right : Nat)
    (leftEvents rightEvents : List LogicalEvent64) (leftAccesses rightAccesses : List Access) :
    (result.prepend right rightEvents rightAccesses).prepend left leftEvents leftAccesses =
      result.prepend (left + right) (leftEvents ++ rightEvents) (leftAccesses ++ rightAccesses) := by
  simp [Result.prepend, Nat.add_assoc, List.append_assoc]

/-- Execute only the actual strict decoder/executor, retaining every event.
A failed step returns its precise fault before any recursive stream advance. -/
def run (choices : Choices) : Nat → State → Except Error Result
  | 0, _ => .error .exhaustedFuel
  | fuel + 1, initial => do
    let observation ← step (choices 0) initial
    match observation.result with
    | .returned final => return ⟨final, 1, [], observation.accesses⟩
    | .atomic64 event middle =>
      let result ← run (choices.drop 1) fuel middle
      return result.prepend 1 [event] observation.accesses

@[simp] theorem run_zero (choices : Choices) (initial : State) :
    run choices 0 initial = .error .exhaustedFuel := rfl

theorem run_return {choices : Choices} {fuel : Nat} {initial final : State}
    {accesses : List Access}
    (actual : step (choices 0) initial = .ok ⟨.returned final, accesses⟩) :
    run choices (fuel + 1) initial = .ok ⟨final, 1, [], accesses⟩ := by
  simp [run, actual]

theorem run_atomic64 {choices : Choices} {fuel : Nat} {initial middle : State}
    {event : LogicalEvent64} {accesses : List Access}
    (actual : step (choices 0) initial = .ok ⟨.atomic64 event middle, accesses⟩) :
    run choices (fuel + 1) initial =
      (run (choices.drop 1) fuel middle).map (Result.prepend 1 [event] accesses) := by
  simp [run, actual]
  cases run (choices.drop 1) fuel middle <;> rfl

theorem run_fault {choices : Choices} {fuel : Nat} {initial : State} {fault : Error}
    (actual : step (choices 0) initial = .error fault) :
    run choices (fuel + 1) initial = .error fault := by
  simp [run, actual]

/-- Successful finite executions retain observations from actual steps.
There is no externally supplied instruction, event, memory or PC gate. -/
inductive Executes : Choices → State → Result → Prop where
  | ret {choices initial final accesses}
      (actual : step (choices 0) initial = .ok ⟨.returned final, accesses⟩) :
      Executes choices initial ⟨final, 1, [], accesses⟩
  | atomic64 {choices initial middle result accesses event}
      (actual : step (choices 0) initial = .ok ⟨.atomic64 event middle, accesses⟩)
      (tail : Executes (choices.drop 1) middle result) :
      Executes choices initial (result.prepend 1 [event] accesses)

/-- Continuing prefixes retain full ordered event/access lists. A return is a
terminal boundary, never a continuing step. -/
inductive Block : Choices → State → State → Nat → List LogicalEvent64 → List Access → Prop where
  | nil {choices state} : Block choices state state 0 [] []
  | atomic64 {choices initial middle final count events accesses rest event}
      (actual : step (choices 0) initial = .ok ⟨.atomic64 event middle, accesses⟩)
      (tail : Block (choices.drop 1) middle final count events rest) :
      Block choices initial final (count + 1) (event :: events) (accesses ++ rest)

theorem run_sound {choices : Choices} {fuel : Nat} {initial : State} {result : Result}
    (success : run choices fuel initial = .ok result) : Executes choices initial result := by
  induction fuel generalizing choices initial result with
  | zero => simp [run] at success
  | succ fuel induction =>
    cases actual : step (choices 0) initial with
    | error fault => simp [run, actual] at success
    | ok observation =>
      rcases observation with ⟨outcome, accesses⟩
      cases outcome with
      | returned final =>
        simp [run, actual] at success
        cases success
        exact .ret actual
      | atomic64 event middle =>
        cases tail : run (choices.drop 1) fuel middle with
        | error fault => simp [run, actual, tail] at success
        | ok rest =>
          simp [run, actual, tail] at success
          cases success
          exact .atomic64 actual (induction tail)

theorem Executes.positive {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) : 0 < result.instructions := by
  cases execution <;> simp only [Result.prepend] <;> omega

theorem run_complete {choices : Choices} {initial : State} {result : Result} {fuel : Nat}
    (execution : Executes choices initial result) (enough : result.instructions ≤ fuel) :
    run choices fuel initial = .ok result := by
  induction execution generalizing fuel with
  | ret actual =>
    cases fuel with
    | zero => simp at enough
    | succ fuel => exact run_return actual
  | @atomic64 choices initial middle result accesses event actual tail induction =>
    cases fuel with
    | zero => simp [Result.prepend] at enough
    | succ fuel =>
      have bound : result.instructions ≤ fuel := by
        simp only [Result.prepend] at enough
        omega
      simp [run_atomic64 actual, induction bound, Except.map]

theorem Executes.exhausted {choices : Choices} {initial : State} {result : Result} {fuel : Nat}
    (execution : Executes choices initial result) (short : fuel < result.instructions) :
    run choices fuel initial = .error .exhaustedFuel := by
  induction execution generalizing fuel with
  | ret actual =>
    have : fuel = 0 := by simpa using short
    subst fuel
    rfl
  | @atomic64 choices initial middle result accesses event actual tail induction =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      have bound : fuel < result.instructions := by
        simp only [Result.prepend] at short
        omega
      simp [run_atomic64 actual, induction bound, Except.map]

theorem Executes.run_eq {choices : Choices} {initial : State} {result : Result} (fuel : Nat)
    (execution : Executes choices initial result) :
    run choices fuel initial =
      if result.instructions ≤ fuel then .ok result else .error .exhaustedFuel := by
  split
  · exact run_complete execution ‹_›
  · exact execution.exhausted (by omega)

theorem Executes.no_fault_prefix {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) {fuel : Nat} {fault : Error}
    (actual : run choices fuel initial = .error fault) : fault = .exhaustedFuel := by
  rw [execution.run_eq fuel] at actual
  split at actual
  · cases actual
  · exact (Except.error.inj actual).symm

/-- Deterministic only after fixing the AF stream. -/
theorem Executes.fixed_choices_unique {choices : Choices} {initial : State} {left right : Result}
    (first : Executes choices initial left) (second : Executes choices initial right) : left = right := by
  have leftRun := run_complete first (fuel := left.instructions + right.instructions) (by omega)
  have rightRun := run_complete second (fuel := left.instructions + right.instructions) (by omega)
  exact Except.ok.inj (leftRun.symm.trans rightRun)

theorem Executes.restrict_choices {choices other : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result)
    (agree : choices.Agree other result.instructions) : Executes other initial result := by
  induction execution generalizing other with
  | ret actual =>
    have head := agree 0 (by simp)
    exact .ret (by simpa [head] using actual)
  | @atomic64 choices initial middle result accesses event actual tail induction =>
    have head := agree 0 (by simp only [Result.prepend]; omega)
    have dropped : (choices.drop 1).Agree (other.drop 1) result.instructions :=
      (by simpa [Result.prepend, Nat.add_comm] using agree :
        choices.Agree other (result.instructions + 1)).drop
    exact .atomic64 (by simpa [head] using actual) (induction dropped)

theorem run_choices_congr {left right : Choices} {fuel : Nat} {initial : State}
    (agree : left.Agree right fuel) : run left fuel initial = run right fuel initial := by
  induction fuel generalizing left right initial with
  | zero => rfl
  | succ fuel induction =>
    have head := agree 0 (by omega)
    cases actual : step (right 0) initial with
    | error fault => simp [run, head, actual]
    | ok observation =>
      rcases observation with ⟨outcome, accesses⟩
      cases outcome with
      | returned final => simp [run, head, actual]
      | atomic64 event middle =>
        simp only [run, head, actual, ok_bind]
        rw [induction agree.drop]

theorem Block.append {choices : Choices} {initial middle final : State} {left right : Nat}
    {leftEvents rightEvents : List LogicalEvent64} {leftAccesses rightAccesses : List Access}
    (first : Block choices initial middle left leftEvents leftAccesses)
    (second : Block (choices.drop left) middle final right rightEvents rightAccesses) :
    Block choices initial final (left + right) (leftEvents ++ rightEvents)
      (leftAccesses ++ rightAccesses) := by
  induction first with
  | nil => simpa using second
  | @atomic64 choices initial next middle count events accesses rest event actual tail induction =>
    have finish := induction (by simpa [Nat.add_comm] using second)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc] using
      Block.atomic64 actual finish

theorem Block.then_executes {choices : Choices} {initial middle : State} {count : Nat}
    {events : List LogicalEvent64} {accesses : List Access} {result : Result}
    (block : Block choices initial middle count events accesses)
    (tail : Executes (choices.drop count) middle result) :
    Executes choices initial (result.prepend count events accesses) := by
  induction block with
  | nil => simpa using tail
  | @atomic64 choices initial next middle count events accesses rest event actual block induction =>
    have finish := induction (by simpa [Nat.add_comm] using tail)
    simpa [Nat.add_comm] using Executes.atomic64 actual finish

theorem Block.run_append {choices : Choices} {initial middle : State} {count fuel : Nat}
    {events : List LogicalEvent64} {accesses : List Access} {result : Result}
    (block : Block choices initial middle count events accesses)
    (tail : run (choices.drop count) fuel middle = .ok result) :
    run choices (count + fuel) initial = .ok (result.prepend count events accesses) := by
  induction block with
  | nil => simpa using tail
  | @atomic64 choices initial next middle count events accesses rest event actual block induction =>
    have finish := induction (by simpa [Nat.add_comm] using tail)
    rw [show count + 1 + fuel = (count + fuel) + 1 by omega, run_atomic64 actual, finish]
    simp [Except.map, Nat.add_comm]

theorem Block.restrict_choices {choices other : Choices} {initial final : State} {count : Nat}
    {events : List LogicalEvent64} {accesses : List Access}
    (block : Block choices initial final count events accesses)
    (agree : choices.Agree other count) : Block other initial final count events accesses := by
  induction block generalizing other with
  | nil => exact .nil
  | atomic64 actual tail induction =>
    have head := agree 0 (by omega)
    exact .atomic64 (by simpa [head] using actual) (induction agree.drop)

/-- Exact accounting for this strict profile: one RMW per continuing
instruction, followed by one genuine RET. This is not a global code optimum. -/
theorem Executes.event_count {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) :
    result.events.length + 1 = result.instructions := by
  induction execution with
  | ret actual => rfl
  | atomic64 actual tail induction => simp [Result.prepend, induction, Nat.add_comm]

theorem Block.event_count {choices : Choices} {initial final : State} {count : Nat}
    {events : List LogicalEvent64} {accesses : List Access}
    (block : Block choices initial final count events accesses) : events.length = count := by
  induction block with
  | nil => rfl
  | atomic64 actual tail induction => simp [induction]

theorem Executes.access_count {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) : result.accesses.length = result.instructions := by
  induction execution with
  | ret actual =>
    rw [(step_returned_sound actual).2.2]
    rfl
  | atomic64 actual tail induction =>
    simp [Result.prepend, (step_atomic64_sound actual).2.2, induction, Nat.add_comm]

/-- Every event has an actual current-memory instruction origin at its exact
ordered position. Prefixes cannot invent, reorder or truncate RMW labels. -/
theorem Executes.event_origin {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) {index : Nat} {event : LogicalEvent64}
    (present : result.events[index]? = some event) :
    ∃ before middle priorEvents priorAccesses accesses,
      Block choices initial before index priorEvents priorAccesses ∧
      step (choices index) before = .ok ⟨.atomic64 event middle, accesses⟩ ∧
      priorEvents.length = index ∧ OrEffect before (choices index) event middle := by
  induction execution generalizing index with
  | ret actual => simp at present
  | @atomic64 choices initial next result accesses head actual tail induction =>
    cases index with
    | zero =>
      simp [Result.prepend] at present
      subst event
      exact ⟨initial, next, [], [], accesses, .nil, actual, rfl,
        (step_atomic64_sound actual).2.1⟩
    | succ index =>
      have later : result.events[index]? = some event := by simpa [Result.prepend] using present
      obtain ⟨before, middle, priorEvents, priorAccesses, lastAccesses, block, current, length, effect⟩ :=
        induction later
      refine ⟨before, middle, head :: priorEvents, accesses ++ priorAccesses, lastAccesses,
        .atomic64 actual block, ?_, by simp [length], ?_⟩
      · simpa [Choices.drop, Nat.add_comm] using current
      · simpa [Choices.drop, Nat.add_comm] using effect

/-- Every operand footprint is attached to an actual successful instruction
with its pre-state and choice index. No entry-memory read authority is inferred. -/
theorem Executes.access_origin {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) {access : Access}
    (present : access ∈ result.accesses) :
    ∃ count before priorEvents priorAccesses observation, count < result.instructions ∧
      Block choices initial before count priorEvents priorAccesses ∧
      step (choices count) before = .ok observation ∧
      access ∈ observation.accesses ∧ AccessSucceeds before access := by
  induction execution with
  | @ret choices initial final accesses actual =>
    have succeeded := execute_accesses_succeed (step_sound actual).choose_spec.2
    exact ⟨0, initial, [], [], ⟨.returned final, accesses⟩, by simp, .nil, actual,
      present, succeeded access present⟩
  | @atomic64 choices initial middle result accesses event actual tail induction =>
    rcases List.mem_append.mp present with first | later
    · have succeeded := execute_accesses_succeed (step_sound actual).choose_spec.2
      exact ⟨0, initial, [], [], ⟨.atomic64 event middle, accesses⟩,
        by simp only [Result.prepend]; omega, .nil, actual, first, succeeded access first⟩
    · obtain ⟨count, before, priorEvents, priorAccesses, observation, bound, block, current, member, succeeds⟩ :=
        induction later
      refine ⟨count + 1, before, event :: priorEvents, accesses ++ priorAccesses, observation,
        by simp only [Result.prepend]; omega, .atomic64 actual block, ?_, member, succeeds⟩
      simpa [Choices.drop, Nat.add_comm] using current

/-- The terminal state comes from an actual RET, after the entire ordered
RMW prefix. RET contributes no event and preserves its current RAM. -/
theorem Executes.terminal_origin {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) :
    ∃ count before priorAccesses lastAccesses,
      count + 1 = result.instructions ∧
      Block choices initial before count result.events priorAccesses ∧
      step (choices count) before = .ok ⟨.returned result.state, lastAccesses⟩ ∧
      result.accesses = priorAccesses ++ lastAccesses ∧ RetEffect before result.state := by
  induction execution with
  | @ret choices initial final accesses actual =>
    exact ⟨0, initial, [], accesses, rfl, .nil, actual, rfl,
      (step_returned_sound actual).2.1⟩
  | @atomic64 choices initial next result accesses event actual tail induction =>
    obtain ⟨count, before, prior, last, cost, block, current, trace, effect⟩ := induction
    refine ⟨count + 1, before, accesses ++ prior, last, ?_, .atomic64 actual block, ?_, ?_, effect⟩
    · simp only [Result.prepend]
      omega
    · simpa [Choices.drop, Result.prepend, Nat.add_comm] using current
    · simp [Result.prepend, trace, List.append_assoc]

/-- Termination and the stated postcondition for every AF stream. No fixed
stream, default AF, or assumed future runner success is hidden in this claim. -/
def AllExecutions (initial : State) (post : Result → Prop) : Prop :=
  ∀ choices, ∃ result, Executes choices initial result ∧ post result

theorem AllExecutions.no_fault_prefix {initial : State} {post : Result → Prop}
    (all : AllExecutions initial post) (choices : Choices) {fuel : Nat} {fault : Error}
    (actual : run choices fuel initial = .error fault) : fault = .exhaustedFuel := by
  obtain ⟨result, execution, _⟩ := all choices
  exact execution.no_fault_prefix actual

end EDSL.X86.LockedLogical64
