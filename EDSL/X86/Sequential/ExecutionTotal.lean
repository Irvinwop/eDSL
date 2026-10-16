/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ExecutionCore

namespace EDSL.X86.Sequential

def nextState : StepResult → Option State
  | .next state | .atomic _ state => some state
  | .returned _ | .syscall _ => none

namespace Engine

variable (transition : Bool → State → Except Error Observation)

/-- A single chosen transition, including an error outcome. -/
def Step (af : Bool) (initial : State) (outcome : Except Error Observation) : Prop :=
  transition af initial = outcome

def ChosenStep (initial : State) (outcome : Except Error Observation) : Prop :=
  ∃ af, Step transition af initial outcome

def Continues (af : Bool) (initial final : State) (reads : List Read) : Prop :=
  ∃ outcome, transition af initial = .ok ⟨outcome, reads⟩ ∧ nextState outcome = some final

/-- An infinite sequence of actual continuing chosen steps. Its choices may
vary on every instruction, including instructions that ignore their AF choice. -/
def DivergesWith (choices : Choices) (initial : State) : Prop :=
  ∃ states : Nat → State, states 0 = initial ∧
    ∀ index, ∃ reads, Continues transition (choices index) (states index) (states (index + 1)) reads

def Diverges (initial : State) : Prop := ∃ choices, DivergesWith transition choices initial

theorem continuation_of_step {af : Bool} {initial final : State}
    {observation : Observation} {reads : List Read}
    (step : transition af initial = .ok observation)
    (continued : Continues transition af initial final reads) :
    nextState observation.result = some final := by
  obtain ⟨outcome, actual, next⟩ := continued
  have same := Except.ok.inj (step.symm.trans actual)
  cases same
  exact next

theorem DivergesWith.tail {choices : Choices} {initial middle : State}
    {observation : Observation} (step : transition (choices 0) initial = .ok observation)
    (next : nextState observation.result = some middle)
    (divergence : DivergesWith transition choices initial) :
    DivergesWith transition (choices.drop 1) middle := by
  obtain ⟨states, start, steps⟩ := divergence
  obtain ⟨reads, first⟩ := steps 0
  have same := continuation_of_step transition step (by simpa [start] using first)
  have middleState : states 1 = middle := Option.some.inj (same.symm.trans next)
  refine ⟨fun index => states (1 + index), by simpa using middleState, ?_⟩
  intro index
  simpa [Choices.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using steps (1 + index)

theorem Executes.no_divergence_with {choices : Choices} {initial : State} {result : Result}
    (execution : Executes transition choices initial result) :
    ¬ DivergesWith transition choices initial := by
  induction execution with
  | ret step =>
    rintro ⟨states, start, steps⟩
    obtain ⟨reads, first⟩ := steps 0
    have impossible := continuation_of_step transition step (by simpa [start] using first)
    cases impossible
  | next step tail induction | atomic step tail induction =>
    intro divergence
    exact induction (divergence.tail transition step rfl)

def NondetExecutes (initial : State) (result : Result) : Prop :=
  ∃ choices, Executes transition choices initial result

/-- Total correctness quantifies over streams before choosing a result. This
does not require different choices to produce identical concrete flags. -/
def AllExecutions (initial : State) (contract : Result → Prop) : Prop :=
  ∀ choices, ∃ result, Executes transition choices initial result ∧ contract result

theorem AllExecutions.project {initial : State} {contract : Result → Prop}
    (correct : AllExecutions transition initial contract) {result : Result}
    (execution : NondetExecutes transition initial result) : contract result := by
  obtain ⟨choices, actual⟩ := execution
  obtain ⟨expected, good, post⟩ := correct choices
  have same := actual.fixed_choices_unique transition good
  rwa [same]

theorem AllExecutions.no_fault_prefix {initial : State} {contract : Result → Prop}
    (correct : AllExecutions transition initial contract) (choices : Choices)
    {fuel : Nat} {error : Error} (fault : run transition choices fuel initial = .error error) :
    error = .exhaustedFuel := by
  obtain ⟨result, execution, _⟩ := correct choices
  exact execution.no_fault_prefix transition fault

theorem AllExecutions.no_divergence {initial : State} {contract : Result → Prop}
    (correct : AllExecutions transition initial contract) : ¬ Diverges transition initial := by
  rintro ⟨choices, divergence⟩
  obtain ⟨result, execution, _⟩ := correct choices
  exact execution.no_divergence_with transition divergence

theorem AllExecutions.run {initial : State} {contract : Result → Prop} {cost : Nat}
    (correct : AllExecutions transition initial contract)
    (exactCost : ∀ result, contract result → result.instructions = cost) (choices : Choices) :
    ∃ result, run transition choices cost initial = .ok result ∧ contract result := by
  obtain ⟨result, execution, post⟩ := correct choices
  exact ⟨result, run_complete transition execution (by simp [exactCost result post]), post⟩

/-- Every AF choice has a successful return or a smaller invariant state.
Syscalls are external boundaries, and cannot discharge this progress contract. -/
def Ranked (invariant : State → Prop) (rank : State → Nat) (post : State → Prop) : Prop :=
  ∀ initial, invariant initial → ∀ af, ∃ observation,
    transition af initial = .ok observation ∧
      match observation.result with
      | .returned final => post final
      | .next middle | .atomic _ middle => invariant middle ∧ rank middle < rank initial
      | .syscall _ => False

theorem Ranked.execution {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked transition invariant rank post) {initial : State} (valid : invariant initial)
    (choices : Choices) : ∃ result, Executes transition choices initial result ∧
      post result.state ∧ result.instructions ≤ rank initial + 1 := by
  have ranked : ∀ bound, ∀ initial, rank initial = bound → invariant initial → ∀ choices,
      ∃ result, Executes transition choices initial result ∧ post result.state ∧
        result.instructions ≤ bound + 1 := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound induction =>
      intro initial value valid choices
      obtain ⟨⟨outcome, reads⟩, step, after⟩ := progress initial valid (choices 0)
      cases outcome with
      | syscall request => exact False.elim after
      | returned final => exact ⟨⟨final, 1, reads⟩, .ret step, after, by simp⟩
      | next middle =>
        obtain ⟨nextValid, decreased⟩ := after
        obtain ⟨result, execution, post, cost⟩ :=
          induction (rank middle) (by omega) middle rfl nextValid (choices.drop 1)
        exact ⟨result.prepend 1 reads, .next step execution, post, by simp only [Result.prepend]; omega⟩
      | atomic event middle =>
        obtain ⟨nextValid, decreased⟩ := after
        obtain ⟨result, execution, post, cost⟩ :=
          induction (rank middle) (by omega) middle rfl nextValid (choices.drop 1)
        exact ⟨result.prepend 1 reads, .atomic step execution, post, by simp only [Result.prepend]; omega⟩
  exact ranked (rank initial) initial rfl valid choices

theorem Ranked.total {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked transition invariant rank post) {initial : State} (valid : invariant initial)
    (choices : Choices) : ∃ result,
      run transition choices (rank initial + 1) initial = .ok result ∧ post result.state := by
  obtain ⟨result, execution, post, cost⟩ := progress.execution transition valid choices
  exact ⟨result, run_complete transition execution cost, post⟩

theorem Ranked.all_executions {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked transition invariant rank post) {initial : State} (valid : invariant initial) :
    AllExecutions transition initial (fun result => post result.state ∧ result.instructions ≤ rank initial + 1) := by
  intro choices
  obtain ⟨result, execution, post, cost⟩ := progress.execution transition valid choices
  exact ⟨result, execution, post, cost⟩

theorem Ranked.continues {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked transition invariant rank post) {initial final : State}
    (valid : invariant initial) {af : Bool} {outcome : StepResult} {reads : List Read}
    (step : transition af initial = .ok ⟨outcome, reads⟩) (next : nextState outcome = some final) :
    invariant final ∧ rank final < rank initial := by
  obtain ⟨observation, actual, after⟩ := progress initial valid af
  have same := Except.ok.inj (actual.symm.trans step)
  cases same
  cases outcome with
  | next middle | atomic event middle =>
    simp only [nextState, Option.some.injEq] at next
    subst final
    exact after
  | returned state | syscall request => cases next

theorem Ranked.block_invariant {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked transition invariant rank post) {initial final : State}
    (valid : invariant initial) {choices : Choices} {count : Nat} {reads : List Read}
    (block : Block transition choices initial final count reads) :
    invariant final ∧ rank final + count ≤ rank initial := by
  induction block with
  | nil => exact ⟨valid, by omega⟩
  | next step tail induction | atomic step tail induction =>
    obtain ⟨middle, decreased⟩ := progress.continues transition valid step rfl
    obtain ⟨final, bound⟩ := induction middle
    exact ⟨final, by omega⟩

def Reachable (initial final : State) : Prop :=
  ∃ choices count reads, Block transition choices initial final count reads

/-- Safety of every reachable continuing prefix, for both choices at its next
instruction. Successful atomic events remain valid continuing outcomes. -/
def Safe (initial : State) : Prop :=
  ∀ before, Reachable transition initial before → ∀ af, ∃ observation,
    transition af before = .ok observation ∧ ∀ request, observation.result ≠ .syscall request

theorem Ranked.safe {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked transition invariant rank post) {initial : State} (valid : invariant initial) :
    Safe transition initial := by
  intro before reachable af
  obtain ⟨choices, count, reads, block⟩ := reachable
  have invariantBefore := (progress.block_invariant transition valid block).1
  obtain ⟨observation, step, after⟩ := progress before invariantBefore af
  refine ⟨observation, step, ?_⟩
  intro request same
  rw [same] at after
  exact after

theorem Ranked.no_fault_prefix {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked transition invariant rank post) {initial : State} (valid : invariant initial)
    (choices : Choices) {fuel : Nat} {error : Error}
    (fault : run transition choices fuel initial = .error error) : error = .exhaustedFuel :=
  (progress.all_executions transition valid).no_fault_prefix transition choices fault

theorem Ranked.no_divergence {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked transition invariant rank post) {initial : State} (valid : invariant initial) :
    ¬ Diverges transition initial :=
  (progress.all_executions transition valid).no_divergence transition

/-- Loop induction with an exact cost and read frame. Each iteration executes
for every stream, and the induction uses the stream after the actual block cost.
The return suffix is proved once at remaining count zero. No future fuel-success
premise is used. `post` may close over the entry memory, ABI state and independent
functional specification. -/
theorem loop_executes (invariant : Nat → State → Prop) (post : State → Prop)
    (cost : Nat → Nat) (reads : Nat → State → List Read)
    (finish : ∀ choices initial, invariant 0 initial → ∃ result,
      Executes transition choices initial result ∧ post result.state ∧
        result.instructions = cost 0 ∧ result.reads = reads 0 initial)
    (iterate : ∀ remaining choices initial, invariant (remaining + 1) initial →
      ∃ middle count accesses, Block transition choices initial middle count accesses ∧
        invariant remaining middle ∧ cost (remaining + 1) = count + cost remaining ∧
          reads (remaining + 1) initial = accesses ++ reads remaining middle)
    (remaining : Nat) (choices : Choices) (initial : State) (valid : invariant remaining initial) :
    ∃ result, Executes transition choices initial result ∧ post result.state ∧
      result.instructions = cost remaining ∧ result.reads = reads remaining initial := by
  induction remaining generalizing choices initial with
  | zero => exact finish choices initial valid
  | succ remaining induction =>
    obtain ⟨middle, count, accesses, block, middleValid, costFrame, readFrame⟩ :=
      iterate remaining choices initial valid
    obtain ⟨result, execution, post, exactCost, exactReads⟩ :=
      induction (choices.drop count) middle middleValid
    refine ⟨result.prepend count accesses, block.then_executes transition execution, post, ?_, ?_⟩
    · simpa only [Result.prepend, exactCost] using costFrame.symm
    · simpa only [Result.prepend, exactReads] using readFrame.symm

theorem loop_total (invariant : Nat → State → Prop) (post : State → Prop)
    (cost : Nat → Nat) (reads : Nat → State → List Read)
    (finish : ∀ choices initial, invariant 0 initial → ∃ result,
      Executes transition choices initial result ∧ post result.state ∧
        result.instructions = cost 0 ∧ result.reads = reads 0 initial)
    (iterate : ∀ remaining choices initial, invariant (remaining + 1) initial →
      ∃ middle count accesses, Block transition choices initial middle count accesses ∧
        invariant remaining middle ∧ cost (remaining + 1) = count + cost remaining ∧
          reads (remaining + 1) initial = accesses ++ reads remaining middle)
    (remaining : Nat) (choices : Choices) (initial : State) (valid : invariant remaining initial) :
    ∃ result, run transition choices (cost remaining) initial = .ok result ∧ post result.state ∧
      result.instructions = cost remaining ∧ result.reads = reads remaining initial := by
  obtain ⟨result, execution, post, exactCost, exactReads⟩ :=
    loop_executes transition invariant post cost reads finish iterate remaining choices initial valid
  exact ⟨result, run_complete transition execution (by simp [exactCost]), post, exactCost, exactReads⟩

theorem loop_all_executions (invariant : Nat → State → Prop) (post : State → Prop)
    (cost : Nat → Nat) (reads : Nat → State → List Read)
    (finish : ∀ choices initial, invariant 0 initial → ∃ result,
      Executes transition choices initial result ∧ post result.state ∧
        result.instructions = cost 0 ∧ result.reads = reads 0 initial)
    (iterate : ∀ remaining choices initial, invariant (remaining + 1) initial →
      ∃ middle count accesses, Block transition choices initial middle count accesses ∧
        invariant remaining middle ∧ cost (remaining + 1) = count + cost remaining ∧
          reads (remaining + 1) initial = accesses ++ reads remaining middle)
    (remaining : Nat) (initial : State) (valid : invariant remaining initial) :
    AllExecutions transition initial (fun result => post result.state ∧
      result.instructions = cost remaining ∧ result.reads = reads remaining initial) := by
  intro choices
  exact loop_executes transition invariant post cost reads finish iterate remaining choices initial valid

end Engine
end EDSL.X86.Sequential
