/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine
import EDSL.X86.Sequential.ExecutionTrace
import EDSL.X86.Execution

namespace EDSL.X86.Sequential

/-- Evaluate the currently decoded actual bytes with a fresh AF choice per
retired instruction. Operand reads exclude instruction fetches. -/
abbrev run := Engine.run step

abbrev Step := Engine.Step step
abbrev ChosenStep := Engine.ChosenStep step
abbrev Executes := Engine.Executes step
abbrev Block := Engine.Block step
abbrev Continues := Engine.Continues step
abbrev DivergesWith := Engine.DivergesWith step
abbrev Diverges := Engine.Diverges step
abbrev NondetExecutes := Engine.NondetExecutes step
abbrev AllExecutions := Engine.AllExecutions step
abbrev Ranked := Engine.Ranked step
abbrev Reachable := Engine.Reachable step
abbrev Safe := Engine.Safe step
abbrev FaultAt := Engine.FaultAt step
abbrev FaultTrace := Engine.FaultTrace step

theorem run_zero (choices : Choices) (state : State) :
    run choices 0 state = .error .exhaustedFuel :=
  @Engine.run_zero Bool EDSL.X86.Sequential.step choices state
theorem run_return {choices : Choices} {fuel : Nat} {initial final : State} {reads : List Read}
    (step : step (choices 0) initial = .ok ⟨.returned final, reads⟩) :
    run choices (fuel + 1) initial = .ok ⟨final, 1, reads⟩ :=
  @Engine.run_return Bool EDSL.X86.Sequential.step choices fuel initial final reads step
theorem run_next {choices : Choices} {fuel : Nat} {initial middle : State} {reads : List Read}
    (step : step (choices 0) initial = .ok ⟨.next middle, reads⟩) :
    run choices (fuel + 1) initial =
      (run (choices.drop 1) fuel middle).map (Result.prepend 1 reads) :=
  @Engine.run_next Bool EDSL.X86.Sequential.step choices fuel initial middle reads step
theorem run_atomic {choices : Choices} {fuel : Nat} {initial middle : State}
    {event : AtomicEvent} {reads : List Read}
    (step : step (choices 0) initial = .ok ⟨.atomic event middle, reads⟩) :
    run choices (fuel + 1) initial =
      (run (choices.drop 1) fuel middle).map (Result.prepend 1 reads) :=
  @Engine.run_atomic Bool EDSL.X86.Sequential.step choices fuel initial middle event reads step
theorem run_fault {choices : Choices} {fuel : Nat} {initial : State} {error : Error}
    (step : step (choices 0) initial = .error error) :
    run choices (fuel + 1) initial = .error error :=
  @Engine.run_fault Bool EDSL.X86.Sequential.step choices fuel initial error step
theorem run_syscall {choices : Choices} {fuel : Nat} {initial : State}
    {request : SyscallRequest} {reads : List Read}
    (step : step (choices 0) initial = .ok ⟨.syscall request, reads⟩) :
    run choices (fuel + 1) initial = .error .syscallBoundary :=
  @Engine.run_syscall Bool EDSL.X86.Sequential.step choices fuel initial request reads step
theorem run_sound {choices : Choices} {fuel : Nat} {initial : State} {result : Result}
    (success : run choices fuel initial = .ok result) :
    Executes choices initial result :=
  @Engine.run_sound Bool EDSL.X86.Sequential.step choices fuel initial result success
theorem run_complete {choices : Choices} {initial : State} {result : Result} {fuel : Nat}
    (execution : Executes choices initial result) (enough : result.instructions ≤ fuel) :
    run choices fuel initial = .ok result :=
  @Engine.run_complete Bool EDSL.X86.Sequential.step choices initial result fuel execution enough
theorem run_complete_prefix {choices other : Choices} {initial : State} {result : Result} {fuel : Nat}
    (execution : Executes choices initial result)
    (agree : choices.Agree other result.instructions) (enough : result.instructions ≤ fuel) :
    run other fuel initial = .ok result :=
  @Engine.run_complete_prefix Bool EDSL.X86.Sequential.step choices other initial result fuel execution agree enough

namespace Executes
theorem ret {choices : Choices} {initial final : State} {reads : List Read}
    (chosen : step (choices 0) initial = .ok ⟨.returned final, reads⟩) :
    Executes choices initial ⟨final, 1, reads⟩ := Engine.Executes.ret chosen

theorem next {choices : Choices} {initial middle : State} {result : Result} {reads : List Read}
    (chosen : step (choices 0) initial = .ok ⟨.next middle, reads⟩)
    (tail : Executes (choices.drop 1) middle result) :
    Executes choices initial (result.prepend 1 reads) := Engine.Executes.next chosen tail

theorem atomic {choices : Choices} {initial middle : State} {result : Result}
    {reads : List Read} {event : AtomicEvent}
    (chosen : step (choices 0) initial = .ok ⟨.atomic event middle, reads⟩)
    (tail : Executes (choices.drop 1) middle result) :
    Executes choices initial (result.prepend 1 reads) := Engine.Executes.atomic chosen tail

theorem positive {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) :
    0 < result.instructions :=
  @Engine.Executes.positive Bool EDSL.X86.Sequential.step choices initial result execution
theorem exhausted {choices : Choices} {initial : State} {result : Result} {fuel : Nat}
    (execution : Executes choices initial result) (short : fuel < result.instructions) :
    run choices fuel initial = .error .exhaustedFuel :=
  @Engine.Executes.exhausted Bool EDSL.X86.Sequential.step choices initial result fuel execution short
theorem run_eq {choices : Choices} {initial : State} {result : Result} (fuel : Nat)
    (execution : Executes choices initial result) :
    run choices fuel initial =
      if result.instructions ≤ fuel then .ok result else .error .exhaustedFuel :=
  @Engine.Executes.run_eq Bool EDSL.X86.Sequential.step choices initial result fuel execution
theorem no_fault_prefix {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) {fuel : Nat} {error : Error}
    (fault : run choices fuel initial = .error error) :
    error = .exhaustedFuel :=
  @Engine.Executes.no_fault_prefix Bool EDSL.X86.Sequential.step choices initial result execution fuel error fault
theorem fixed_choices_unique {choices : Choices} {initial : State} {left right : Result}
    (first : Executes choices initial left)
    (second : Executes choices initial right) :
    left = right :=
  @Engine.Executes.fixed_choices_unique Bool EDSL.X86.Sequential.step choices initial left right first second
theorem restrict_choices {choices other : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result)
    (agree : choices.Agree other result.instructions) :
    Executes other initial result :=
  @Engine.Executes.restrict_choices Bool EDSL.X86.Sequential.step choices other initial result execution agree
theorem no_divergence_with {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) :
    ¬ DivergesWith choices initial :=
  @Engine.Executes.no_divergence_with Bool EDSL.X86.Sequential.step choices initial result execution
end Executes

namespace Block
theorem nil {choices : Choices} {state : State} : Block choices state state 0 [] := Engine.Block.nil

theorem next {choices : Choices} {initial middle final : State} {count : Nat} {reads rest : List Read}
    (chosen : step (choices 0) initial = .ok ⟨.next middle, reads⟩)
    (tail : Block (choices.drop 1) middle final count rest) :
    Block choices initial final (count + 1) (reads ++ rest) := Engine.Block.next chosen tail

theorem atomic {choices : Choices} {initial middle final : State} {count : Nat}
    {reads rest : List Read} {event : AtomicEvent}
    (chosen : step (choices 0) initial = .ok ⟨.atomic event middle, reads⟩)
    (tail : Block (choices.drop 1) middle final count rest) :
    Block choices initial final (count + 1) (reads ++ rest) := Engine.Block.atomic chosen tail

theorem append {choices : Choices} {initial middle final : State} {left right : Nat}
    {leftReads rightReads : List Read}
    (first : Block choices initial middle left leftReads)
    (second : Block (choices.drop left) middle final right rightReads) :
    Block choices initial final (left + right) (leftReads ++ rightReads) :=
  @Engine.Block.append Bool EDSL.X86.Sequential.step choices initial middle final left right leftReads rightReads first second
theorem then_executes {choices : Choices} {initial middle : State} {count : Nat}
    {reads : List Read} {result : Result}
    (block : Block choices initial middle count reads)
    (tail : Executes (choices.drop count) middle result) :
    Executes choices initial (result.prepend count reads) :=
  @Engine.Block.then_executes Bool EDSL.X86.Sequential.step choices initial middle count reads result block tail
theorem run_append {choices : Choices} {initial middle : State} {count fuel : Nat}
    {reads : List Read} {result : Result}
    (block : Block choices initial middle count reads)
    (tail : run (choices.drop count) fuel middle = .ok result) :
    run choices (count + fuel) initial = .ok (result.prepend count reads) :=
  @Engine.Block.run_append Bool EDSL.X86.Sequential.step choices initial middle count fuel reads result block tail
theorem restrict_choices {choices other : Choices} {initial final : State} {count : Nat}
    {reads : List Read} (block : Block choices initial final count reads)
    (agree : choices.Agree other count) :
    Block other initial final count reads :=
  @Engine.Block.restrict_choices Bool EDSL.X86.Sequential.step choices other initial final count reads block agree
end Block

namespace AllExecutions
theorem project {initial : State} {contract : Result → Prop}
    (correct : AllExecutions initial contract) {result : Result}
    (execution : NondetExecutes initial result) :
    contract result :=
  @Engine.AllExecutions.project Bool EDSL.X86.Sequential.step initial contract correct result execution
theorem no_fault_prefix {initial : State} {contract : Result → Prop}
    (correct : AllExecutions initial contract) (choices : Choices)
    {fuel : Nat} {error : Error} (fault : run choices fuel initial = .error error) :
    error = .exhaustedFuel :=
  @Engine.AllExecutions.no_fault_prefix Bool EDSL.X86.Sequential.step initial contract correct choices fuel error fault
theorem no_divergence {initial : State} {contract : Result → Prop}
    (correct : AllExecutions initial contract) :
    ¬ Diverges initial :=
  @Engine.AllExecutions.no_divergence Bool EDSL.X86.Sequential.step initial contract correct
theorem run {initial : State} {contract : Result → Prop} {cost : Nat}
    (correct : AllExecutions initial contract)
    (exactCost : ∀ result, contract result → result.instructions = cost) (choices : Choices) :
    ∃ result, run choices cost initial = .ok result ∧ contract result :=
  @Engine.AllExecutions.run Bool EDSL.X86.Sequential.step initial contract cost correct exactCost choices
end AllExecutions

namespace Ranked
theorem execution {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked invariant rank post) {initial : State} (valid : invariant initial)
    (choices : Choices) :
    ∃ result, Executes choices initial result ∧
      post result.state ∧ result.instructions ≤ rank initial + 1 :=
  @Engine.Ranked.execution Bool EDSL.X86.Sequential.step invariant rank post progress initial valid choices
theorem total {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked invariant rank post) {initial : State} (valid : invariant initial)
    (choices : Choices) :
    ∃ result,
      run choices (rank initial + 1) initial = .ok result ∧ post result.state :=
  @Engine.Ranked.total Bool EDSL.X86.Sequential.step invariant rank post progress initial valid choices
theorem all_executions {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked invariant rank post) {initial : State} (valid : invariant initial) :
    AllExecutions initial (fun result => post result.state ∧ result.instructions ≤ rank initial + 1) :=
  @Engine.Ranked.all_executions Bool EDSL.X86.Sequential.step invariant rank post progress initial valid
theorem continues {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked invariant rank post) {initial final : State}
    (valid : invariant initial) {af : Bool} {outcome : StepResult} {reads : List Read}
    (step : step af initial = .ok ⟨outcome, reads⟩) (next : nextState outcome = some final) :
    invariant final ∧ rank final < rank initial :=
  @Engine.Ranked.continues Bool EDSL.X86.Sequential.step invariant rank post progress initial final valid af outcome reads step next
theorem block_invariant {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked invariant rank post) {initial final : State}
    (valid : invariant initial) {choices : Choices} {count : Nat} {reads : List Read}
    (block : Block choices initial final count reads) :
    invariant final ∧ rank final + count ≤ rank initial :=
  @Engine.Ranked.block_invariant Bool EDSL.X86.Sequential.step invariant rank post progress initial final valid choices count reads block
theorem safe {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked invariant rank post) {initial : State} (valid : invariant initial) :
    Safe initial :=
  @Engine.Ranked.safe Bool EDSL.X86.Sequential.step invariant rank post progress initial valid
theorem no_fault_prefix {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked invariant rank post) {initial : State} (valid : invariant initial)
    (choices : Choices) {fuel : Nat} {error : Error}
    (fault : run choices fuel initial = .error error) :
    error = .exhaustedFuel :=
  @Engine.Ranked.no_fault_prefix Bool EDSL.X86.Sequential.step invariant rank post progress initial valid choices fuel error fault
theorem no_divergence {invariant : State → Prop} {rank : State → Nat} {post : State → Prop}
    (progress : Ranked invariant rank post) {initial : State} (valid : invariant initial) :
    ¬ Diverges initial :=
  @Engine.Ranked.no_divergence Bool EDSL.X86.Sequential.step invariant rank post progress initial valid
end Ranked

theorem loop_executes (invariant : Nat → State → Prop) (post : State → Prop)
    (cost : Nat → Nat) (reads : Nat → State → List Read)
    (finish : ∀ choices initial, invariant 0 initial → ∃ result,
      Executes choices initial result ∧ post result.state ∧
        result.instructions = cost 0 ∧ result.reads = reads 0 initial)
    (iterate : ∀ remaining choices initial, invariant (remaining + 1) initial →
      ∃ middle count accesses, Block choices initial middle count accesses ∧
        invariant remaining middle ∧ cost (remaining + 1) = count + cost remaining ∧
          reads (remaining + 1) initial = accesses ++ reads remaining middle)
    (remaining : Nat) (choices : Choices) (initial : State) (valid : invariant remaining initial) :
    ∃ result, Executes choices initial result ∧ post result.state ∧
      result.instructions = cost remaining ∧ result.reads = reads remaining initial :=
  @Engine.loop_executes Bool EDSL.X86.Sequential.step invariant post cost reads finish iterate remaining choices initial valid
theorem loop_total (invariant : Nat → State → Prop) (post : State → Prop)
    (cost : Nat → Nat) (reads : Nat → State → List Read)
    (finish : ∀ choices initial, invariant 0 initial → ∃ result,
      Executes choices initial result ∧ post result.state ∧
        result.instructions = cost 0 ∧ result.reads = reads 0 initial)
    (iterate : ∀ remaining choices initial, invariant (remaining + 1) initial →
      ∃ middle count accesses, Block choices initial middle count accesses ∧
        invariant remaining middle ∧ cost (remaining + 1) = count + cost remaining ∧
          reads (remaining + 1) initial = accesses ++ reads remaining middle)
    (remaining : Nat) (choices : Choices) (initial : State) (valid : invariant remaining initial) :
    ∃ result, run choices (cost remaining) initial = .ok result ∧ post result.state ∧
      result.instructions = cost remaining ∧ result.reads = reads remaining initial :=
  @Engine.loop_total Bool EDSL.X86.Sequential.step invariant post cost reads finish iterate remaining choices initial valid
theorem loop_all_executions (invariant : Nat → State → Prop) (post : State → Prop)
    (cost : Nat → Nat) (reads : Nat → State → List Read)
    (finish : ∀ choices initial, invariant 0 initial → ∃ result,
      Executes choices initial result ∧ post result.state ∧
        result.instructions = cost 0 ∧ result.reads = reads 0 initial)
    (iterate : ∀ remaining choices initial, invariant (remaining + 1) initial →
      ∃ middle count accesses, Block choices initial middle count accesses ∧
        invariant remaining middle ∧ cost (remaining + 1) = count + cost remaining ∧
          reads (remaining + 1) initial = accesses ++ reads remaining middle)
    (remaining : Nat) (initial : State) (valid : invariant remaining initial) :
    AllExecutions initial (fun result => post result.state ∧
      result.instructions = cost remaining ∧ result.reads = reads remaining initial) :=
  @Engine.loop_all_executions Bool EDSL.X86.Sequential.step invariant post cost reads finish iterate remaining initial valid

theorem run_choices_congr {left right : Choices} {fuel : Nat} {initial : State}
    (agree : left.Agree right fuel) : run left fuel initial = run right fuel initial :=
  Engine.run_choices_congr step agree

theorem run_instructions_le {choices : Choices} {fuel : Nat} {initial : State} {result : Result}
    (success : run choices fuel initial = .ok result) : result.instructions ≤ fuel :=
  Engine.run_instructions_le step success

theorem run_error_sound {choices : Choices} {fuel : Nat} {initial : State} {error : Error}
    (fault : run choices fuel initial = .error error) :
    error = .exhaustedFuel ∨ ∃ count reads, count < fuel ∧ FaultTrace choices initial error count reads :=
  Engine.run_error_sound step fault

theorem FaultTrace.run {choices : Choices} {initial : State} {error : Error} {count fuel : Nat}
    {reads : List Read} (trace : FaultTrace choices initial error count reads)
    (enough : count < fuel) : run choices fuel initial = .error error :=
  Engine.FaultTrace.run step trace enough

theorem Block.run_error_append {choices : Choices} {initial middle : State} {count fuel : Nat}
    {reads : List Read} {error : Error} (block : Block choices initial middle count reads)
    (tail : run (choices.drop count) fuel middle = .error error) :
    run choices (count + fuel) initial = .error error :=
  Engine.Block.run_error_append step block tail

theorem AllExecutions.no_fault_trace {initial : State} {contract : Result → Prop}
    (correct : AllExecutions initial contract) {choices : Choices} {error : Error}
    {count : Nat} {reads : List Read} : ¬ FaultTrace choices initial error count reads :=
  Engine.AllExecutions.no_fault_trace step correct

theorem AllExecutions.safe {initial : State} {contract : Result → Prop}
    (correct : AllExecutions initial contract) : Safe initial :=
  Engine.AllExecutions.safe step correct

/-- Reported operand reads have succeeded in the actual pre-instruction memory.
The decoder's instruction-fetch accesses never enter this list. -/
theorem observed_reads_succeed {af : Bool} {initial : State} {observation : Observation}
    (success : step af initial = .ok observation) :
    ∀ read ∈ observation.reads, OperandReadSucceeds initial read := by
  cases decoded : decodeAt initial with
  | error fault => simp [step, decoded] at success
  | ok instruction =>
    rw [step_eq_execute af decoded] at success
    exact execute_reads_succeed success

theorem Executes.read_origin {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) {read : Read} (member : read ∈ result.reads) :
    ∃ count before priorReads observation, count < result.instructions ∧
      Block choices initial before count priorReads ∧ step (choices count) before = .ok observation ∧
        read ∈ observation.reads :=
  Engine.Executes.read_origin step execution member

theorem Block.read_origin {choices : Choices} {initial final : State} {count : Nat} {reads : List Read}
    (execution : Block choices initial final count reads) {read : Read} (member : read ∈ reads) :
    ∃ index before priorReads observation, index < count ∧
      Block choices initial before index priorReads ∧ step (choices index) before = .ok observation ∧
        read ∈ observation.reads :=
  Engine.Block.read_origin step execution member

theorem Executes.reads_succeed {choices : Choices} {initial : State} {result : Result}
    (execution : Executes choices initial result) {read : Read} (member : read ∈ result.reads) :
    ∃ before, Reachable initial before ∧ OperandReadSucceeds before read := by
  obtain ⟨count, before, priorReads, observation, _, block, actual, present⟩ :=
    execution.read_origin member
  exact ⟨before, ⟨choices, count, priorReads, block⟩, observed_reads_succeed actual read present⟩

theorem run_reads_succeed {choices : Choices} {fuel : Nat} {initial : State} {result : Result}
    (success : run choices fuel initial = .ok result) {read : Read} (member : read ∈ result.reads) :
    ∃ before, Reachable initial before ∧ OperandReadSucceeds before read :=
  (run_sound success).reads_succeed member

/-- Successful steps of the legacy decoder embed for every choice. A legacy
decoder rejection need not embed: the new decoder deliberately accepts more
instructions. -/
theorem legacy_step_observation {initial : State} {outcome : StepResult}
    (success : X86.step initial = .ok outcome) :
    ∃ reads, ∀ af, step af initial = .ok ⟨outcome, reads⟩ := by
  cases decoded : X86.decodeAt initial with
  | error fault => simp [X86.step, decoded] at success
  | ok instruction =>
    rw [X86.step_eq_executeInstruction initial instruction decoded] at success
    refine ⟨(Instruction.legacy instruction).operandReads initial, ?_⟩
    intro af
    rw [step_eq_execute af (decodeAt_legacy decoded), execute_legacy, success]
    rfl

/-- The complete legacy state and instruction cost are preserved, and operand
reads are now exposed. The same read trace works for all choice streams. -/
theorem legacy_executes {initial final : State} {count : Nat}
    (execution : X86.Executes initial final count) :
    ∃ reads, ∀ choices, Executes choices initial ⟨final, count, reads⟩ := by
  induction execution with
  | ret transition =>
    obtain ⟨reads, actual⟩ := legacy_step_observation transition
    exact ⟨reads, fun choices => .ret (actual (choices 0))⟩
  | @next initial middle final count transition tail induction =>
    obtain ⟨reads, actual⟩ := legacy_step_observation transition
    obtain ⟨rest, executes⟩ := induction
    refine ⟨reads ++ rest, ?_⟩
    intro choices
    simpa [Result.prepend, Nat.add_comm] using
      Engine.Executes.next (actual (choices 0)) (executes (choices.drop 1))
  | @atomic initial middle final count event transition tail induction =>
    obtain ⟨reads, actual⟩ := legacy_step_observation transition
    obtain ⟨rest, executes⟩ := induction
    refine ⟨reads ++ rest, ?_⟩
    intro choices
    simpa [Result.prepend, Nat.add_comm] using
      Engine.Executes.atomic (actual (choices 0)) (executes (choices.drop 1))

private theorem legacy_run_cost {fuel : Nat} {initial : State} {result : X86.Execution}
    (success : X86.run fuel initial = .ok result) : result.instructions ≤ fuel := by
  induction fuel generalizing initial result with
  | zero => simp [X86.run] at success
  | succ fuel induction =>
    cases transition : X86.step initial with
    | error fault => simp [X86.run, transition] at success
    | ok outcome =>
      cases outcome with
      | returned final =>
        simp [X86.run, transition] at success
        cases success
        simp
      | syscall request => simp [X86.run, transition] at success
      | next middle | atomic event middle =>
        cases tail : X86.run fuel middle with
        | error fault => simp [X86.run, transition, tail] at success
        | ok rest =>
          simp [X86.run, transition, tail] at success
          cases success
          have bound := induction tail
          simpa using Nat.add_le_add_right bound 1

theorem legacy_run {fuel : Nat} {initial : State} {result : X86.Execution}
    (success : X86.run fuel initial = .ok result) :
    ∃ reads, ∀ choices, run choices fuel initial = .ok ⟨result.state, result.instructions, reads⟩ := by
  obtain ⟨reads, execution⟩ := legacy_executes (X86.run_sound success)
  exact ⟨reads, fun choices => run_complete (execution choices) (legacy_run_cost success)⟩

end EDSL.X86.Sequential
