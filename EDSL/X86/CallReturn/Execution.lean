/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.CallReturn.Facts
import EDSL.X86.Sequential.ExecutionTrace

namespace EDSL.X86.CallReturn

abbrev Choices := Sequential.Choices
abbrev Result := Sequential.Result

/-- The boundary is a stack slot, not a code range or a ghost target. The
pre-instruction RSP selects whether an actual RET is terminal. -/
def atBoundary (originalSlot : Word) (before : State) (observation : Observation) : Observation :=
  match observation.result with
  | .returned after => if before.registers .rsp = originalSlot then observation
    else ⟨.next after, observation.reads⟩
  | _ => observation

def boundaryStep (originalSlot : Word) (af : Bool) (before : State) : Except Error Observation :=
  (rawStep af before).map (atBoundary originalSlot before)

/-- Explicit boundary APIs compose without ever resetting the original slot. -/
abbrev runFrom (originalSlot : Word) := Sequential.Engine.run (boundaryStep originalSlot)
abbrev ExecutesFrom (originalSlot : Word) := Sequential.Engine.Executes (boundaryStep originalSlot)
abbrev BlockFrom (originalSlot : Word) := Sequential.Engine.Block (boundaryStep originalSlot)

/-- Capture the initial RSP exactly once, outside the recursive engine. -/
def run (choices : Choices) (fuel : Nat) (initial : State) : Except Error Result :=
  runFrom (initial.registers .rsp) choices fuel initial

def Executes (choices : Choices) (initial : State) (result : Result) : Prop :=
  ExecutesFrom (initial.registers .rsp) choices initial result

@[simp] theorem atBoundary_reads (originalSlot : Word) (before : State) (observation : Observation) :
    (atBoundary originalSlot before observation).reads = observation.reads := by
  rcases observation with ⟨result, reads⟩
  cases result <;> simp [atBoundary] <;> split <;> rfl

/-- Extract a CPU when the underlying observation carries one. Relabeling does
not change this projection; syscalls retain their existing separate request. -/
def cpu : StepResult → Option State
  | .next after | .returned after | .atomic _ after => some after
  | .syscall _ => none

theorem atBoundary_cpu (originalSlot : Word) (before : State) (observation : Observation) :
    cpu (atBoundary originalSlot before observation).result = cpu observation.result := by
  rcases observation with ⟨result, reads⟩
  cases result <;> simp [atBoundary] <;> split <;> rfl

theorem boundaryStep_success_iff {originalSlot : Word} {af : Bool} {before : State} {observation : Observation} :
    boundaryStep originalSlot af before = .ok observation ↔
    ∃ raw, rawStep af before = .ok raw ∧ observation = atBoundary originalSlot before raw := by
  cases actual : rawStep af before <;> simp [boundaryStep, actual, Except.map, eq_comm]

theorem boundaryStep_error_iff {originalSlot : Word} {af : Bool} {before : State} {fault : Error} :
    boundaryStep originalSlot af before = .error fault ↔ rawStep af before = .error fault := by
  cases actual : rawStep af before <;> simp [boundaryStep, actual, Except.map]

theorem boundaryStep_returned_iff {originalSlot : Word} {af : Bool} {before after : State} {reads : List Read} :
    boundaryStep originalSlot af before = .ok ⟨.returned after, reads⟩ ↔
    before.registers .rsp = originalSlot ∧ rawStep af before = .ok ⟨.returned after, reads⟩ := by
  cases actual : rawStep af before with
  | error fault => simp [boundaryStep, actual, Except.map]
  | ok observation =>
    rcases observation with ⟨result, observed⟩
    cases result <;> by_cases equal : before.registers .rsp = originalSlot <;>
      simp [boundaryStep, actual, Except.map, atBoundary, equal, Sequential.Observation.mk.injEq]

theorem boundaryStep_internal_ret {originalSlot : Word} {af : Bool} {before after : State} {reads : List Read}
    (internal : before.registers .rsp ≠ originalSlot)
    (actual : rawStep af before = .ok ⟨.returned after, reads⟩) :
    boundaryStep originalSlot af before = .ok ⟨.next after, reads⟩ := by
  simp [boundaryStep, actual, Except.map, atBoundary, internal]

theorem boundaryStep_nonreturn {originalSlot : Word} {af : Bool} {before : State} {observation : Observation}
    (actual : rawStep af before = .ok observation)
    (continues : ∀ after, observation.result ≠ .returned after) :
    boundaryStep originalSlot af before = .ok observation := by
  rcases observation with ⟨result, reads⟩
  cases result with
  | returned after => exact False.elim (continues after rfl)
  | next after | atomic event after | syscall request => simp [boundaryStep, actual, Except.map, atBoundary]

/-- Decoded non-RET instructions and raw errors pass through unchanged. -/
theorem boundaryStep_nonret {originalSlot : Word} {af : Bool} {before : State}
    (notRet : decodeAt before ≠ .ok (.sequential (.legacy .ret))) :
    boundaryStep originalSlot af before = rawStep af before := by
  cases actual : rawStep af before with
  | error fault => simp [boundaryStep, actual, Except.map]
  | ok observation =>
    apply boundaryStep_nonreturn actual
    intro after returned
    have actualReturn : rawStep af before = .ok ⟨.returned after, observation.reads⟩ := by
      rw [actual]
      cases observation
      simp_all
    exact notRet (rawStep_returned_iff.mp actualReturn).1

/-- A terminal observation is exactly an actual decoded, RAM-driven RET at the
original slot, with no assumption about code-window membership of its target. -/
theorem boundaryStep_terminal_iff {originalSlot : Word} {af : Bool} {before after : State} {reads : List Read} :
    boundaryStep originalSlot af before = .ok ⟨.returned after, reads⟩ ↔
    before.registers .rsp = originalSlot ∧
    decodeAt before = .ok (.sequential (.legacy .ret)) ∧
    ∃ target, readWord before.memory (before.registers .rsp) = .ok target ∧ canonical target = true ∧
      after = { before.writeRegister .rsp (before.registers .rsp + 8) with rip := target } ∧
      reads = [⟨.stack, before.registers .rsp, 8⟩] := by
  rw [boundaryStep_returned_iff, rawStep_returned_iff, execute_ret_success_iff]

theorem boundaryStep_projection {originalSlot : Word} {af : Bool} {before : State} {observation : Observation}
    (actual : boundaryStep originalSlot af before = .ok observation) :
    ∃ raw, rawStep af before = .ok raw ∧ observation.reads = raw.reads ∧
      cpu observation.result = cpu raw.result := by
  obtain ⟨raw, executed, same⟩ := boundaryStep_success_iff.mp actual
  subst observation
  exact ⟨raw, executed, atBoundary_reads _ _ _, atBoundary_cpu _ _ _⟩

theorem boundaryStep_read_origin {originalSlot : Word} {af : Bool} {before : State} {observation : Observation}
    (actual : boundaryStep originalSlot af before = .ok observation) :
    ∃ instruction raw, decodeAt before = .ok instruction ∧ execute before instruction af = .ok raw ∧
      observation = atBoundary originalSlot before raw ∧
      observation.reads = instruction.operandReads before ∧
      ∀ read, read ∈ observation.reads → Sequential.OperandReadSucceeds before read := by
  obtain ⟨raw, executed, same⟩ := boundaryStep_success_iff.mp actual
  obtain ⟨instruction, decoded, ran, reads, valid⟩ := rawStep_read_origin executed
  subst observation
  exact ⟨instruction, raw, decoded, ran, rfl, (atBoundary_reads _ _ _).trans reads,
    by simpa only [atBoundary_reads] using valid⟩

theorem runFrom_sound {originalSlot : Word} {choices : Choices} {fuel : Nat} {initial : State} {result : Result}
    (actual : runFrom originalSlot choices fuel initial = .ok result) :
    ExecutesFrom originalSlot choices initial result := Sequential.Engine.run_sound _ actual

theorem runFrom_complete {originalSlot : Word} {choices : Choices} {fuel : Nat} {initial : State} {result : Result}
    (actual : ExecutesFrom originalSlot choices initial result) (enough : result.instructions ≤ fuel) :
    runFrom originalSlot choices fuel initial = .ok result := Sequential.Engine.run_complete _ actual enough

theorem run_sound {choices : Choices} {fuel : Nat} {initial : State} {result : Result}
    (actual : run choices fuel initial = .ok result) : Executes choices initial result :=
  runFrom_sound actual

theorem run_complete {choices : Choices} {fuel : Nat} {initial : State} {result : Result}
    (actual : Executes choices initial result) (enough : result.instructions ≤ fuel) :
    run choices fuel initial = .ok result := runFrom_complete actual enough

theorem ExecutesFrom.fixed_choices_unique {originalSlot : Word} {choices : Choices} {initial : State}
    {left right : Result} (first : ExecutesFrom originalSlot choices initial left)
    (second : ExecutesFrom originalSlot choices initial right) : left = right :=
  Sequential.Engine.Executes.fixed_choices_unique _ first second

theorem ExecutesFrom.positive {originalSlot : Word} {choices : Choices} {initial : State} {result : Result}
    (actual : ExecutesFrom originalSlot choices initial result) : 0 < result.instructions :=
  Sequential.Engine.Executes.positive _ actual

theorem BlockFrom.append {originalSlot : Word} {choices : Choices} {initial middle final : State}
    {left right : Nat} {leftReads rightReads : List Read}
    (first : BlockFrom originalSlot choices initial middle left leftReads)
    (second : BlockFrom originalSlot (choices.drop left) middle final right rightReads) :
    BlockFrom originalSlot choices initial final (left + right) (leftReads ++ rightReads) :=
  Sequential.Engine.Block.append _ first second

theorem BlockFrom.then_executes {originalSlot : Word} {choices : Choices} {initial middle : State}
    {count : Nat} {reads : List Read} {result : Result}
    (block : BlockFrom originalSlot choices initial middle count reads)
    (tail : ExecutesFrom originalSlot (choices.drop count) middle result) :
    ExecutesFrom originalSlot choices initial (result.prepend count reads) :=
  Sequential.Engine.Block.then_executes _ block tail

/-- Each accumulated read has an actual decoded/executed instruction origin,
with its exact pre-state and stream index, using the concrete machine. -/
theorem ExecutesFrom.read_origin {originalSlot : Word} {choices : Choices} {initial : State} {result : Result}
    (actual : ExecutesFrom originalSlot choices initial result) {read : Read} (member : read ∈ result.reads) :
    ∃ count before priorReads instruction raw, count < result.instructions ∧
      BlockFrom originalSlot choices initial before count priorReads ∧
      decodeAt before = .ok instruction ∧ execute before instruction (choices count) = .ok raw ∧
      read ∈ instruction.operandReads before ∧ Sequential.OperandReadSucceeds before read := by
  obtain ⟨count, before, prior, observation, bound, preceding, step, present⟩ :=
    Sequential.Engine.Executes.read_origin _ actual member
  obtain ⟨instruction, raw, decoded, executed, _, reads, valid⟩ := boundaryStep_read_origin step
  exact ⟨count, before, prior, instruction, raw, bound, preceding, decoded, executed,
    by simpa only [reads] using present, valid read present⟩

end EDSL.X86.CallReturn

namespace EDSL.X86.CallReturn

/-- A finite returning execution ends at a concrete actual RET at the frozen
original slot, after an exact continuing preceding. No balanced-call invariant is
assumed or inferred. -/
theorem ExecutesFrom.terminal_origin {originalSlot : Word} {choices : Choices} {initial : State}
    {result : Result} (actual : ExecutesFrom originalSlot choices initial result) :
    ∃ count before priorReads lastReads, count + 1 = result.instructions ∧
      BlockFrom originalSlot choices initial before count priorReads ∧
      before.registers .rsp = originalSlot ∧
      rawStep (choices count) before = .ok ⟨.returned result.state, lastReads⟩ ∧
      result.reads = priorReads ++ lastReads := by
  induction actual with
  | @ret choices initial final reads step =>
    obtain ⟨slot, raw⟩ := boundaryStep_returned_iff.mp step
    exact ⟨0, initial, [], reads, rfl, .nil, slot, raw, rfl⟩
  | @next choices initial middle result reads step tail ih =>
    obtain ⟨count, before, prior, last, cost, preceding, slot, raw, trace⟩ := ih
    exact ⟨count + 1, before, reads ++ prior, last,
      by simp only [Sequential.Result.prepend]; omega,
      .next step preceding, slot, by simpa [Sequential.ChoiceStream.drop, Sequential.Result.prepend, Nat.add_comm] using raw,
      by simp [Sequential.Result.prepend, trace, List.append_assoc]⟩
  | @atomic choices initial middle result reads event step tail ih =>
    obtain ⟨count, before, prior, last, cost, preceding, slot, raw, trace⟩ := ih
    exact ⟨count + 1, before, reads ++ prior, last,
      by simp only [Sequential.Result.prepend]; omega,
      .atomic step preceding, slot, by simpa [Sequential.ChoiceStream.drop, Sequential.Result.prepend, Nat.add_comm] using raw,
      by simp [Sequential.Result.prepend, trace, List.append_assoc]⟩

/-- The explicit boundary stays fixed through a continuing preceding. -/
theorem BlockFrom.run_append {originalSlot : Word} {choices : Choices} {initial middle : State}
    {count fuel : Nat} {reads : List Read} {result : Result}
    (preceding : BlockFrom originalSlot choices initial middle count reads)
    (tail : runFrom originalSlot (choices.drop count) fuel middle = .ok result) :
    runFrom originalSlot choices (count + fuel) initial = .ok (result.prepend count reads) :=
  Sequential.Engine.Block.run_append _ preceding tail

end EDSL.X86.CallReturn
