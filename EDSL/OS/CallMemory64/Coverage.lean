/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallMemory64.CPU
import EDSL.CallStack.Coverage

set_option warningAsError true

namespace EDSL.OS.CallMemory64
open X86

/-- Recover a machine RAM frame outside the UNION of the private stack and
the target word from the same coupled endpoints and mixed checked history.
The old private-only memory frame does not apply to external DATA stores. -/
theorem memory_frame {descriptor : Descriptor} {before after : Shared} {initial final : State}
    (first : Current descriptor before initial) (last : Current descriptor after final)
    (preserved : Preservation descriptor before after) :
    (∀ query, ¬descriptor.frame.region.Contains query →
      ¬(AddressSpace.qwordRegion descriptor.target).Contains query →
      final.memory.read query = initial.memory.read query) ∧
      final.memory.executable = initial.memory.executable ∧
      final.memory.writable = initial.memory.writable := by
  rw [first.coupled, last.coupled]
  refine ⟨?_, ?_, ?_⟩
  · intro query stack data
    simp only [AddressSpace.toMemory, preserved.outside query stack data]
  · funext query
    have same := preserved.permissions query
    cases a : after.resources.space.cells query <;>
      cases b : before.resources.space.cells query <;>
      simp_all [AddressSpace.toMemory]
  · funext query
    have same := preserved.permissions query
    cases a : after.resources.space.cells query <;>
      cases b : before.resources.space.cells query <;>
      simp_all [AddressSpace.toMemory]

/-- Every actual instruction encoding of a continuing mixed trace lies in
the frozen whole code extent, including prefixes, SIB and immediate bytes. -/
inductive CoveredHistory (descriptor : Descriptor) : CallReturn.Choices → Shared →
    State → Shared → State → Nat → List CallReturn.Read → Prop where
  | nil {choices shared state} : CoveredHistory descriptor choices shared state shared state 0 []
  | next {choices shared evolved final before middle after count reads rest}
      (step : CPU.Step descriptor shared evolved before middle (choices 0) ⟨.next middle, reads⟩)
      (fetch : EDSL.CallStack.FetchWithin descriptor.frame before)
      (tail : CoveredHistory descriptor (choices.drop 1) evolved middle final after count rest) :
      CoveredHistory descriptor choices shared before final after (count + 1) (reads ++ rest)

theorem CoveredHistory.history {descriptor choices shared initial evolved after count reads}
    (covered : CoveredHistory descriptor choices shared initial evolved after count reads) :
    CPU.History descriptor choices shared initial evolved after count reads := by
  induction covered with
  | nil => exact .nil
  | next step _ _ ih => exact .next step ih

theorem CoveredHistory.machine {descriptor choices shared initial evolved after count reads}
    (covered : CoveredHistory descriptor choices shared initial evolved after count reads) :
    CallReturn.BlockFrom descriptor.frame.top choices initial after count reads := covered.history.machine

theorem CoveredHistory.mixedHistory {descriptor choices shared initial evolved after count reads}
    (covered : CoveredHistory descriptor choices shared initial evolved after count reads) :
    History descriptor shared evolved := covered.history.mixedHistory

theorem CoveredHistory.current {descriptor choices shared initial evolved after count reads}
    (covered : CoveredHistory descriptor choices shared initial evolved after count reads)
    (current : Current descriptor shared initial) : Current descriptor evolved after :=
  covered.history.current current

theorem CoveredHistory.preserves {descriptor choices shared initial evolved after count reads}
    (covered : CoveredHistory descriptor choices shared initial evolved after count reads) :
    Preservation descriptor shared evolved := covered.history.preserves

theorem CoveredHistory.trans {descriptor choices shared initial evolved middle count reads
    final after more rest}
    (first : CoveredHistory descriptor choices shared initial evolved middle count reads)
    (last : CoveredHistory descriptor (choices.drop count) evolved middle final after more rest) :
    CoveredHistory descriptor choices shared initial final after (count + more) (reads ++ rest) := by
  induction first with
  | nil => simpa using last
  | @next choices shared nextShared evolved initial nextCpu middle count firstReads prior
      step fetch _ ih =>
    have finish := ih (by simpa [Sequential.Choices.drop, Nat.add_comm] using last)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc] using
      CoveredHistory.next step fetch finish

/-- A sibling returning execution with complete fetch footprints and the
original caller-slot boundary. The terminal RET's encoding is covered, while
its actual caller-supplied target need not belong to the code extent. -/
inductive CoveredExecution (descriptor : Descriptor) : CallReturn.Choices → Shared →
    State → Shared → CallReturn.Result → Prop where
  | ret {choices shared evolved before after reads}
      (step : CPU.Step descriptor shared evolved before after (choices 0) ⟨.returned after, reads⟩)
      (fetch : EDSL.CallStack.FetchWithin descriptor.frame before) :
      CoveredExecution descriptor choices shared before evolved ⟨after, 1, reads⟩
  | next {choices shared evolved final before middle result reads}
      (step : CPU.Step descriptor shared evolved before middle (choices 0) ⟨.next middle, reads⟩)
      (fetch : EDSL.CallStack.FetchWithin descriptor.frame before)
      (tail : CoveredExecution descriptor (choices.drop 1) evolved middle final result) :
      CoveredExecution descriptor choices shared before final (result.prepend 1 reads)

theorem CoveredExecution.execution {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result) :
    CPU.Execution descriptor choices shared initial evolved result := by
  induction covered with
  | ret step _ => exact .ret step
  | next step _ _ ih => exact .next step ih

/-- Compose at the precise remaining choice stream, accumulating all operand
reads and instruction counts without resetting the original-slot boundary. -/
theorem CoveredHistory.then_execution
    {descriptor choices shared before evolved middle count reads final result}
    (history : CoveredHistory descriptor choices shared before evolved middle count reads)
    (tail : CoveredExecution descriptor (choices.drop count) evolved middle final result) :
    CoveredExecution descriptor choices shared before final (result.prepend count reads) := by
  induction history with
  | nil => simpa [Sequential.Result.prepend] using tail
  | @next choices shared nextShared evolved before nextCpu middle count firstReads rest step fetch _ ih =>
    have finish := ih (by simpa [Sequential.Choices.drop, Nat.add_comm] using tail)
    simpa [Sequential.Result.prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.append_assoc] using CoveredExecution.next step fetch finish

theorem CoveredExecution.machine {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result) :
    CallReturn.ExecutesFrom descriptor.frame.top choices initial result := covered.execution.machine

theorem CoveredExecution.mixedHistory {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result) :
    History descriptor shared evolved := covered.execution.mixedHistory

theorem CoveredExecution.current {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) : Current descriptor evolved result.state :=
  covered.execution.current current

theorem CoveredExecution.preserves {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result) :
    Preservation descriptor shared evolved := covered.execution.preserves

theorem CoveredExecution.memory_frame {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) :
    (∀ query, ¬descriptor.frame.region.Contains query →
      ¬(AddressSpace.qwordRegion descriptor.target).Contains query →
      result.state.memory.read query = initial.memory.read query) ∧
      result.state.memory.executable = initial.memory.executable ∧
      result.state.memory.writable = initial.memory.writable :=
  CallMemory64.memory_frame current (covered.current current) covered.preserves

/-- Concrete evaluator success follows from these actual steps, with any
sufficient fuel; no future successful run is part of the resource admission. -/
theorem CoveredExecution.run {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result) {fuel : Nat}
    (enough : result.instructions ≤ fuel) :
    CallReturn.runFrom descriptor.frame.top choices fuel initial = .ok result :=
  covered.execution.run enough

theorem CoveredExecution.fetchWithin {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result) :
    EDSL.CallStack.FetchWithin descriptor.frame initial := by
  cases covered with
  | ret _ fetch | next _ fetch _ => exact fetch

/-- Every actual pre-terminal prefix reaches a covered instruction, including
the original-slot terminal RET. Determinism identifies the prefix CPU state. -/
theorem CoveredExecution.prefix {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    {before count reads}
    (block : CallReturn.BlockFrom descriptor.frame.top choices initial before count reads)
    (bound : count < result.instructions) : EDSL.CallStack.FetchWithin descriptor.frame before := by
  induction covered generalizing before count reads with
  | ret step fetch =>
    cases block with
    | nil => exact fetch
    | next actual _ | atomic actual _ =>
      have impossible := Except.ok.inj (step.machine.symm.trans actual)
      cases impossible
  | next step fetch tail ih =>
    cases block with
    | nil => exact fetch
    | next actual rest =>
      have same := Except.ok.inj (step.machine.symm.trans actual)
      cases same
      exact ih rest (by simp only [Sequential.Result.prepend] at bound; omega)
    | atomic actual _ =>
      have impossible := Except.ok.inj (step.machine.symm.trans actual)
      cases impossible

/-- A covered mixed execution supplies an actual current OS world at every
concrete pre-terminal CPU prefix, rather than a stale-world read receipt. -/
theorem CoveredExecution.prefix_current {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) {before count reads}
    (block : CallReturn.BlockFrom descriptor.frame.top choices initial before count reads)
    (bound : count < result.instructions) :
    ∃ world, CPU.History descriptor choices shared initial world before count reads ∧
      Current descriptor world before := by
  induction covered generalizing before count reads with
  | ret step fetch =>
    cases block with
    | nil => exact ⟨_, .nil, current⟩
    | next actual _ | atomic actual _ =>
      have impossible := Except.ok.inj (step.machine.symm.trans actual)
      cases impossible
  | next step fetch tail ih =>
    cases block with
    | nil => exact ⟨_, .nil, current⟩
    | next actual rest =>
      have same := Except.ok.inj (step.machine.symm.trans actual)
      cases same
      obtain ⟨world, history, present⟩ := ih (step.current current) rest
        (by simp only [Sequential.Result.prepend] at bound; omega)
      exact ⟨world, .next step history, present⟩
    | atomic actual _ =>
      have impossible := Except.ok.inj (step.machine.symm.trans actual)
      cases impossible

/-- Strengthen an existing mixed execution by proving complete fetch coverage
at its actual CPU prefixes. This is a construction rule, not admission. -/
theorem CoveredExecution.of_execution {descriptor choices shared initial evolved result}
    (execution : CPU.Execution descriptor choices shared initial evolved result)
    (fetches : ∀ {before count reads},
      CallReturn.BlockFrom descriptor.frame.top choices initial before count reads →
      count < result.instructions → EDSL.CallStack.FetchWithin descriptor.frame before) :
    CoveredExecution descriptor choices shared initial evolved result := by
  induction execution with
  | ret step => exact .ret step (fetches .nil (by change 0 < 1; decide))
  | next step tail ih =>
    refine .next step (fetches .nil (by simp only [Sequential.Result.prepend]; omega)) (ih ?_)
    intro before count reads block bound
    exact fetches (.next step.machine block) (by simp only [Sequential.Result.prepend]; omega)

/-- Accumulated reads originate at the actual covered decoded instruction,
with its complete footprint and actual memory-primitive success. -/
theorem CoveredExecution.read_origin {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    {read : CallReturn.Read} (member : read ∈ result.reads) :
    ∃ count before priorReads instruction raw, count < result.instructions ∧
      CallReturn.BlockFrom descriptor.frame.top choices initial before count priorReads ∧
      EDSL.CallStack.FetchWithin descriptor.frame before ∧
      CallReturn.decodeAt before = .ok instruction ∧
      CallReturn.execute before instruction (choices count) = .ok raw ∧
      read ∈ instruction.operandReads before ∧ Sequential.OperandReadSucceeds before read := by
  obtain ⟨count, before, priorReads, instruction, raw, bound, block, decoded, actual,
    present, succeeds⟩ := covered.machine.read_origin member
  exact ⟨count, before, priorReads, instruction, raw, bound, block,
    covered.prefix block bound, decoded, actual, present, succeeds⟩

/-- The terminal RET uses the actual original slot, and its own fetch is
covered. The returned caller target is not subjected to an extra fetch. -/
theorem CoveredExecution.terminal_origin {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result) :
    ∃ count before priorReads lastReads, count + 1 = result.instructions ∧
      CallReturn.BlockFrom descriptor.frame.top choices initial before count priorReads ∧
      EDSL.CallStack.FetchWithin descriptor.frame before ∧ before.registers .rsp = descriptor.frame.top ∧
      CallReturn.rawStep (choices count) before = .ok ⟨.returned result.state, lastReads⟩ ∧
      result.reads = priorReads ++ lastReads := by
  obtain ⟨count, before, priorReads, lastReads, cost, block, slot, actual, trace⟩ :=
    covered.machine.terminal_origin
  exact ⟨count, before, priorReads, lastReads, cost, block,
    covered.prefix block (by omega), slot, actual, trace⟩

end EDSL.OS.CallMemory64
