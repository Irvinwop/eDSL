/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Frame
import EDSL.OS.StackFrame.CPU

set_option warningAsError true

namespace EDSL.CallStack
open X86 OS

/-- The actual decoded instruction's entire encoding fits the selected whole
extent. `Instruction.length` includes prefixes, SIB bytes and immediates.
This is a pre-state property, independent of the next RIP or return target.
It does not replace `CodeAt` or the CPU/OS memory coupling in `Current`. -/
def FetchWithin (frame : StackFrame.Descriptor) (before : State) : Prop :=
  ∃ (offset : Nat) (instruction : CallReturn.Instruction),
    before.rip = frame.call.code + BitVec.ofNat 64 offset ∧
    CallReturn.decodeAt before = .ok instruction ∧
    offset + instruction.length ≤ frame.call.bytes.length

/-- Determinism binds the extent bound to any independently supplied actual
decode; a shorter ghost instruction cannot justify the fetch. -/
theorem FetchWithin.decoded {frame before instruction}
    (covered : FetchWithin frame before)
    (decoded : CallReturn.decodeAt before = .ok instruction) :
    ∃ offset, before.rip = frame.call.code + BitVec.ofNat 64 offset ∧
      offset + instruction.length ≤ frame.call.bytes.length := by
  obtain ⟨offset, actual, pc, observed, bound⟩ := covered
  have same : actual = instruction := Except.ok.inj (observed.symm.trans decoded)
  subst actual
  exact ⟨offset, pc, bound⟩

theorem FetchWithin.length_le {frame before instruction}
    (covered : FetchWithin frame before)
    (decoded : CallReturn.decodeAt before = .ok instruction) :
    instruction.length ≤ frame.call.bytes.length := by
  obtain ⟨offset, _, bound⟩ := covered.decoded decoded
  omega

theorem FetchWithin.entry {frame before} (covered : FetchWithin frame before) :
    ∃ offset, before.rip = frame.call.code + BitVec.ofNat 64 offset ∧
      offset < frame.call.bytes.length := by
  obtain ⟨offset, instruction, pc, _, bound⟩ := covered
  have positive := instruction.length_pos
  exact ⟨offset, pc, by omega⟩

/-- At a known natural offset, coverage is exactly the full-length bound.
The explicit size hypotheses exclude modular aliases of natural offsets;
`Current`'s `CodeAt` contract supplies the extent bound when needed. -/
theorem FetchWithin.atOffset_iff {frame before instruction offset}
    (extent : frame.call.bytes.length ≤ 2^64) (small : offset < 2^64)
    (pc : before.rip = frame.call.code + BitVec.ofNat 64 offset)
    (decoded : CallReturn.decodeAt before = .ok instruction) :
    FetchWithin frame before ↔ offset + instruction.length ≤ frame.call.bytes.length := by
  constructor
  · intro covered
    obtain ⟨actualOffset, actualPc, bound⟩ := covered.decoded decoded
    have positive := instruction.length_pos
    have actualSmall : actualOffset < 2^64 := by omega
    have sameWord : BitVec.ofNat 64 actualOffset = BitVec.ofNat 64 offset :=
      (BitVec.add_right_inj frame.call.code).mp (actualPc.symm.trans pc)
    have same := congrArg BitVec.toNat sameWord
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt actualSmall, Nat.mod_eq_of_lt small] at same
    simpa only [same] using bound
  · intro bound
    exact ⟨offset, instruction, pc, decoded, bound⟩

/-- A continuing prefix whose every actual instruction fetch fits the same
whole code extent. This retains the CPU/OS steps, resource worlds, choice
indices and operand reads of `CPU.History`. -/
inductive CoveredHistory (frame : StackFrame.Descriptor) : CallReturn.Choices →
    StackFrame.Shared → State → StackFrame.Shared → State → Nat →
    List CallReturn.Read → Prop where
  | nil {choices shared state} : CoveredHistory frame choices shared state shared state 0 []
  | next {choices shared evolved final before middle after count reads rest}
      (step : StackFrame.CPU.Step frame shared evolved before middle (choices 0)
        ⟨.next middle, reads⟩)
      (fetch : FetchWithin frame before)
      (tail : CoveredHistory frame (choices.drop 1) evolved middle final after count rest) :
      CoveredHistory frame choices shared before final after (count + 1) (reads ++ rest)

theorem CoveredHistory.history {frame choices shared initial evolved after count reads}
    (covered : CoveredHistory frame choices shared initial evolved after count reads) :
    StackFrame.CPU.History frame choices shared initial evolved after count reads := by
  induction covered with
  | nil => exact .nil
  | next step _ _ ih => exact .next step ih

theorem CoveredHistory.current {frame choices shared initial evolved after count reads}
    (covered : CoveredHistory frame choices shared initial evolved after count reads)
    (current : StackFrame.Current frame shared initial) :
    StackFrame.Current frame evolved after := covered.history.current current

theorem CoveredHistory.preserves {frame choices shared initial evolved after count reads}
    (covered : CoveredHistory frame choices shared initial evolved after count reads) :
    StackFrame.Preservation frame shared evolved := covered.history.preserves

/-- A proof-only returning trace over actual checked CPU/OS steps. The same
immutable descriptor fixes the whole code extent and original caller-slot
boundary through every state. The terminal RET's own encoding must fit;
its returned target is not required to be fetched or belong to the extent.

This adds no admission premise and supplies no balanced-call invariant or
coverage certificate for existing compiler clients. Clients construct this
relation from their actual steps and present pre-state fetch bounds. -/
inductive CoveredExecution (frame : StackFrame.Descriptor) : CallReturn.Choices →
    StackFrame.Shared → State → StackFrame.Shared → CallReturn.Result → Prop where
  | ret {choices shared evolved before after reads}
      (step : StackFrame.CPU.Step frame shared evolved before after (choices 0)
        ⟨.returned after, reads⟩)
      (fetch : FetchWithin frame before) :
      CoveredExecution frame choices shared before evolved ⟨after, 1, reads⟩
  | next {choices shared evolved final before middle result reads}
      (step : StackFrame.CPU.Step frame shared evolved before middle (choices 0)
        ⟨.next middle, reads⟩)
      (fetch : FetchWithin frame before)
      (tail : CoveredExecution frame (choices.drop 1) evolved middle final result) :
      CoveredExecution frame choices shared before final (result.prepend 1 reads)

theorem CoveredExecution.execution {frame choices shared initial evolved result}
    (covered : CoveredExecution frame choices shared initial evolved result) :
    StackFrame.CPU.Execution frame choices shared initial evolved result := by
  induction covered with
  | ret step _ => exact .ret step
  | next step _ _ ih => exact .next step ih

/-- Compose a covered continuing prefix with a covered returning tail, using
the exact remaining choice stream and preserving all reads and step counts. -/
theorem CoveredHistory.then_execution
    {frame choices shared before evolved middle count reads final result}
    (history : CoveredHistory frame choices shared before evolved middle count reads)
    (tail : CoveredExecution frame (choices.drop count) evolved middle final result) :
    CoveredExecution frame choices shared before final (result.prepend count reads) := by
  induction history with
  | nil => simpa [Sequential.Result.prepend] using tail
  | @next choices shared nextShared evolved before nextCpu middle count firstReads rest step fetch _ ih =>
    have finish := ih (by simpa [Sequential.Choices.drop, Nat.add_comm] using tail)
    simpa [Sequential.Result.prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.append_assoc] using CoveredExecution.next step fetch finish

/-- Projection to the concrete default machine, at the same frozen boundary. -/
theorem CoveredExecution.machine {frame choices shared initial evolved result}
    (covered : CoveredExecution frame choices shared initial evolved result) :
    CallReturn.ExecutesFrom frame.top choices initial result := covered.execution.machine

theorem CoveredExecution.privateHistory {frame choices shared initial evolved result}
    (covered : CoveredExecution frame choices shared initial evolved result) :
    StackFrame.PrivateHistory frame shared evolved := covered.execution.privateHistory

theorem CoveredExecution.current {frame choices shared initial evolved result}
    (covered : CoveredExecution frame choices shared initial evolved result)
    (current : StackFrame.Current frame shared initial) :
    StackFrame.Current frame evolved result.state := covered.execution.current current

theorem CoveredExecution.preserves {frame choices shared initial evolved result}
    (covered : CoveredExecution frame choices shared initial evolved result) :
    StackFrame.Preservation frame shared evolved := covered.execution.preserves

theorem CoveredExecution.memory_frame {frame choices shared initial evolved result}
    (covered : CoveredExecution frame choices shared initial evolved result)
    (current : StackFrame.Current frame shared initial) :
    (∀ query, ¬frame.region.Contains query →
      result.state.memory.read query = initial.memory.read query) ∧
      result.state.memory.executable = initial.memory.executable ∧
      result.state.memory.writable = initial.memory.writable :=
  EDSL.CallStack.memory_frame current (covered.current current) covered.preserves

theorem CoveredExecution.fetchWithin {frame choices shared initial evolved result}
    (covered : CoveredExecution frame choices shared initial evolved result) :
    FetchWithin frame initial := by
  cases covered with
  | ret _ fetch | next _ fetch _ => exact fetch

/-- Every actual continuing prefix shorter than the certified execution ends
at a covered pre-state, including the pre-state of the terminal RET. This
quantifies over real `BlockFrom` proofs, not a client-selected list of PCs.
Equality of deterministic first boundary observations identifies each next
state and excludes atomic prefixes. The tail uses exactly `choices.drop 1`. -/
theorem CoveredExecution.prefix {frame choices shared initial evolved result}
    (covered : CoveredExecution frame choices shared initial evolved result)
    {before count reads}
    (block : CallReturn.BlockFrom frame.top choices initial before count reads)
    (bound : count < result.instructions) : FetchWithin frame before := by
  induction covered generalizing before count reads with
  | ret step fetch =>
    cases block with
    | nil => exact fetch
    | next actual _ =>
      have impossible := Except.ok.inj (step.machine.symm.trans actual)
      cases impossible
    | atomic actual _ =>
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

/-- An existing actual CPU/OS execution can be strengthened by proving fetch
coverage for every actual pre-terminal prefix. This is a proof-construction
rule, not an admission or future-success assumption. -/
theorem CoveredExecution.of_execution {frame choices shared initial evolved result}
    (execution : StackFrame.CPU.Execution frame choices shared initial evolved result)
    (fetches : ∀ {before count reads},
      CallReturn.BlockFrom frame.top choices initial before count reads →
      count < result.instructions → FetchWithin frame before) :
    CoveredExecution frame choices shared initial evolved result := by
  induction execution with
  | ret step => exact .ret step (fetches .nil (by change 0 < 1; decide))
  | next step tail ih =>
    refine .next step (fetches .nil (by simp only [Sequential.Result.prepend]; omega)) (ih ?_)
    intro before count reads block bound
    exact fetches (.next step.machine block)
      (by simp only [Sequential.Result.prepend]; omega)

/-- Accumulated operand reads originate at covered actual machine pre-states,
with the same frozen original slot and the exact choice-stream index. -/
theorem CoveredExecution.read_origin {frame choices shared initial evolved result}
    (covered : CoveredExecution frame choices shared initial evolved result)
    {read : CallReturn.Read} (member : read ∈ result.reads) :
    ∃ count before priorReads instruction raw, count < result.instructions ∧
      CallReturn.BlockFrom frame.top choices initial before count priorReads ∧
      FetchWithin frame before ∧
      CallReturn.decodeAt before = .ok instruction ∧
      CallReturn.execute before instruction (choices count) = .ok raw ∧
      read ∈ instruction.operandReads before ∧ Sequential.OperandReadSucceeds before read := by
  obtain ⟨count, before, priorReads, instruction, raw, bound, block, decoded, actual,
    present, succeeds⟩ := covered.machine.read_origin member
  exact ⟨count, before, priorReads, instruction, raw, bound, block,
    covered.prefix block bound, decoded, actual, present, succeeds⟩

/-- The terminal RET is covered, even when its actual RAM-derived target lies
outside the code extent. No fetch condition is imposed on `result.state`. -/
theorem CoveredExecution.terminal_origin {frame choices shared initial evolved result}
    (covered : CoveredExecution frame choices shared initial evolved result) :
    ∃ count before priorReads lastReads, count + 1 = result.instructions ∧
      CallReturn.BlockFrom frame.top choices initial before count priorReads ∧
      FetchWithin frame before ∧ before.registers .rsp = frame.top ∧
      CallReturn.rawStep (choices count) before = .ok ⟨.returned result.state, lastReads⟩ ∧
      result.reads = priorReads ++ lastReads := by
  obtain ⟨count, before, priorReads, lastReads, cost, block, slot, actual, trace⟩ :=
    covered.machine.terminal_origin
  exact ⟨count, before, priorReads, lastReads, cost, block,
    covered.prefix block (by omega), slot, actual, trace⟩

end EDSL.CallStack
