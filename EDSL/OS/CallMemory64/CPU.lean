/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallMemory64.History
import EDSL.OS.StackFrame.CPU

set_option warningAsError true

namespace EDSL.OS.CallMemory64
open X86 AddressSpace

/-- Retain the existing STACK8 policy. The only additional operand is an
actual owned DATA8 observation at the selected target in this OS world.
Observation creates neither a read loan nor an evolved world. -/
inductive ReadAllowed (descriptor : Descriptor) (shared : Shared)
    (read : CallReturn.Read) : Prop where
  | stack (allowed : StackFrame.ReadAllowed descriptor.frame shared read)
  | data (kind : read.kind = .data) (bytes : read.bytes = 8)
      (target : read.address = descriptor.target)
      (owned : ∃ value, Borrowing.loadOwnedWord64 shared descriptor.owner
        descriptor.ticket descriptor.target = .ok value)

theorem ReadAllowed.bytes {descriptor shared read}
    (allowed : ReadAllowed descriptor shared read) : read.bytes = 8 := by
  cases allowed with
  | data _ bytes _ _ => exact bytes
  | stack allowed =>
    cases allowed with
    | original allowed => exact allowed.2.2.1
    | privateSlot _ bytes _ => exact bytes

theorem ReadAllowed.data_target {descriptor shared read}
    (allowed : ReadAllowed descriptor shared read) (kind : read.kind = .data) :
    read.address = descriptor.target ∧
      ∃ value, Borrowing.loadOwnedWord64 shared descriptor.owner descriptor.ticket
        descriptor.target = .ok value := by
  cases allowed with
  | data _ _ target owned => exact ⟨target, owned⟩
  | stack allowed =>
    have stack : read.kind = .stack := by
      cases allowed with
      | original allowed => exact allowed.1
      | privateSlot kind _ _ => exact kind
    rw [kind] at stack
    cases stack

namespace CPU

/-- Derive the current machine load and owner/epoch authority from the same
complete coupled RAM. A successful read in a prior world is insufficient. -/
theorem current_target_read {descriptor : Descriptor} {shared : Shared} {before : X86.State}
    (current : Current descriptor shared before) :
    ∃ value, Borrowing.loadOwnedWord64 shared descriptor.owner descriptor.ticket
        descriptor.target = .ok value ∧
      loadQWord before.memory descriptor.target = .ok value ∧
      Ownership.Current shared.resources descriptor.owner descriptor.ticket ∧
      ReadAllowed descriptor shared ⟨.data, descriptor.target, 8⟩ ∧
      Sequential.OperandReadSucceeds before ⟨.data, descriptor.target, 8⟩ := by
  obtain ⟨value, owned, observed, authority⟩ := current.contract.data_read
  have loaded : loadQWord before.memory descriptor.target = .ok value := by
    rw [current.coupled]
    exact loadQWord_of_readWord _ _ _ observed
  exact ⟨value, owned, loaded, authority, .data rfl rfl rfl ⟨value, owned⟩, value, loaded⟩

/-- Private CALL/PUSH effects retain their existing relation. An ordinary
DATA8 store has a separate intent and uses only the selected DATA ticket. -/
inductive Effect (descriptor : Descriptor) : Shared → Shared → X86.State → X86.State →
    CallReturn.Instruction → Prop where
  | stack {shared evolved before after instruction}
      (effect : StackFrame.CPU.Effect descriptor.frame shared evolved before after instruction) :
      Effect descriptor shared evolved before after instruction
  | data64 {shared evolved before after instruction value}
      (intent : instruction.storeIntent64 before = some (descriptor.target, value))
      (success : Borrowing.mutate shared
        (.store64 descriptor.owner descriptor.ticket descriptor.target value) = .ok (evolved, none)) :
      Effect descriptor shared evolved before after (.sequential instruction)

/-- The ordinary full-width intent is classified as embedded DATA, never as
a CALL/PUSH write and never as an embedded four-byte write. -/
theorem data64_writeEffect {instruction : Sequential.Instruction} {before : X86.State}
    {address value : Word}
    (intent : instruction.storeIntent64 before = some (address, value)) :
    (CallReturn.Instruction.sequential instruction).writeEffect before =
      some (.embeddedData64 address value) := by
  cases instruction <;>
    simp only [Sequential.Instruction.storeIntent64, Option.some.injEq, Prod.mk.injEq,
      reduceCtorEq] at intent
  rcases intent with ⟨rfl, rfl⟩
  rfl

/-- Any admitted ordinary full64 effect writes precisely the selected target
and value using the DATA ticket, including when other mapped RAM is writable. -/
theorem Effect.data64_checked {descriptor shared evolved before after instruction address value}
    (effect : Effect descriptor shared evolved before after instruction)
    (classified : instruction.writeEffect before = some (.embeddedData64 address value)) :
    address = descriptor.target ∧
      Borrowing.mutate shared (.store64 descriptor.owner descriptor.ticket descriptor.target value) =
        .ok (evolved, none) := by
  cases effect with
  | stack effect =>
    cases effect with
    | call _ _ | push _ _ => cases classified
    | unchanged noWrite _ => rw [noWrite] at classified; cases classified
  | data64 intent success =>
    have same := Option.some.inj ((data64_writeEffect intent).symm.trans classified)
    cases same
    exact ⟨rfl, success⟩

theorem Effect.no_data32 {descriptor shared evolved before after instruction address value}
    (effect : Effect descriptor shared evolved before after instruction) :
    instruction.writeEffect before ≠ some (.embeddedData32 address value) := by
  intro classified
  cases effect with
  | stack effect =>
    cases effect with
    | call _ _ | push _ _ => cases classified
    | unchanged noWrite _ => rw [noWrite] at classified; cases classified
  | data64 intent _ => rw [data64_writeEffect intent] at classified; cases classified

theorem Effect.history {descriptor shared evolved before after instruction}
    (effect : Effect descriptor shared evolved before after instruction) :
    CallMemory64.History descriptor shared evolved := by
  cases effect with
  | stack effect =>
    cases effect with
    | call slot success | push slot success => exact .next (.privateSlot slot success) .refl
    | unchanged _ _ => exact .refl
  | data64 _ success => exact .next (.data success) .refl

/-- Exact decoding, execution, raw CPU endpoint, frozen original-slot
observation, owner mutation and all operand permissions share this pre-state.
Use with `Current` to obtain the full RAM coupling at both endpoints. DATA4
and atomic operand reads have no permission constructor; syscalls have no CPU. -/
def Step (descriptor : Descriptor) (shared evolved : Shared) (before after : X86.State)
    (af : Bool) (observation : CallReturn.Observation) : Prop :=
  ∃ instruction raw, CallReturn.decodeAt before = .ok instruction ∧
    CallReturn.execute before instruction af = .ok raw ∧
    CallReturn.cpu raw.result = some after ∧
    observation = CallReturn.atBoundary descriptor.frame.top before raw ∧
    Effect descriptor shared evolved before after instruction ∧
    ∀ read, read ∈ raw.reads → ReadAllowed descriptor shared read

/-- Existing private stack steps embed without weakening their resource or
read relations. This also covers register instructions and original RET. -/
theorem lift_stack {descriptor shared evolved before after af observation}
    (step : StackFrame.CPU.Step descriptor.frame shared evolved before after af observation) :
    Step descriptor shared evolved before after af observation := by
  obtain ⟨instruction, raw, decoded, actual, cpu, observed, effect, reads⟩ := step
  exact ⟨instruction, raw, decoded, actual, cpu, observed, .stack effect,
    fun read member => .stack (reads read member)⟩

theorem Step.machine {descriptor shared evolved before after af observation}
    (step : Step descriptor shared evolved before after af observation) :
    CallReturn.boundaryStep descriptor.frame.top af before = .ok observation := by
  obtain ⟨instruction, raw, decoded, actual, _, observed, _, _⟩ := step
  exact CallReturn.boundaryStep_success_iff.mpr
    ⟨raw, (CallReturn.rawStep_eq_execute af decoded).trans actual, observed⟩

theorem Step.cpu {descriptor shared evolved before after af observation}
    (step : Step descriptor shared evolved before after af observation) :
    CallReturn.cpu observation.result = some after := by
  obtain ⟨_, raw, _, _, cpu, observed, _, _⟩ := step
  subst observation
  exact (CallReturn.atBoundary_cpu _ _ raw).trans cpu

theorem Step.reads {descriptor shared evolved before after af observation}
    (step : Step descriptor shared evolved before after af observation) :
    ∀ read, read ∈ observation.reads → ReadAllowed descriptor shared read := by
  obtain ⟨_, _, _, _, _, observed, _, reads⟩ := step
  subst observation
  simpa only [CallReturn.atBoundary_reads] using reads

private theorem locked_read {instruction : CallReturn.Instruction} {before : X86.State}
    (locked : instruction.isLocked = true) :
    (⟨.data, before.registers .rdi, 4⟩ : CallReturn.Read) ∈ instruction.operandReads before := by
  cases instruction <;> simp only [CallReturn.Instruction.isLocked, Bool.false_eq_true] at locked
  rename_i old
  cases old <;> simp only [Sequential.Instruction.isLocked, Bool.false_eq_true] at locked
  rename_i old
  rcases (X86.Instruction.isLocked_eq_true_iff old).mp locked with rfl | rfl <;>
    simp [CallReturn.Instruction.operandReads, Sequential.Instruction.operandReads]

/-- The current ISA's locked RMWs require DATA4 reads, which this sibling
cannot authorize. This does not invent an atomic DATA8 resource rule. -/
theorem Step.unlocked {descriptor shared evolved before after af observation instruction}
    (step : Step descriptor shared evolved before after af observation)
    (decoded : CallReturn.decodeAt before = .ok instruction) : instruction.isLocked = false := by
  obtain ⟨actualInstruction, raw, actualDecoded, actual, _, _, _, reads⟩ := step
  have same : actualInstruction = instruction := Except.ok.inj (actualDecoded.symm.trans decoded)
  subst actualInstruction
  cases locked : instruction.isLocked with
  | false => rfl
  | true =>
    have allowed := reads ⟨.data, before.registers .rdi, 4⟩
      (by rw [CallReturn.execute_reads actual]; exact locked_read locked)
    exact False.elim ((by decide : (4 : Nat) ≠ 8) allowed.bytes)

theorem Step.no_syscall {descriptor shared evolved before after af observation}
    (step : Step descriptor shared evolved before after af observation) (request : SyscallRequest) :
    observation.result ≠ .syscall request := by
  intro same
  have cpu := step.cpu
  rw [same] at cpu
  cases cpu

theorem Step.history {descriptor shared evolved before after af observation}
    (step : Step descriptor shared evolved before after af observation) :
    CallMemory64.History descriptor shared evolved := by
  obtain ⟨_, _, _, _, _, _, effect, _⟩ := step
  exact effect.history

theorem Step.current {descriptor shared evolved before after af observation}
    (step : Step descriptor shared evolved before after af observation)
    (current : Current descriptor shared before) : Current descriptor evolved after := by
  have contract := step.history.contract current.contract
  obtain ⟨instruction, raw, _, actual, cpu, _, effect, _⟩ := step
  refine ⟨contract, ?_⟩
  cases effect with
  | stack effect =>
    cases effect with
    | call slot success =>
      obtain ⟨_, memory, stored, same⟩ := CallReturn.execute_call_success_iff.mp actual
      subst raw
      have afterEq : CallReturn.callState before _ memory = after := Option.some.inj cpu
      have machine := stored
      rw [current.coupled] at machine
      rw [← afterEq]
      exact Except.ok.inj (machine.symm.trans (Borrowing.store64_effect success).machine)
    | push slot success =>
      obtain ⟨memory, stored, same⟩ := CallReturn.execute_push_success_iff.mp actual
      subst raw
      have afterEq : CallReturn.pushState before _ memory = after := Option.some.inj cpu
      have machine := stored
      rw [current.coupled] at machine
      rw [← afterEq]
      exact Except.ok.inj (machine.symm.trans (Borrowing.store64_effect success).machine)
    | unchanged _ memory => exact memory.trans current.coupled
  | data64 intent success =>
    rw [CallReturn.execute_sequential] at actual
    obtain ⟨memory, stored, same⟩ := (Sequential.execute_storeIntent64_success_iff intent).mp actual
    subst raw
    have afterEq : ({ before with
        memory := memory
        rip := before.rip + BitVec.ofNat 64 _ } : X86.State) = after := Option.some.inj cpu
    have machine := stored
    rw [current.coupled] at machine
    rw [← afterEq]
    exact Except.ok.inj (machine.symm.trans (Borrowing.store64_effect success).machine)

/-- Present target authority enables the real checked Borrowing mutation,
which derives the actual Sequential and sibling CALL/RET-ISA execution.
The returned CPU has exactly the mutated OS world's full memory. -/
theorem data_store_step {descriptor : Descriptor} {shared : Shared} {before : X86.State}
    {instruction : Sequential.Instruction} {value : Word}
    (current : Current descriptor shared before)
    (decoded : Sequential.decodeAt before = .ok instruction)
    (intent : instruction.storeIntent64 before = some (descriptor.target, value)) (af : Bool) :
    ∃ evolved, let after := WordResources64.storeAfterLength before evolved instruction.length
      Borrowing.mutate shared (.store64 descriptor.owner descriptor.ticket descriptor.target value) =
        .ok (evolved, none) ∧
      CallReturn.execute before (.sequential instruction) af = .ok ⟨.next after, []⟩ ∧
      Step descriptor shared evolved before after af ⟨.next after, []⟩ ∧
      Current descriptor evolved after ∧
      Borrowing.StoreEffect64 shared evolved descriptor.target value ∧
      Borrowing.loadOwnedWord64 evolved descriptor.owner descriptor.ticket descriptor.target =
        .ok value := by
  obtain ⟨evolved, success⟩ := current.contract.data_store64_enabled value
  obtain ⟨sequential, effect⟩ :=
    WordResources64.actual_store64_bridge current.coupled decoded intent success af
  have actual := (CallReturn.execute_sequential before instruction af).trans
    ((Sequential.step_eq_execute af decoded).symm.trans sequential)
  have step : Step descriptor shared evolved before
      (WordResources64.storeAfterLength before evolved instruction.length) af
      ⟨.next (WordResources64.storeAfterLength before evolved instruction.length), []⟩ :=
    ⟨.sequential instruction, _, CallReturn.decodeAt_sequential_store64 decoded intent, actual, rfl, rfl,
      .data64 intent success, by intro read member; cases member⟩
  exact ⟨evolved, success, actual, step, step.current current, effect,
    Borrowing.store64_owned_readback success⟩

/-- Read-only execution can use the sibling's current DATA8 policy. Full RAM
equality is required in addition to absence of an ordinary write effect. -/
theorem unchanged_step {descriptor : Descriptor} {shared : Shared} {before after : X86.State}
    {instruction : CallReturn.Instruction} {af : Bool} {raw : CallReturn.Observation}
    (decoded : CallReturn.decodeAt before = .ok instruction)
    (actual : CallReturn.execute before instruction af = .ok raw)
    (cpu : CallReturn.cpu raw.result = some after)
    (noWrite : instruction.writeEffect before = none) (memory : after.memory = before.memory)
    (reads : ∀ read, read ∈ raw.reads → ReadAllowed descriptor shared read) :
    Step descriptor shared shared before after af
      (CallReturn.atBoundary descriptor.frame.top before raw) :=
  ⟨instruction, raw, decoded, actual, cpu, rfl, .stack (.unchanged noWrite memory), reads⟩

/-- The decoded load uses the PRE-state address, including destination/base
aliases. Its permission is an actual observation of the current owned word. -/
theorem data_load_step {descriptor : Descriptor} {shared : Shared} {before : X86.State}
    {destination : Register} {address : Sequential.Address}
    (current : Current descriptor shared before)
    (decoded : Sequential.decodeAt before = .ok (.loadMem64 destination address))
    (effective : address.eval before = descriptor.target) (af : Bool) :
    ∃ (value : Word), let after : X86.State := { before.writeRegister destination value with
        rip := before.rip + BitVec.ofNat 64 (Sequential.Instruction.loadMem64 destination address).length }
      Borrowing.loadOwnedWord64 shared descriptor.owner descriptor.ticket descriptor.target =
        .ok value ∧
      loadQWord before.memory descriptor.target = .ok value ∧
      Step descriptor shared shared before after af
        ⟨.next after, [⟨.data, descriptor.target, 8⟩]⟩ ∧
      Current descriptor shared after ∧ after.registers destination = value := by
  obtain ⟨value, owned, loaded, _, allowed, _⟩ := current_target_read current
  let after : X86.State := { before.writeRegister destination value with
    rip := before.rip + BitVec.ofNat 64 (Sequential.Instruction.loadMem64 destination address).length }
  have actual : CallReturn.execute before (.sequential (.loadMem64 destination address)) af =
      .ok ⟨.next after, [⟨.data, descriptor.target, 8⟩]⟩ := by
    rw [CallReturn.execute_sequential, Sequential.execute_loadMem64, effective, loaded]
    rfl
  have step : Step descriptor shared shared before after af
      ⟨.next after, [⟨.data, descriptor.target, 8⟩]⟩ :=
    unchanged_step (CallReturn.decodeAt_sequential decoded) actual rfl rfl rfl
      (fun read member => List.mem_singleton.mp member ▸ allowed)
  exact ⟨value, owned, loaded, step, step.current current, by simp [State.writeRegister]⟩

/-- A continuing trace threads one OS world and one frozen original slot
through private stack writes, ordinary DATA8 stores and current reads. -/
inductive History (descriptor : Descriptor) : CallReturn.Choices → Shared → X86.State →
    Shared → X86.State → Nat → List CallReturn.Read → Prop where
  | nil {choices shared machine} : History descriptor choices shared machine shared machine 0 []
  | next {choices shared evolved final before middle after count reads rest}
      (step : Step descriptor shared evolved before middle (choices 0) ⟨.next middle, reads⟩)
      (tail : History descriptor (choices.drop 1) evolved middle final after count rest) :
      History descriptor choices shared before final after (count + 1) (reads ++ rest)

theorem History.machine {descriptor choices shared before final after count reads}
    (history : History descriptor choices shared before final after count reads) :
    CallReturn.BlockFrom descriptor.frame.top choices before after count reads := by
  induction history with
  | nil => exact .nil
  | next step _ ih => exact .next step.machine ih

theorem History.mixedHistory {descriptor choices shared before final after count reads}
    (history : History descriptor choices shared before final after count reads) :
    CallMemory64.History descriptor shared final := by
  induction history with
  | nil => exact .refl
  | next step _ ih => exact step.history.trans ih

theorem History.current {descriptor choices shared before final after count reads}
    (history : History descriptor choices shared before final after count reads)
    (current : Current descriptor shared before) : Current descriptor final after := by
  induction history with
  | nil => exact current
  | next step _ ih => exact ih (step.current current)

theorem History.preserves {descriptor choices shared before final after count reads}
    (history : History descriptor choices shared before final after count reads) :
    Preservation descriptor shared final := history.mixedHistory.preserves

/-- Returning mixed executions include the actual original-slot terminal RET.
Internal RETs continue according to the existing concrete boundary adapter. -/
inductive Execution (descriptor : Descriptor) : CallReturn.Choices → Shared → X86.State →
    Shared → CallReturn.Result → Prop where
  | ret {choices shared evolved before after reads}
      (step : Step descriptor shared evolved before after (choices 0) ⟨.returned after, reads⟩) :
      Execution descriptor choices shared before evolved ⟨after, 1, reads⟩
  | next {choices shared evolved final before middle result reads}
      (step : Step descriptor shared evolved before middle (choices 0) ⟨.next middle, reads⟩)
      (tail : Execution descriptor (choices.drop 1) evolved middle final result) :
      Execution descriptor choices shared before final (result.prepend 1 reads)

theorem Execution.machine {descriptor choices shared before final result}
    (execution : Execution descriptor choices shared before final result) :
    CallReturn.ExecutesFrom descriptor.frame.top choices before result := by
  induction execution with
  | ret step => exact .ret step.machine
  | next step _ ih => exact .next step.machine ih

theorem Execution.mixedHistory {descriptor choices shared before final result}
    (execution : Execution descriptor choices shared before final result) :
    CallMemory64.History descriptor shared final := by
  induction execution with
  | ret step => exact step.history
  | next step _ ih => exact step.history.trans ih

theorem Execution.current {descriptor choices shared before final result}
    (execution : Execution descriptor choices shared before final result)
    (current : Current descriptor shared before) : Current descriptor final result.state := by
  induction execution with
  | ret step => exact step.current current
  | next step _ ih => exact ih (step.current current)

theorem Execution.preserves {descriptor choices shared before final result}
    (execution : Execution descriptor choices shared before final result) :
    Preservation descriptor shared final := execution.mixedHistory.preserves

theorem History.then_execution {descriptor choices shared before evolved middle count reads final result}
    (history : History descriptor choices shared before evolved middle count reads)
    (tail : Execution descriptor (choices.drop count) evolved middle final result) :
    Execution descriptor choices shared before final (result.prepend count reads) := by
  induction history with
  | nil => simpa [Sequential.Result.prepend] using tail
  | @next choices shared nextShared evolved before nextCpu middle count firstReads rest step _ ih =>
    have finish := ih (by simpa [Sequential.Choices.drop, Nat.add_comm] using tail)
    simpa [Sequential.Result.prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.append_assoc] using Execution.next step finish

/-- The concrete evaluator succeeds with any sufficient fuel. -/
theorem Execution.run {descriptor choices shared before final result}
    (execution : Execution descriptor choices shared before final result) {fuel : Nat}
    (enough : result.instructions ≤ fuel) :
    CallReturn.runFrom descriptor.frame.top choices fuel before = .ok result :=
  CallReturn.runFrom_complete execution.machine enough

end CPU
end EDSL.OS.CallMemory64
