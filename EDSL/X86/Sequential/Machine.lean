/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Flags
import EDSL.X86.Sequential.DecodeTransport

namespace EDSL.X86.Sequential

/-- Exact operand reads of an instruction, using the PRE-instruction state.
Instruction fetch and write-validation permission queries are not operand reads. -/
def Instruction.operandReads (instruction : Instruction) (state : State) : List Read :=
  match instruction with
  | .legacy .ret => [⟨.stack, state.registers .rsp, 8⟩]
  | .legacy .loadEaxRdi | .legacy .exchangeEaxRdi | .legacy .fetchAddEaxRdi =>
    [⟨.data, state.registers .rdi, 4⟩]
  | .legacy .loadEaxRsi => [⟨.data, state.registers .rsi, 4⟩]
  | .loadMem32 _ address | .addMem32 _ address => [⟨.data, address.eval state, 4⟩]
  | _ => []

/-- Ordinary store intent uses the PRE-instruction address and low 32 source
bits. Permission validation is part of execution, not an operand read. -/
def Instruction.storeIntent (instruction : Instruction) (state : State) : Option (Word × BitVec 32) :=
  match instruction with
  | .legacy old => old.storeIntent state
  | .storeMem32 address source => some (address.eval state, (state.registers source).setWidth 32)
  | _ => none

/-- The sequential extension does not enroll ordinary MOV stores in a
concurrent profile. Only embedded legacy instructions can be locked. -/
def Instruction.isLocked : Instruction → Bool
  | .legacy old => old.isLocked
  | _ => false

def Instruction.choosesAF : Instruction → Bool
  | .xorSelf32 _ | .test64 _ _ => true
  | _ => false

/-- Read success is checked by the actual memory primitives, including their
canonicality, nonwrapping and per-byte accessibility checks. -/
def OperandReadSucceeds (state : State) (read : Read) : Prop :=
  match read.kind with
  | .stack => read.bytes = 8 ∧ ∃ value, readWord state.memory read.address = .ok value
  | .data => read.bytes = 4 ∧ ∃ value, loadDWord state.memory read.address = .ok value

/-- The explicit AF argument is used only by XOR/TEST. Legacy execution retains
its complete old result, including concrete flags, stores, atomics and syscall
contexts, for EVERY value of the new argument. -/
def execute (state : State) (instruction : Instruction) (af : Bool) : Except Error Observation := do
  let reads := instruction.operandReads state
  match instruction with
  | .legacy old => return ⟨← X86.executeInstruction state old, reads⟩
  | .movReg32 destination source =>
    return ⟨.next { state.writeRegister destination
      (((state.registers source).setWidth 32).setWidth 64) with rip := state.rip + 2 }, reads⟩
  | .movReg64 destination source =>
    return ⟨.next { state.writeRegister destination (state.registers source) with
      rip := state.rip + 3 }, reads⟩
  | .loadMem32 destination address =>
    let value ← loadDWord state.memory (address.eval state)
    return ⟨.next { state.writeRegister destination (value.setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 instruction.length }, reads⟩
  | .storeMem32 address source =>
    let memory ← storeDWord state.memory (address.eval state) ((state.registers source).setWidth 32)
    return ⟨.next { state with
      memory := memory
      rip := state.rip + BitVec.ofNat 64 instruction.length }, reads⟩
  | .xorSelf32 destination =>
    return ⟨.next { state.writeRegister destination 0 with
      rip := state.rip + 2, flags := logicalFlags32 state.flags 0 af }, reads⟩
  | .test64 left right =>
    return ⟨.next { state with
      rip := state.rip + 3
      flags := logicalFlags64 state.flags (state.registers left &&& state.registers right) af }, reads⟩
  | .cmp64 left right =>
    return ⟨.next { state with
      rip := state.rip + 3
      flags := cmpFlags64 state.flags (state.registers left) (state.registers right) }, reads⟩
  | .addMem32 destination address =>
    let value ← loadDWord state.memory (address.eval state)
    let left := (state.registers destination).setWidth 32
    return ⟨.next { state.writeRegister destination ((left + value).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 instruction.length,
      flags := addFlags32 state.flags left value }, reads⟩
  | .addImm64 destination immediate =>
    let left := state.registers destination
    let right := immediate.signExtend 64
    return ⟨.next { state.writeRegister destination (left + right) with
      rip := state.rip + 4, flags := addFlags64 state.flags left right }, reads⟩
  | .inc64 destination =>
    return ⟨.next { state.writeRegister destination (state.registers destination + 1) with
      rip := state.rip + 3, flags := incFlags64 state.flags (state.registers destination) }, reads⟩
  | .dec64 destination =>
    return ⟨.next { state.writeRegister destination (state.registers destination - 1) with
      rip := state.rip + 3, flags := decFlags64 state.flags (state.registers destination) }, reads⟩
  | .je displacement => return ⟨.next (← executeShortBranch state (state.flags.getLsbD 6) displacement), reads⟩
  | .jmp displacement => return ⟨.next (← executeShortBranch state true displacement), reads⟩

def step (af : Bool) (state : State) : Except Error Observation := do
  let instruction ← decodeAt state
  execute state instruction af

theorem step_eq_execute {state : State} {instruction : Instruction} (af : Bool)
    (decoded : decodeAt state = .ok instruction) :
    step af state = execute state instruction af := by
  simp only [step, decoded, ok_bind]

theorem execute_legacy (state : State) (instruction : X86.Instruction) (af : Bool) :
    execute state (.legacy instruction) af =
      (fun result => Observation.mk result ((Instruction.legacy instruction).operandReads state)) <$>
        X86.executeInstruction state instruction := rfl

theorem execute_movReg32 (state : State) (destination source : Register) (af : Bool) :
    execute state (.movReg32 destination source) af =
      .ok ⟨.next { state.writeRegister destination
        (((state.registers source).setWidth 32).setWidth 64) with rip := state.rip + 2 }, []⟩ := rfl

theorem execute_movReg64 (state : State) (destination source : Register) (af : Bool) :
    execute state (.movReg64 destination source) af =
      .ok ⟨.next { state.writeRegister destination (state.registers source) with
        rip := state.rip + 3 }, []⟩ := rfl

theorem execute_loadMem32 (state : State) (destination : Register) (address : Address) (af : Bool) :
    execute state (.loadMem32 destination address) af = do
      let value ← loadDWord state.memory (address.eval state)
      return ⟨.next { state.writeRegister destination (value.setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (Instruction.loadMem32 destination address).length },
        [⟨.data, address.eval state, 4⟩]⟩ := rfl

theorem execute_storeMem32 (state : State) (address : Address) (source : Register) (af : Bool) :
    execute state (.storeMem32 address source) af = do
      let memory ← storeDWord state.memory (address.eval state) ((state.registers source).setWidth 32)
      return ⟨.next { state with
        memory := memory
        rip := state.rip + BitVec.ofNat 64 (Instruction.storeMem32 address source).length }, []⟩ := rfl

/-- Register operands are captured before the destination update, including
self-moves. All flags and all memory fields are preserved. -/
theorem execute_movReg32_context (state : State) (destination source : Register) (af : Bool) :
    ∃ final, execute state (.movReg32 destination source) af = .ok ⟨.next final, []⟩ ∧
      final.registers destination = ((state.registers source).setWidth 32).setWidth 64 ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags ∧ final.rip = state.rip + 2 := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

/-- Even a self-move clears the upper 32 bits rather than preserving the old
64-bit register value. -/
theorem execute_movReg32_self (state : State) (register : Register) (af : Bool) :
    ∃ final, execute state (.movReg32 register register) af = .ok ⟨.next final, []⟩ ∧
      (final.registers register).toNat = (state.registers register).toNat % 2^32 := by
  obtain ⟨final, executed, value, _⟩ := execute_movReg32_context state register register af
  refine ⟨final, executed, ?_⟩
  rw [value]
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

/-- Full-width MOV uses the PRE-instruction source for every register, including
self-copies and RSP destinations. It preserves all flags and the full memory. -/
theorem execute_movReg64_context (state : State) (destination source : Register) (af : Bool) :
    ∃ final, execute state (.movReg64 destination source) af = .ok ⟨.next final, []⟩ ∧
      final.registers destination = state.registers source ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags ∧ final.rip = state.rip + 3 := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

/-- A full-width self-copy leaves the entire state identical except for RIP. -/
theorem execute_movReg64_self (state : State) (register : Register) (af : Bool) :
    execute state (.movReg64 register register) af =
      .ok ⟨.next { state with rip := state.rip + 3 }, []⟩ := by
  rw [execute_movReg64]
  have unchanged : state.writeRegister register (state.registers register) = state := by
    have registers :
        (fun other => if other = register then state.registers register else state.registers other) =
          state.registers := by
      funext other
      split
      · next equal => subst other; rfl
      · rfl
    simp only [State.writeRegister, registers]
  rw [unchanged]

/-- The actual checked load uses the PRE-instruction address, even when the
destination is an address base or index. No distinctness assumption is needed. -/
theorem execute_loadMem32_context {state : State} {destination : Register} {address : Address}
    {value : BitVec 32} (af : Bool)
    (loaded : loadDWord state.memory (address.eval state) = .ok value) :
    ∃ final, execute state (.loadMem32 destination address) af =
        .ok ⟨.next final, [⟨.data, address.eval state, 4⟩]⟩ ∧
      final.registers destination = value.setWidth 64 ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.loadMem32 destination address).length := by
  refine ⟨{ state.writeRegister destination (value.setWidth 64) with
    rip := state.rip + BitVec.ofNat 64 (Instruction.loadMem32 destination address).length },
    ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [execute_loadMem32, loaded, ok_bind, pure_ok]
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

/-- Success exposes the actual four-byte primitive result; an observation
cannot assert an unchecked or differently addressed load. -/
theorem execute_loadMem32_success_iff {state : State} {destination : Register} {address : Address}
    {af : Bool} {observation : Observation} :
    execute state (.loadMem32 destination address) af = .ok observation ↔
      ∃ value, loadDWord state.memory (address.eval state) = .ok value ∧
        observation = ⟨.next { state.writeRegister destination (value.setWidth 64) with
          rip := state.rip + BitVec.ofNat 64 (Instruction.loadMem32 destination address).length },
          [⟨.data, address.eval state, 4⟩]⟩ := by
  rw [execute_loadMem32]
  cases loaded : loadDWord state.memory (address.eval state) <;> simp [eq_comm]

/-- Every classified ordinary store executes the same checked store primitive.
This also covers the embedded legacy ordinary stores without changing them. -/
theorem execute_storeIntent {state : State} {instruction : Instruction} {address : Word}
    {value : BitVec 32} (af : Bool)
    (intent : instruction.storeIntent state = some (address, value)) :
    execute state instruction af = do
      let memory ← storeDWord state.memory address value
      return ⟨.next { state with
        memory := memory
        rip := state.rip + BitVec.ofNat 64 instruction.length }, []⟩ := by
  cases instruction with
  | legacy old =>
    change old.storeIntent state = some (address, value) at intent
    rcases (old.storeIntent_eq_some_iff state address value).mp intent with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · cases stored : storeDWord state.memory (state.registers .rdi) ((state.registers .rsi).setWidth 32) <;>
        simp [execute, X86.executeInstruction, executeStore, Instruction.operandReads,
          Instruction.length, stored]
    · cases stored : storeDWord state.memory (state.registers .rsi) ((state.registers .rax).setWidth 32) <;>
        simp [execute, X86.executeInstruction, executeStoreRsi, Instruction.operandReads,
          Instruction.length, stored]
  | storeMem32 operand source =>
    simp only [Instruction.storeIntent, Option.some.injEq, Prod.mk.injEq] at intent
    rcases intent with ⟨rfl, rfl⟩
    exact execute_storeMem32 state operand source af
  | movReg32 _ _ | movReg64 _ _ | loadMem32 _ _ | xorSelf32 _ | test64 _ _ | cmp64 _ _ | addMem32 _ _
  | addImm64 _ _ | inc64 _ | dec64 _ | je _ | jmp _ =>
    simp [Instruction.storeIntent] at intent

/-- Successful stores expose the exact checked memory result and empty operand
read footprint. Validation queries never become data reads. -/
theorem execute_storeIntent_success_iff {state : State} {instruction : Instruction} {address : Word}
    {value : BitVec 32} {af : Bool} {observation : Observation}
    (intent : instruction.storeIntent state = some (address, value)) :
    execute state instruction af = .ok observation ↔
      ∃ memory, storeDWord state.memory address value = .ok memory ∧
        observation = ⟨.next { state with
          memory := memory
          rip := state.rip + BitVec.ofNat 64 instruction.length }, []⟩ := by
  rw [execute_storeIntent af intent]
  cases stored : storeDWord state.memory address value <;> simp [eq_comm]

/-- Complete success/failure behavior: all four bytes are validated before an
updated state exists. This is a sequential byte update, not an atomicity claim. -/
theorem execute_storeIntent_checked {state : State} {instruction : Instruction} {address : Word}
    {value : BitVec 32} (af : Bool)
    (intent : instruction.storeIntent state = some (address, value)) :
    execute state instruction af =
      if canStoreDWord state.memory address then
        .ok ⟨.next { state with
          memory := writeDWordUnchecked state.memory address value
          rip := state.rip + BitVec.ofNat 64 instruction.length }, []⟩
      else .error (.writeDenied address) := by
  rw [execute_storeIntent af intent]
  cases allowed : canStoreDWord state.memory address <;> simp [storeDWord, allowed]

/-- Store intent determines the full next state, including preserved registers
and flags. Permission failure produces no partial next-state observation. -/
theorem execute_storeIntent_next_iff {initial final : State} {instruction : Instruction}
    {address : Word} {value : BitVec 32} {af : Bool} {reads : List Read}
    (intent : instruction.storeIntent initial = some (address, value)) :
    execute initial instruction af = .ok ⟨.next final, reads⟩ ↔
      canStoreDWord initial.memory address = true ∧
      final = { initial with
        memory := writeDWordUnchecked initial.memory address value
        rip := initial.rip + BitVec.ofNat 64 instruction.length } ∧ reads = [] := by
  rw [execute_storeIntent_checked af intent]
  cases canStoreDWord initial.memory address <;> simp [eq_comm]

/-- Successful ordinary stores preserve every byte outside their exact
four-byte footprint and both permission maps, and load back the source low32. -/
theorem execute_storeIntent_frame {initial final : State} {instruction : Instruction}
    {address : Word} {value : BitVec 32} {af : Bool} {observation : Observation}
    (intent : instruction.storeIntent initial = some (address, value))
    (success : execute initial instruction af = .ok observation)
    (next : observation.result = .next final) :
    final.registers = initial.registers ∧ final.flags = initial.flags ∧
      final.rip = initial.rip + BitVec.ofNat 64 instruction.length ∧
      loadDWord final.memory address = .ok value ∧
      (∀ query, 4 ≤ (query - address).toNat → final.memory.read query = initial.memory.read query) ∧
      final.memory.executable = initial.memory.executable ∧
      final.memory.writable = initial.memory.writable ∧ observation.reads = [] := by
  rw [execute_storeIntent_checked af intent] at success
  cases allowed : canStoreDWord initial.memory address with
  | false => simp [allowed] at success
  | true =>
    simp only [allowed, ↓reduceIte, Except.ok.injEq] at success
    cases success
    cases next
    refine ⟨rfl, rfl, rfl, (store_sound _ _ _ allowed).2, ?_, rfl, rfl, rfl⟩
    intro query outside
    exact writeDWord_frame initial.memory address query value outside

theorem execute_xorSelf32 (state : State) (destination : Register) (af : Bool) :
    execute state (.xorSelf32 destination) af =
      .ok ⟨.next { state.writeRegister destination 0 with
        rip := state.rip + 2, flags := logicalFlags32 state.flags 0 af }, []⟩ := rfl

theorem execute_test64 (state : State) (left right : Register) (af : Bool) :
    execute state (.test64 left right) af =
      .ok ⟨.next { state with
        rip := state.rip + 3
        flags := logicalFlags64 state.flags (state.registers left &&& state.registers right) af }, []⟩ := rfl

theorem execute_cmp64 (state : State) (left right : Register) (af : Bool) :
    execute state (.cmp64 left right) af =
      .ok ⟨.next { state with
        rip := state.rip + 3
        flags := cmpFlags64 state.flags (state.registers left) (state.registers right) }, []⟩ := rfl

theorem execute_addMem32 (state : State) (destination : Register) (address : Address) (af : Bool) :
    execute state (.addMem32 destination address) af = do
      let value ← loadDWord state.memory (address.eval state)
      let left := (state.registers destination).setWidth 32
      return ⟨.next { state.writeRegister destination ((left + value).setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (Instruction.addMem32 destination address).length,
        flags := addFlags32 state.flags left value }, [⟨.data, address.eval state, 4⟩]⟩ := rfl

theorem execute_addImm64 (state : State) (destination : Register) (immediate : Byte) (af : Bool) :
    execute state (.addImm64 destination immediate) af =
      .ok ⟨.next { state.writeRegister destination (state.registers destination + immediate.signExtend 64) with
        rip := state.rip + 4,
        flags := addFlags64 state.flags (state.registers destination) (immediate.signExtend 64) }, []⟩ := rfl

theorem execute_inc64 (state : State) (destination : Register) (af : Bool) :
    execute state (.inc64 destination) af =
      .ok ⟨.next { state.writeRegister destination (state.registers destination + 1) with
        rip := state.rip + 3, flags := incFlags64 state.flags (state.registers destination) }, []⟩ := rfl

theorem execute_dec64 (state : State) (destination : Register) (af : Bool) :
    execute state (.dec64 destination) af =
      .ok ⟨.next { state.writeRegister destination (state.registers destination - 1) with
        rip := state.rip + 3, flags := decFlags64 state.flags (state.registers destination) }, []⟩ := rfl

theorem execute_je (state : State) (displacement : Byte) (af : Bool) :
    execute state (.je displacement) af = do
      return ⟨.next (← executeShortBranch state (state.flags.getLsbD 6) displacement), []⟩ := rfl

theorem execute_jmp (state : State) (displacement : Byte) (af : Bool) :
    execute state (.jmp displacement) af = do
      return ⟨.next (← executeShortBranch state true displacement), []⟩ := rfl

/-- Observation footprints cannot be supplied independently of execution. -/
theorem execute_reads {state : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (success : execute state instruction af = .ok observation) :
    observation.reads = instruction.operandReads state := by
  cases instruction with
  | legacy old =>
    cases result : X86.executeInstruction state old <;> simp only [execute, result, ok_bind, error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at success
    cases success
    rfl
  | loadMem32 destination address | addMem32 destination address =>
    cases loaded : loadDWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success
    rfl
  | storeMem32 address source =>
    cases stored : storeDWord state.memory (address.eval state) ((state.registers source).setWidth 32) <;>
      simp [execute, stored] at success
    cases success
    rfl
  | je displacement =>
    cases result : executeShortBranch state (state.flags.getLsbD 6) displacement <;>
      simp only [execute, result, ok_bind, error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at success
    cases success
    rfl
  | jmp displacement =>
    cases result : executeShortBranch state true displacement <;> simp only [execute, result, ok_bind, error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at success
    cases success
    rfl
  | movReg32 destination source | movReg64 destination source
  | xorSelf32 destination | test64 left right | cmp64 left right
  | addImm64 destination immediate | inc64 destination | dec64 destination =>
    cases success
    rfl

private theorem legacy_reads_succeed {state : State} {instruction : X86.Instruction}
    {result : StepResult} (success : X86.executeInstruction state instruction = .ok result) :
    ∀ read ∈ (Instruction.legacy instruction).operandReads state, OperandReadSucceeds state read := by
  cases instruction with
  | ret =>
    cases loaded : readWord state.memory (state.registers .rsp) with
    | error fault => simp [X86.executeInstruction, executeRet, loaded] at success
    | ok value =>
      intro read member
      simp only [Instruction.operandReads, List.mem_singleton] at member
      subst read
      exact ⟨rfl, value, loaded⟩
  | loadEaxRdi =>
    cases loaded : loadDWord state.memory (state.registers .rdi) with
    | error fault => simp [X86.executeInstruction, executeLoad, loaded] at success
    | ok value =>
      intro read member
      simp only [Instruction.operandReads, List.mem_singleton] at member
      subst read
      exact ⟨rfl, value, loaded⟩
  | loadEaxRsi =>
    cases loaded : loadDWord state.memory (state.registers .rsi) with
    | error fault => simp [X86.executeInstruction, executeLoadRsi, loaded] at success
    | ok value =>
      intro read member
      simp only [Instruction.operandReads, List.mem_singleton] at member
      subst read
      exact ⟨rfl, value, loaded⟩
  | exchangeEaxRdi =>
    cases executed : executeExchange state with
    | error fault => simp [X86.executeInstruction, executed] at success
    | ok output =>
      intro read member
      simp only [Instruction.operandReads, List.mem_singleton] at member
      subst read
      refine ⟨rfl, output.1.before, ?_⟩
      rw [←(executeExchange_sound executed).2.1]
      exact (executeExchange_sound executed).1.2.2.1
  | fetchAddEaxRdi =>
    cases executed : executeFetchAdd state with
    | error fault => simp [X86.executeInstruction, executed] at success
    | ok output =>
      intro read member
      simp only [Instruction.operandReads, List.mem_singleton] at member
      subst read
      refine ⟨rfl, output.1.before, ?_⟩
      rw [←(executeFetchAdd_sound executed).2.1]
      exact (executeFetchAdd_sound executed).1.2.2.1
  | leaEaxRdiDisp8 _ | leaEaxRaxDisp8 _ | movEaxEdi | movEaxEsi | jrcxz _ | loopRcx _
  | jnz _ | cmpEaxZero | storeEsiRdi | storeEaxRsi | mov32 _ _ | syscall =>
    simp [Instruction.operandReads]

theorem execute_reads_succeed {state : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (success : execute state instruction af = .ok observation) :
    ∀ read ∈ observation.reads, OperandReadSucceeds state read := by
  rw [execute_reads success]
  cases instruction with
  | legacy old =>
    cases executed : X86.executeInstruction state old with
    | error fault => simp [execute, executed] at success
    | ok result => exact legacy_reads_succeed executed
  | loadMem32 destination address | addMem32 destination address =>
    cases loaded : loadDWord state.memory (address.eval state) with
    | error fault => simp [execute, loaded] at success
    | ok value =>
      intro read member
      simp only [Instruction.operandReads, List.mem_singleton] at member
      subst read
      exact ⟨rfl, value, loaded⟩
  | movReg32 _ _ | movReg64 _ _ | storeMem32 _ _ | xorSelf32 _ | test64 _ _ | cmp64 _ _
  | addImm64 _ _ | inc64 _ | dec64 _ | je _ | jmp _ =>
    simp [Instruction.operandReads]

/-- New operations with no store intent preserve the full memory, including
its permission maps. Ordinary MOV stores require their checked-store contract. -/
theorem execute_new_memory {state final : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (newInstruction : instruction.isNew = true)
    (noStore : instruction.storeIntent state = none)
    (success : execute state instruction af = .ok observation)
    (next : observation.result = .next final) : final.memory = state.memory := by
  cases instruction with
  | legacy old => simp [Instruction.isNew] at newInstruction
  | movReg32 destination source | movReg64 destination source
  | xorSelf32 destination | test64 left right | cmp64 left right
  | addImm64 destination immediate | inc64 destination | dec64 destination =>
    cases success
    cases next
    rfl
  | loadMem32 destination address | addMem32 destination address =>
    cases loaded : loadDWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success
    cases next
    rfl
  | storeMem32 address source => simp [Instruction.storeIntent] at noStore
  | je displacement =>
    cases branched : executeShortBranch state (state.flags.getLsbD 6) displacement with
    | error fault => simp only [execute, branched, error_bind, reduceCtorEq] at success
    | ok result =>
      simp only [execute, branched, ok_bind, pure_ok, Except.ok.injEq] at success
      cases success
      cases next
      exact executeShortBranch_memory branched
  | jmp displacement =>
    cases branched : executeShortBranch state true displacement with
    | error fault => simp only [execute, branched, error_bind, reduceCtorEq] at success
    | ok result =>
      simp only [execute, branched, ok_bind, pure_ok, Except.ok.injEq] at success
      cases success
      cases next
      exact executeShortBranch_memory branched

/-- Every success of the legacy machine transfers its entire outcome, not just
an observation projection of registers or flags. -/
theorem step_legacy {state : State} {instruction : X86.Instruction} (af : Bool)
    (decoded : X86.decodeAt state = .ok instruction) :
    step af state =
      (fun result => Observation.mk result ((Instruction.legacy instruction).operandReads state)) <$>
        X86.step state := by
  rw [step_eq_execute af (decodeAt_legacy decoded), execute_legacy,
    X86.step_eq_executeInstruction state instruction decoded]

/-- New stores are ordinary sequential writes, with no locked outcome. -/
theorem Instruction.new_unlocked (instruction : Instruction)
    (newInstruction : instruction.isNew = true) :
    instruction.isLocked = false := by
  cases instruction <;> simp_all [Instruction.isNew, Instruction.isLocked]

theorem Instruction.new_effects (instruction : Instruction) (state : State)
    (newInstruction : instruction.isNew = true) (noStore : instruction.storeIntent state = none) :
    instruction.storeIntent state = none ∧ instruction.isLocked = false :=
  ⟨noStore, instruction.new_unlocked newInstruction⟩

theorem execute_af_independent (state : State) (instruction : Instruction) (left right : Bool)
    (noChoice : instruction.choosesAF = false) :
    execute state instruction left = execute state instruction right := by
  cases instruction <;> first | rfl | simp [Instruction.choosesAF] at noChoice

theorem execute_new_next {state : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (newInstruction : instruction.isNew = true)
    (success : execute state instruction af = .ok observation) :
    ∃ final, observation.result = .next final := by
  cases instruction with
  | legacy old => simp [Instruction.isNew] at newInstruction
  | movReg32 destination source | movReg64 destination source
  | xorSelf32 destination | test64 left right | cmp64 left right
  | addImm64 destination immediate | inc64 destination | dec64 destination =>
    cases success
    exact ⟨_, rfl⟩
  | loadMem32 destination address | addMem32 destination address =>
    cases loaded : loadDWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success
    exact ⟨_, rfl⟩
  | storeMem32 address source =>
    cases stored : storeDWord state.memory (address.eval state) ((state.registers source).setWidth 32) <;>
      simp [execute, stored] at success
    cases success
    exact ⟨_, rfl⟩
  | je displacement =>
    cases branched : executeShortBranch state (state.flags.getLsbD 6) displacement with
    | error fault => simp only [execute, branched, error_bind, reduceCtorEq] at success
    | ok result =>
      simp only [execute, branched, ok_bind, pure_ok, Except.ok.injEq] at success
      cases success
      exact ⟨_, rfl⟩
  | jmp displacement =>
    cases branched : executeShortBranch state true displacement with
    | error fault => simp only [execute, branched, error_bind, reduceCtorEq] at success
    | ok result =>
      simp only [execute, branched, ok_bind, pure_ok, Except.ok.injEq] at success
      cases success
      exact ⟨_, rfl⟩

theorem shortBranch_flags {initial final : State} {taken : Bool} {displacement : Byte}
    (success : executeShortBranch initial taken displacement = .ok final) :
    final.flags = initial.flags := by
  unfold executeShortBranch at success
  split at success
  · dsimp only at success
    split at success
    · cases success; rfl
    · cases success
  · cases success; rfl

/-- Full preservation of ALL bits outside the six arithmetic status flags, not
just a selected ABI flag. INC/DEC additionally preserve CF (see their bit lemmas). -/
theorem execute_new_flags {state final : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (newInstruction : instruction.isNew = true)
    (success : execute state instruction af = .ok observation)
    (next : observation.result = .next final) :
    final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask := by
  cases instruction with
  | legacy old => simp [Instruction.isNew] at newInstruction
  | movReg32 destination source | movReg64 destination source =>
    cases success; cases next
    rfl
  | loadMem32 destination address =>
    cases loaded : loadDWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success; cases next
    rfl
  | storeMem32 address source =>
    cases stored : storeDWord state.memory (address.eval state) ((state.registers source).setWidth 32) <;>
      simp [execute, stored] at success
    cases success; cases next
    rfl
  | xorSelf32 destination =>
    cases success; cases next
    exact logicalFlags32_preserves ..
  | test64 left right =>
    cases success; cases next
    exact logicalFlags64_preserves ..
  | cmp64 left right =>
    cases success; cases next
    exact cmpFlags64_preserves ..
  | addImm64 destination immediate =>
    cases success; cases next
    exact addFlags64_preserves ..
  | inc64 destination =>
    cases success; cases next
    exact incFlags64_preserves ..
  | dec64 destination =>
    cases success; cases next
    exact decFlags64_preserves ..
  | addMem32 destination address =>
    cases loaded : loadDWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success; cases next
    exact addFlags32_preserves ..
  | je displacement =>
    cases branched : executeShortBranch state (state.flags.getLsbD 6) displacement with
    | error fault => simp only [execute, branched, error_bind, reduceCtorEq] at success
    | ok result =>
      simp only [execute, branched, ok_bind, pure_ok, Except.ok.injEq] at success
      cases success; cases next
      rw [shortBranch_flags branched]
  | jmp displacement =>
    cases branched : executeShortBranch state true displacement with
    | error fault => simp only [execute, branched, error_bind, reduceCtorEq] at success
    | ok result =>
      simp only [execute, branched, ok_bind, pure_ok, Except.ok.injEq] at success
      cases success; cases next
      rw [shortBranch_flags branched]

end EDSL.X86.Sequential
