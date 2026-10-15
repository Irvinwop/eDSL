/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.AtomicMemory
import EDSL.X86.Flags
import EDSL.X86.Syscall

namespace EDSL.X86

inductive Instruction where
  /-- `8D 47 ib`: LEA EAX, [RDI + sign_extend(disp8)], default 64-bit address size. -/
  | leaEaxRdiDisp8 (displacement : Byte)
  /-- `8D 40 ib`: LEA EAX, [RAX + sign_extend(disp8)]. -/
  | leaEaxRaxDisp8 (displacement : Byte)
  /-- `89 F8`: MOV EAX, EDI. -/
  | movEaxEdi
  /-- `89 F0`: MOV EAX, ESI. -/
  | movEaxEsi
  /-- `87 07`: XCHG DWORD PTR [RDI], EAX; memory form is implicitly locked. -/
  | exchangeEaxRdi
  /-- `F0 0F C1 07`: LOCK XADD DWORD PTR [RDI], EAX. -/
  | fetchAddEaxRdi
  /-- `E3 cb`: JRCXZ rel8 with default 64-bit address size. -/
  | jrcxz (displacement : Byte)
  /-- `E2 cb`: LOOP rel8 using full RCX, with no flags dependence. -/
  | loopRcx (displacement : Byte)
  /-- `75 cb`: JNE/JNZ rel8, taken exactly when ZF is clear. -/
  | jnz (displacement : Byte)
  /-- `83 F8 00`: CMP EAX, sign_extend(0), default 32-bit operand size. -/
  | cmpEaxZero
  /-- `8B 07`: MOV EAX, DWORD PTR [RDI]. -/
  | loadEaxRdi
  /-- `8B 06`: MOV EAX, DWORD PTR [RSI]. -/
  | loadEaxRsi
  /-- `89 37`: MOV DWORD PTR [RDI], ESI. -/
  | storeEsiRdi
  /-- `89 06`: MOV DWORD PTR [RSI], EAX. -/
  | storeEaxRsi
  /-- `B8/BA/BE/BF id`: supported 32-bit immediate register writes. -/
  | mov32 (destination : Register) (value : BitVec 32)
  /-- `0F 05`: userspace syscall request; privileged execution is external. -/
  | syscall
  /-- `C3`: near return, with an accessible stack word and canonical target. -/
  | ret
  deriving DecidableEq, Repr

/-- The address and low 32-bit value of an ordinary store. This is an intent,
not permission to write: execution still validates all four destination bytes.
Locked RMWs have no ordinary store intent. -/
def Instruction.storeIntent (instruction : Instruction) (state : State) :
    Option (Word × BitVec 32) :=
  match instruction with
  | .storeEsiRdi => some (state.registers .rdi, (state.registers .rsi).setWidth 32)
  | .storeEaxRsi => some (state.registers .rsi, (state.registers .rax).setWidth 32)
  | _ => none

/-- These decoded operations require an indivisible locked RMW transition. -/
def Instruction.isLocked (instruction : Instruction) : Bool :=
  match instruction with
  | .exchangeEaxRdi | .fetchAddEaxRdi => true
  | _ => false

theorem Instruction.storeIntent_eq_some_iff (instruction : Instruction) (state : State)
    (address : Word) (value : BitVec 32) :
    instruction.storeIntent state = some (address, value) ↔
      (instruction = .storeEsiRdi ∧ address = state.registers .rdi ∧
        value = (state.registers .rsi).setWidth 32) ∨
      (instruction = .storeEaxRsi ∧ address = state.registers .rsi ∧
        value = (state.registers .rax).setWidth 32) := by
  cases instruction <;> simp [Instruction.storeIntent, eq_comm]

theorem Instruction.storeIntent_eq_none_iff (instruction : Instruction) (state : State) :
    instruction.storeIntent state = none ↔
      instruction ≠ .storeEsiRdi ∧ instruction ≠ .storeEaxRsi := by
  cases instruction <;> simp [Instruction.storeIntent]

theorem Instruction.isLocked_eq_true_iff (instruction : Instruction) :
    instruction.isLocked = true ↔
      instruction = .exchangeEaxRdi ∨ instruction = .fetchAddEaxRdi := by
  cases instruction <;> simp [Instruction.isLocked]

theorem Instruction.storeIntent_none_of_isLocked (instruction : Instruction) (state : State)
    (locked : instruction.isLocked = true) : instruction.storeIntent state = none := by
  rcases (instruction.isLocked_eq_true_iff).mp locked with rfl | rfl <;> rfl

def decodeAt (state : State) : Except Error Instruction := do
  let opcode ← fetchByte state.memory state.rip
  if opcode = 0xc3 then
    return .ret
  else if opcode = 0x8d then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm ≠ 0x47 ∧ modrm ≠ 0x40 then
      throw .unsupportedEncoding
    let displacement ← fetchByte state.memory (state.rip + 2)
    return if modrm = 0x47 then .leaEaxRdiDisp8 displacement else .leaEaxRaxDisp8 displacement
  else if opcode = 0x8b then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm = 0x07 then return .loadEaxRdi
    else if modrm = 0x06 then return .loadEaxRsi
    else throw .unsupportedEncoding
  else if opcode = 0x89 then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm = 0x37 then return .storeEsiRdi
    else if modrm = 0x06 then return .storeEaxRsi
    else if modrm = 0xf8 then return .movEaxEdi
    else if modrm = 0xf0 then return .movEaxEsi
    else throw .unsupportedEncoding
  else if opcode = 0x87 then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm ≠ 0x07 then throw .unsupportedEncoding
    return .exchangeEaxRdi
  else if opcode = 0xf0 then
    let escape ← fetchByte state.memory (state.rip + 1)
    if escape ≠ 0x0f then throw .unsupportedEncoding
    let operation ← fetchByte state.memory (state.rip + 2)
    if operation ≠ 0xc1 then throw .unsupportedEncoding
    let modrm ← fetchByte state.memory (state.rip + 3)
    if modrm ≠ 0x07 then throw .unsupportedEncoding
    return .fetchAddEaxRdi
  else if opcode = 0xe3 ∨ opcode = 0xe2 then
    let displacement ← fetchByte state.memory (state.rip + 1)
    return if opcode = 0xe3 then .jrcxz displacement else .loopRcx displacement
  else if opcode = 0x75 then
    return .jnz (← fetchByte state.memory (state.rip + 1))
  else if opcode = 0x83 then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm ≠ 0xf8 then throw .unsupportedEncoding
    let immediate ← fetchByte state.memory (state.rip + 2)
    if immediate ≠ 0 then throw .unsupportedEncoding
    return .cmpEaxZero
  else if opcode = 0xb8 ∨ opcode = 0xba ∨ opcode = 0xbe ∨ opcode = 0xbf then
    let b0 ← fetchByte state.memory (state.rip + 1)
    let b1 ← fetchByte state.memory (state.rip + 2)
    let b2 ← fetchByte state.memory (state.rip + 3)
    let b3 ← fetchByte state.memory (state.rip + 4)
    let destination := if opcode = 0xb8 then .rax else if opcode = 0xba then .rdx
      else if opcode = 0xbe then .rsi else .rdi
    return .mov32 destination (joinDWord b0 b1 b2 b3)
  else if opcode = 0x0f then
    let second ← fetchByte state.memory (state.rip + 1)
    if second ≠ 0x05 then throw .unsupportedEncoding
    return .syscall
  else
    throw (.unsupportedOpcode opcode)

def executeLea (state : State) (displacement : Byte) : State :=
  let address := state.registers .rdi + displacement.signExtend 64
  let result := (address.setWidth 32).setWidth 64
  { state.writeRegister .rax result with rip := state.rip + 3 }

def executeLoad (state : State) : Except Error State := do
  let value ← loadDWord state.memory (state.registers .rdi)
  return { state.writeRegister .rax (value.setWidth 64) with rip := state.rip + 2 }

def executeStore (state : State) : Except Error State := do
  let memory ← storeDWord state.memory (state.registers .rdi) ((state.registers .rsi).setWidth 32)
  return { state with memory := memory, rip := state.rip + 2 }

def executeLoadRsi (state : State) : Except Error State := do
  let value ← loadDWord state.memory (state.registers .rsi)
  return { state.writeRegister .rax (value.setWidth 64) with rip := state.rip + 2 }

def executeStoreRsi (state : State) : Except Error State := do
  let memory ← storeDWord state.memory (state.registers .rsi) ((state.registers .rax).setWidth 32)
  return { state with memory := memory, rip := state.rip + 2 }

def executeCmpEaxZero (state : State) : State :=
  { state with
    rip := state.rip + 3
    flags := cmpZeroFlags32 state.flags ((state.registers .rax).setWidth 32) }

def executeMov32 (state : State) (destination : Register) (value : BitVec 32) : State :=
  { state.writeRegister destination (value.setWidth 64) with rip := state.rip + 5 }

def executeLeaRax (state : State) (displacement : Byte) : State :=
  { state.writeRegister .rax
      (((state.registers .rax + displacement.signExtend 64).setWidth 32).setWidth 64)
    with rip := state.rip + 3 }

def executeMovEaxEdi (state : State) : State :=
  { state.writeRegister .rax (((state.registers .rdi).setWidth 32).setWidth 64)
    with rip := state.rip + 2 }

def executeMovEaxEsi (state : State) : State :=
  { state.writeRegister .rax (((state.registers .rsi).setWidth 32).setWidth 64)
    with rip := state.rip + 2 }

def executeExchange (state : State) : Except Error (AtomicEvent × State) := do
  let result ← exchangeDWord state.memory (state.registers .rdi) ((state.registers .rax).setWidth 32)
  return (⟨state.registers .rdi, result.2, (state.registers .rax).setWidth 32⟩,
    { state.writeRegister .rax (result.2.setWidth 64) with memory := result.1, rip := state.rip + 2 })

theorem executeExchange_sound {initial : State} {result : AtomicEvent × State}
    (success : executeExchange initial = .ok result) :
    ExchangeTransition initial.memory result.1 result.2.memory ∧
    result.1.address = initial.registers .rdi ∧
    result.1.after = (initial.registers .rax).setWidth 32 ∧
    result.2.registers .rax = result.1.before.setWidth 64 ∧
    result.2.flags = initial.flags ∧ result.2.rip = initial.rip + 2 := by
  cases exchanged : exchangeDWord initial.memory (initial.registers .rdi) ((initial.registers .rax).setWidth 32) with
  | error fault => simp [executeExchange, exchanged] at success
  | ok output =>
    simp [executeExchange, exchanged] at success
    subst result
    exact ⟨exchangeDWord_ok _ _ _ _ exchanged, rfl, rfl, by simp [State.writeRegister], rfl, rfl⟩

theorem executeExchange_preserves_rdi {initial : State} {result : AtomicEvent × State}
    (success : executeExchange initial = .ok result) : result.2.registers .rdi = initial.registers .rdi := by
  cases exchanged : exchangeDWord initial.memory (initial.registers .rdi) ((initial.registers .rax).setWidth 32) with
  | error fault => simp [executeExchange, exchanged] at success
  | ok output =>
    simp [executeExchange, exchanged] at success
    subst result
    simp [State.writeRegister]

def executeFetchAdd (state : State) : Except Error (AtomicEvent × State) := do
  let delta := (state.registers .rax).setWidth 32
  let result ← fetchAddDWord state.memory (state.registers .rdi) delta
  return (⟨state.registers .rdi, result.2, result.2 + delta⟩,
    { state.writeRegister .rax (result.2.setWidth 64) with
      memory := result.1, rip := state.rip + 4, flags := addFlags32 state.flags result.2 delta })

theorem executeFetchAdd_sound {initial : State} {result : AtomicEvent × State}
    (success : executeFetchAdd initial = .ok result) :
    ExchangeTransition initial.memory result.1 result.2.memory ∧
    result.1.address = initial.registers .rdi ∧
    result.1.after = result.1.before + (initial.registers .rax).setWidth 32 ∧
    result.2.registers .rax = result.1.before.setWidth 64 ∧
    result.2.flags = addFlags32 initial.flags result.1.before ((initial.registers .rax).setWidth 32) ∧
    result.2.rip = initial.rip + 4 := by
  cases added : fetchAddDWord initial.memory (initial.registers .rdi) ((initial.registers .rax).setWidth 32) with
  | error fault => simp [executeFetchAdd, added] at success
  | ok output =>
    simp [executeFetchAdd, added] at success
    subst result
    exact ⟨fetchAddDWord_ok _ _ _ _ added, rfl, rfl, by simp [State.writeRegister], rfl, rfl⟩

theorem executeFetchAdd_preserves_rdi {initial : State} {result : AtomicEvent × State}
    (success : executeFetchAdd initial = .ok result) : result.2.registers .rdi = initial.registers .rdi := by
  cases added : fetchAddDWord initial.memory (initial.registers .rdi) ((initial.registers .rax).setWidth 32) with
  | error fault => simp [executeFetchAdd, added] at success
  | ok output =>
    simp [executeFetchAdd, added] at success
    subst result
    simp [State.writeRegister]

/-- Relative displacements are signed and measured from the next instruction.
Only taken targets need this canonicality check. Prefixes are unsupported. -/
def executeShortBranch (state : State) (taken : Bool) (displacement : Byte) : Except Error State :=
  if taken then
    let target := state.rip + 2 + displacement.signExtend 64
    if canonical target then .ok { state with rip := target }
    else .error (.noncanonicalBranch target)
  else .ok { state with rip := state.rip + 2 }

def executeJrcxz (state : State) (displacement : Byte) : Except Error State :=
  executeShortBranch state (decide (state.registers .rcx = 0)) displacement

def executeJnz (state : State) (displacement : Byte) : Except Error State :=
  executeShortBranch state (!state.flags.getLsbD 6) displacement

theorem executeJnz_afterCmp (state : State) (displacement : Byte) :
    executeJnz (executeCmpEaxZero state) displacement =
      executeShortBranch (executeCmpEaxZero state)
        (decide ((state.registers .rax).setWidth 32 ≠ 0)) displacement := by
  unfold executeJnz
  have zero := (cmpZeroFlags32_bits state.flags ((state.registers .rax).setWidth 32)).2.2.2.1
  simp only [executeCmpEaxZero] at zero ⊢
  rw [zero]
  simp [Bool.beq_eq_decide_eq]

/-- LOOP decrements modulo 2^64 before testing; a zero entry wraps to all ones.
It preserves every flag and does not test ZF. -/
def executeLoop (state : State) (displacement : Byte) : Except Error State :=
  let count := state.registers .rcx - 1
  executeShortBranch (state.writeRegister .rcx count) (decide (count ≠ 0)) displacement

theorem executeShortBranch_registers {initial final : State} {taken : Bool} {displacement : Byte}
    (success : executeShortBranch initial taken displacement = .ok final) :
    final.registers = initial.registers := by
  unfold executeShortBranch at success
  split at success
  · dsimp only at success
    split at success
    · cases success; rfl
    · cases success
  · cases success; rfl

theorem executeShortBranch_memory {initial final : State} {taken : Bool} {displacement : Byte}
    (success : executeShortBranch initial taken displacement = .ok final) :
    final.memory = initial.memory := by
  unfold executeShortBranch at success
  split at success
  · dsimp only at success
    split at success
    · cases success; rfl
    · cases success
  · cases success; rfl

def executeRet (state : State) : Except Error State := do
  let target ← readWord state.memory (state.registers .rsp)
  if canonical target then
    return { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target }
  else
    throw (.noncanonicalReturn target)

inductive StepResult where
  | next (state : State)
  | atomic (event : AtomicEvent) (state : State)
  | returned (state : State)
  | syscall (request : SyscallRequest)

/- Simplification can turn a reducible execution branch's bind/pure into a map.
Keep constructor outcomes reducible without eagerly unfolding unknown decoded
instructions in callers' execution-inversion proofs. -/
@[simp] theorem except_map_ok (function : α → β) (value : α) :
    function <$> (Except.ok value : Except ε α) = .ok (function value) := rfl

@[simp] theorem except_map_error (function : α → β) (fault : ε) :
    function <$> (Except.error fault : Except ε α) = .error fault := rfl

/-- Execute a supplied decoded instruction. Instruction fetch is deliberately
separate from this state's data memory, so a caller can decode shared code and
execute using a store-buffer-forwarded data view. Reducibility preserves the
existing definitional execution interface of `step`. -/
abbrev executeInstruction (state : State) (instruction : Instruction) : Except Error StepResult := do
  match instruction with
  | .leaEaxRdiDisp8 displacement => return .next (executeLea state displacement)
  | .leaEaxRaxDisp8 displacement => return .next (executeLeaRax state displacement)
  | .movEaxEdi => return .next (executeMovEaxEdi state)
  | .movEaxEsi => return .next (executeMovEaxEsi state)
  | .exchangeEaxRdi =>
    let result ← executeExchange state
    return .atomic result.1 result.2
  | .fetchAddEaxRdi =>
    let result ← executeFetchAdd state
    return .atomic result.1 result.2
  | .jrcxz displacement => return .next (← executeJrcxz state displacement)
  | .loopRcx displacement => return .next (← executeLoop state displacement)
  | .jnz displacement => return .next (← executeJnz state displacement)
  | .cmpEaxZero => return .next (executeCmpEaxZero state)
  | .loadEaxRdi => return .next (← executeLoad state)
  | .loadEaxRsi => return .next (← executeLoadRsi state)
  | .storeEsiRdi => return .next (← executeStore state)
  | .storeEaxRsi => return .next (← executeStoreRsi state)
  | .mov32 destination value => return .next (executeMov32 state destination value)
  | .syscall => return .syscall ⟨state, state.rip + 2⟩
  | .ret => return .returned (← executeRet state)

def step (state : State) : Except Error StepResult := do
  let instruction ← decodeAt state
  executeInstruction state instruction

theorem step_eq_executeInstruction (state : State) (instruction : Instruction)
    (decoded : decodeAt state = .ok instruction) :
    step state = executeInstruction state instruction := by
  simp only [step, decoded, ok_bind]

/-- Complete ordinary-store outcome, including the existing permission failure,
unchanged registers/flags, two-byte PC advance and exact four-byte update. -/
theorem executeInstruction_storeEsiRdi (state : State) :
    executeInstruction state .storeEsiRdi =
      if canStoreDWord state.memory (state.registers .rdi) then
        .ok (.next { state with
          memory := writeDWordUnchecked state.memory (state.registers .rdi)
            ((state.registers .rsi).setWidth 32)
          rip := state.rip + 2 })
      else .error (.writeDenied (state.registers .rdi)) := by
  cases allowed : canStoreDWord state.memory (state.registers .rdi) <;>
    simp [executeInstruction, executeStore, storeDWord, allowed]

theorem executeInstruction_storeEaxRsi (state : State) :
    executeInstruction state .storeEaxRsi =
      if canStoreDWord state.memory (state.registers .rsi) then
        .ok (.next { state with
          memory := writeDWordUnchecked state.memory (state.registers .rsi)
            ((state.registers .rax).setWidth 32)
          rip := state.rip + 2 })
      else .error (.writeDenied (state.registers .rsi)) := by
  cases allowed : canStoreDWord state.memory (state.registers .rsi) <;>
    simp [executeInstruction, executeStoreRsi, storeDWord, allowed]

/-- A scheduler can use the classified intent without reimplementing either
ordinary store's execution or validation. -/
theorem executeInstruction_storeIntent {state : State} {instruction : Instruction}
    {address : Word} {value : BitVec 32}
    (intent : instruction.storeIntent state = some (address, value)) :
    executeInstruction state instruction =
      if canStoreDWord state.memory address then
        .ok (.next { state with
          memory := writeDWordUnchecked state.memory address value
          rip := state.rip + 2 })
      else .error (.writeDenied address) := by
  rcases (instruction.storeIntent_eq_some_iff state address value).mp intent with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact executeInstruction_storeEsiRdi state
  · exact executeInstruction_storeEaxRsi state

theorem executeInstruction_storeIntent_next_iff {initial final : State} {instruction : Instruction}
    {address : Word} {value : BitVec 32}
    (intent : instruction.storeIntent initial = some (address, value)) :
    executeInstruction initial instruction = .ok (.next final) ↔
      canStoreDWord initial.memory address = true ∧
      final = { initial with
        memory := writeDWordUnchecked initial.memory address value
        rip := initial.rip + 2 } := by
  rw [executeInstruction_storeIntent intent]
  cases canStoreDWord initial.memory address <;> simp [eq_comm]

/-- Successful ordinary non-writing execution preserves the entire data memory,
including permissions. Loads and RET still read this state's data view; locked
RMW outcomes are deliberately excluded by the result constructors. -/
theorem executeInstruction_ordinary_memory {initial final : State} {instruction : Instruction}
    (noStore : instruction.storeIntent initial = none)
    (transition : executeInstruction initial instruction = .ok (.next final) ∨
      executeInstruction initial instruction = .ok (.returned final)) :
    final.memory = initial.memory := by
  cases instruction with
  | leaEaxRdiDisp8 displacement | leaEaxRaxDisp8 displacement
  | movEaxEdi | movEaxEsi | cmpEaxZero | mov32 destination value =>
    simp [executeInstruction] at transition
    subst final
    rfl
  | exchangeEaxRdi =>
    cases result : executeExchange initial <;> simp [executeInstruction, result] at transition
  | fetchAddEaxRdi =>
    cases result : executeFetchAdd initial <;> simp [executeInstruction, result] at transition
  | jrcxz displacement =>
    cases result : executeJrcxz initial displacement with
    | error fault => simp [executeInstruction, result] at transition
    | ok next =>
      simp [executeInstruction, result] at transition
      subst final
      exact executeShortBranch_memory result
  | loopRcx displacement =>
    cases result : executeLoop initial displacement with
    | error fault => simp [executeInstruction, result] at transition
    | ok next =>
      simp [executeInstruction, result] at transition
      subst final
      exact executeShortBranch_memory
        (initial := initial.writeRegister .rcx (initial.registers .rcx - 1)) result
  | jnz displacement =>
    cases result : executeJnz initial displacement with
    | error fault => simp [executeInstruction, result] at transition
    | ok next =>
      simp [executeInstruction, result] at transition
      subst final
      exact executeShortBranch_memory result
  | loadEaxRdi =>
    cases loaded : loadDWord initial.memory (initial.registers .rdi) with
    | error fault => simp [executeInstruction, executeLoad, loaded] at transition
    | ok value =>
      simp [executeInstruction, executeLoad, loaded] at transition
      subst final
      rfl
  | loadEaxRsi =>
    cases loaded : loadDWord initial.memory (initial.registers .rsi) with
    | error fault => simp [executeInstruction, executeLoadRsi, loaded] at transition
    | ok value =>
      simp [executeInstruction, executeLoadRsi, loaded] at transition
      subst final
      rfl
  | storeEsiRdi | storeEaxRsi => simp [Instruction.storeIntent] at noStore
  | syscall => simp [executeInstruction] at transition
  | ret =>
    cases stack : readWord initial.memory (initial.registers .rsp) with
    | error fault => simp [executeInstruction, executeRet, stack] at transition
    | ok target =>
      cases valid : canonical target <;>
        simp [executeInstruction, executeRet, stack, valid] at transition
      subst final
      rfl

theorem executeInstruction_next_memory {initial final : State} {instruction : Instruction}
    (noStore : instruction.storeIntent initial = none)
    (transition : executeInstruction initial instruction = .ok (.next final)) :
    final.memory = initial.memory :=
  executeInstruction_ordinary_memory noStore (.inl transition)

theorem executeInstruction_returned_memory {initial final : State} {instruction : Instruction}
    (noStore : instruction.storeIntent initial = none)
    (transition : executeInstruction initial instruction = .ok (.returned final)) :
    final.memory = initial.memory :=
  executeInstruction_ordinary_memory noStore (.inr transition)

theorem executeInstruction_atomic_sound {initial final : State} {event : AtomicEvent}
    (transition : executeInstruction initial .exchangeEaxRdi = .ok (.atomic event final)) :
    ExchangeTransition initial.memory event final.memory ∧
    event.address = initial.registers .rdi ∧ event.after = (initial.registers .rax).setWidth 32 ∧
    final.registers .rax = event.before.setWidth 64 ∧
    final.flags = initial.flags ∧ final.rip = initial.rip + 2 := by
  cases result : executeExchange initial with
  | error fault => simp [executeInstruction, result] at transition
  | ok exchanged =>
    simp [executeInstruction, result] at transition
    rcases transition with ⟨rfl, rfl⟩
    exact executeExchange_sound result

theorem step_atomic_sound {initial final : State} {event : AtomicEvent}
    (decoded : decodeAt initial = .ok .exchangeEaxRdi)
    (transition : step initial = .ok (.atomic event final)) :
    ExchangeTransition initial.memory event final.memory ∧
    event.address = initial.registers .rdi ∧ event.after = (initial.registers .rax).setWidth 32 ∧
    final.registers .rax = event.before.setWidth 64 ∧
    final.flags = initial.flags ∧ final.rip = initial.rip + 2 := by
  rw [step_eq_executeInstruction initial .exchangeEaxRdi decoded] at transition
  exact executeInstruction_atomic_sound transition

theorem executeInstruction_fetchAdd_sound {initial final : State} {event : AtomicEvent}
    (transition : executeInstruction initial .fetchAddEaxRdi = .ok (.atomic event final)) :
    ExchangeTransition initial.memory event final.memory ∧
    event.address = initial.registers .rdi ∧ event.after = event.before + (initial.registers .rax).setWidth 32 ∧
    final.registers .rax = event.before.setWidth 64 ∧
    final.flags = addFlags32 initial.flags event.before ((initial.registers .rax).setWidth 32) ∧
    final.rip = initial.rip + 4 := by
  cases result : executeFetchAdd initial with
  | error fault => simp [executeInstruction, result] at transition
  | ok added =>
    simp [executeInstruction, result] at transition
    rcases transition with ⟨rfl, rfl⟩
    exact executeFetchAdd_sound result

theorem step_fetchAdd_sound {initial final : State} {event : AtomicEvent}
    (decoded : decodeAt initial = .ok .fetchAddEaxRdi)
    (transition : step initial = .ok (.atomic event final)) :
    ExchangeTransition initial.memory event final.memory ∧
    event.address = initial.registers .rdi ∧ event.after = event.before + (initial.registers .rax).setWidth 32 ∧
    final.registers .rax = event.before.setWidth 64 ∧
    final.flags = addFlags32 initial.flags event.before ((initial.registers .rax).setWidth 32) ∧
    final.rip = initial.rip + 4 := by
  rw [step_eq_executeInstruction initial .fetchAddEaxRdi decoded] at transition
  exact executeInstruction_fetchAdd_sound transition

/-- Common guarantees of every supported labeled RMW execution. Instruction-specific
replacement arithmetic, flags and length remain in the corresponding theorem. -/
theorem executeInstruction_atomic_transition {initial final : State} {event : AtomicEvent}
    {instruction : Instruction}
    (transition : executeInstruction initial instruction = .ok (.atomic event final)) :
    ExchangeTransition initial.memory event final.memory ∧ event.address = initial.registers .rdi ∧
      final.registers .rax = event.before.setWidth 64 := by
  cases instruction with
  | leaEaxRdiDisp8 displacement | leaEaxRaxDisp8 displacement
  | movEaxEdi | movEaxEsi | cmpEaxZero | mov32 destination value | syscall =>
    simp [executeInstruction] at transition
  | jrcxz displacement => cases result : executeJrcxz initial displacement <;> simp [executeInstruction, result] at transition
  | loopRcx displacement => cases result : executeLoop initial displacement <;> simp [executeInstruction, result] at transition
  | jnz displacement => cases result : executeJnz initial displacement <;> simp [executeInstruction, result] at transition
  | loadEaxRdi => cases result : executeLoad initial <;> simp [executeInstruction, result] at transition
  | loadEaxRsi => cases result : executeLoadRsi initial <;> simp [executeInstruction, result] at transition
  | storeEsiRdi => cases result : executeStore initial <;> simp [executeInstruction, result] at transition
  | storeEaxRsi => cases result : executeStoreRsi initial <;> simp [executeInstruction, result] at transition
  | ret => cases result : executeRet initial <;> simp [executeInstruction, result] at transition
  | exchangeEaxRdi =>
    have proof := executeInstruction_atomic_sound transition
    exact ⟨proof.1, proof.2.1, proof.2.2.2.1⟩
  | fetchAddEaxRdi =>
    have proof := executeInstruction_fetchAdd_sound transition
    exact ⟨proof.1, proof.2.1, proof.2.2.2.1⟩

theorem step_atomic_transition {initial final : State} {event : AtomicEvent}
    (transition : step initial = .ok (.atomic event final)) :
    ExchangeTransition initial.memory event final.memory ∧ event.address = initial.registers .rdi ∧
      final.registers .rax = event.before.setWidth 64 := by
  cases decoded : decodeAt initial with
  | error fault => simp [step, decoded] at transition
  | ok instruction =>
    rw [step_eq_executeInstruction initial instruction decoded] at transition
    exact executeInstruction_atomic_transition transition

structure Execution where
  state : State
  instructions : Nat

/-- Fuel bounds the supported evaluator, not a claim about arbitrary executions.
Returning through a validated near RET is the function observation boundary. -/
def run : Nat → State → Except Error Execution
  | 0, _ => .error .exhaustedFuel
  | fuel + 1, state => do
    match ← step state with
    | .returned final => return ⟨final, 1⟩
    | .syscall _ => throw .syscallBoundary
    | .next next | .atomic _ next =>
      let result ← run fuel next
      return { result with instructions := result.instructions + 1 }

end EDSL.X86
