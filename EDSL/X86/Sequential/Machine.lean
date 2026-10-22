/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.ByteComparison
import EDSL.X86.Sequential.DecodeTransport
import EDSL.WordMath.Scalar

namespace EDSL.X86.Sequential

/-- Exact operand reads of an instruction, using the PRE-instruction state.
Instruction fetch and write-validation permission queries are not operand reads. -/
def Instruction.operandReads (instruction : Instruction) (state : State) : List Read :=
  match instruction with
  | .legacy .ret => [⟨.stack, state.registers .rsp, 8⟩]
  | .legacy .loadEaxRdi | .legacy .exchangeEaxRdi | .legacy .fetchAddEaxRdi =>
    [⟨.data, state.registers .rdi, 4⟩]
  | .legacy .loadEaxRsi => [⟨.data, state.registers .rsi, 4⟩]
  | .loadMem32 _ address | .addMem32 _ address | .cmpMemReg32 address _ => [⟨.data, address.eval state, 4⟩]
  | .cmpMemImm8 address _ | .cmpMemReg8 address _ | .cmpRegMem8 _ address _ | .movzxMem8 _ address _ =>
    [⟨.data, address.eval state, 1⟩]
  | .loadMem64 _ address | .addMem64 _ address => [⟨.data, address.eval state, 8⟩]
  | _ => []

/-- Ordinary store intent uses the PRE-instruction address and low 32 source
bits. Permission validation is part of execution, not an operand read. -/
def Instruction.storeIntent (instruction : Instruction) (state : State) : Option (Word × BitVec 32) :=
  match instruction with
  | .legacy old => old.storeIntent state
  | .storeMem32 address source => some (address.eval state, (state.registers source).setWidth 32)
  | _ => none

/-- Full-width store operands are both captured in the original state. The
existing 32-bit intent classifier retains its original type and meaning. -/
def Instruction.storeIntent64 (instruction : Instruction) (state : State) : Option (Word × Word) :=
  match instruction with
  | .storeMem64 address source => some (address.eval state, state.registers source)
  | _ => none

/-- The sequential extension does not enroll ordinary MOV stores in a
concurrent profile. Only embedded legacy instructions can be locked. -/
def Instruction.isLocked : Instruction → Bool
  | .legacy old => old.isLocked
  | _ => false

def Instruction.choosesAF : Instruction → Bool
  | .logicalReg32 _ _ _ _ | .logicalImm32 _ _ _ _
  | .xorSelf32 _ | .test32 _ _ _ | .test64 _ _ | .logicalReg64 _ _ _ | .shrOne64 _ => true
  | _ => false

/-- Identity of the single undefined flag supported by this profile. This is
not a multi-flag choice vector; IMUL's four undefined bits remain unsupported. -/
inductive ChoiceFlag where
  | af | of
  deriving DecidableEq, Repr

def ChoiceFlag.bitIndex : ChoiceFlag → Nat
  | .af => 4 | .of => 11

def ChoiceFlag.mask : ChoiceFlag → Word
  | .af => 0x10 | .of => 0x800

/-- State-dependent, truthful choice metadata. `choosesAF` retains its old
AF-only meaning for native capture clients. ROL uses old RCX, including aliases. -/
def Instruction.choiceFlag (instruction : Instruction) (state : State) : Option ChoiceFlag :=
  match instruction with
  | .rolCL64 _ => if 1 < rolCount64 (state.registers .rcx) then some .of else none
  | other => if other.choosesAF then some .af else none

/-- Read success is checked by the actual memory primitives, including their
canonicality, nonwrapping and per-byte accessibility checks. -/
def OperandReadSucceeds (state : State) (read : Read) : Prop :=
  match read.kind with
  | .stack => read.bytes = 8 ∧ ∃ value, readWord state.memory read.address = .ok value
  | .data => match read.bytes with
    | 1 => ∃ value, readDataByte state.memory read.address = .ok value
    | 8 => ∃ value, loadQWord state.memory read.address = .ok value
    | _ => read.bytes = 4 ∧ ∃ value, loadDWord state.memory read.address = .ok value

/-- The Bool selects the flag named by `choiceFlag`: AF for self-XOR32, TEST,
logical32/64 and SHR1; OF for ROL with masked count > 1. Legacy execution retains
its complete old result, including concrete flags, stores, atomics and syscall
contexts, for EVERY value of the new argument. -/
def execute (state : State) (instruction : Instruction) (af : Bool) : Except Error Observation := do
  let reads := instruction.operandReads state
  match instruction with
  | .legacy old => return ⟨← X86.executeInstruction state old, reads⟩
  | .imulReg64 _ _ => throw .unsupportedEncoding
  | .endbr64IbtDisabled | .nop _ =>
    return ⟨.next { state with rip := state.rip + BitVec.ofNat 64 instruction.length }, reads⟩
  | .logicalReg32 operation destination source _ =>
    let result := operation.eval ((state.registers destination).setWidth 32)
      ((state.registers source).setWidth 32)
    return ⟨.next { state.writeRegister destination (result.setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 instruction.length
      flags := logicalFlags32 state.flags result af }, reads⟩
  | .logicalImm32 operation destination immediate _ =>
    let result := operation.eval ((state.registers destination).setWidth 32)
      (immediate.signExtend 32)
    return ⟨.next { state.writeRegister destination (result.setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 instruction.length
      flags := logicalFlags32 state.flags result af }, reads⟩
  | .test32 left right _ =>
    let result := (state.registers left).setWidth 32 &&& (state.registers right).setWidth 32
    return ⟨.next { state with
      rip := state.rip + BitVec.ofNat 64 instruction.length
      flags := logicalFlags32 state.flags result af }, reads⟩
  | .cmp32 left right _ =>
    return ⟨.next { state with
      rip := state.rip + BitVec.ofNat 64 instruction.length
      flags := cmpFlags32 state.flags ((state.registers left).setWidth 32)
        ((state.registers right).setWidth 32) }, reads⟩
  | .cmpReg8 left right _ =>
    return ⟨.next { state with
      rip := state.rip + BitVec.ofNat 64 instruction.length
      flags := cmpFlags8 state.flags ((state.registers left).setWidth 8)
        ((state.registers right).setWidth 8) }, reads⟩
  | .subReg32 destination source _ =>
    let left := (state.registers destination).setWidth 32
    let right := (state.registers source).setWidth 32
    return ⟨.next { state.writeRegister destination ((left - right).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 instruction.length
      flags := cmpFlags32 state.flags left right }, reads⟩
  | .negReg32 destination _ =>
    let value := (state.registers destination).setWidth 32
    return ⟨.next { state.writeRegister destination ((-value).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 instruction.length
      flags := cmpFlags32 state.flags 0 value }, reads⟩
  | .bswapReg64 destination =>
    return ⟨.next { state.writeRegister destination (WordMath.byteSwap64 (state.registers destination)) with
      rip := state.rip + 3 }, reads⟩
  | .shrOne64 destination =>
    let value := state.registers destination
    return ⟨.next { state.writeRegister destination (value >>> 1) with
      rip := state.rip + 3, flags := shrOneFlags64 state.flags value af }, reads⟩
  | .rolCL64 destination =>
    let value := state.registers destination
    let count := rolCount64 (state.registers .rcx)
    let result := value.rotateLeft count
    return ⟨.next { state.writeRegister destination result with
      rip := state.rip + 3, flags := rolFlags64 state.flags result count af }, reads⟩
  | .movzxReg8 destination source _ =>
    let value := (state.registers source).setWidth 8
    return ⟨.next { state.writeRegister destination ((value.setWidth 32).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 instruction.length }, reads⟩
  | .movzxMem8 destination address _ =>
    let value ← readDataByte state.memory (address.eval state)
    return ⟨.next { state.writeRegister destination ((value.setWidth 32).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 instruction.length }, reads⟩
  | .cmpMemImm8 address immediate =>
    let value ← readDataByte state.memory (address.eval state)
    return ⟨.next { state with
      rip := state.rip + BitVec.ofNat 64 instruction.length
      flags := cmpFlags8 state.flags value immediate }, reads⟩
  | .cmpMemReg8 address source =>
    let value ← readDataByte state.memory (address.eval state)
    return ⟨.next { state with
      rip := state.rip + BitVec.ofNat 64 instruction.length
      flags := cmpFlags8 state.flags value ((state.registers source).setWidth 8) }, reads⟩
  | .cmpRegMem8 left address _ =>
    let value ← readDataByte state.memory (address.eval state)
    return ⟨.next { state with
      rip := state.rip + BitVec.ofNat 64 instruction.length
      flags := cmpFlags8 state.flags ((state.registers left).setWidth 8) value }, reads⟩
  | .cmpMemReg32 address source =>
    let value ← loadDWord state.memory (address.eval state)
    return ⟨.next { state with
      rip := state.rip + BitVec.ofNat 64 instruction.length
      flags := cmpFlags32 state.flags value ((state.registers source).setWidth 32) }, reads⟩
  | .movReg32 destination source =>
    return ⟨.next { state.writeRegister destination
      (((state.registers source).setWidth 32).setWidth 64) with rip := state.rip + 2 }, reads⟩
  | .movReg64 destination source =>
    return ⟨.next { state.writeRegister destination (state.registers source) with
      rip := state.rip + 3 }, reads⟩
  | .movSignImm32 destination immediate =>
    return ⟨.next { state.writeRegister destination (immediate.signExtend 64) with
      rip := state.rip + 7 }, reads⟩
  | .setcc condition destination _ =>
    let value : Byte := if condition.holds state.flags then 1 else 0
    return ⟨.next { state.writeRegister destination
      (replaceLow8 (state.registers destination) value) with
      rip := state.rip + BitVec.ofNat 64 instruction.length }, reads⟩
  | .movImm8 destination immediate _ =>
    return ⟨.next { state.writeRegister destination
      (replaceLow8 (state.registers destination) immediate) with
      rip := state.rip + BitVec.ofNat 64 instruction.length }, reads⟩
  | .cmovReg64 condition destination source =>
    return ⟨.next { state.writeRegister destination
      (if condition.holds state.flags then state.registers source else state.registers destination) with
      rip := state.rip + 4 }, reads⟩
  | .cmovReg32 condition destination source _ =>
    let chosen := if condition.holds state.flags then state.registers source
      else state.registers destination
    return ⟨.next { state.writeRegister destination ((chosen.setWidth 32).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 instruction.length }, reads⟩
  | .lea64 destination address =>
    return ⟨.next { state.writeRegister destination (address.eval state) with
      rip := state.rip + BitVec.ofNat 64 instruction.length }, reads⟩
  | .addReg64 destination source =>
    let left := state.registers destination
    let right := state.registers source
    return ⟨.next { state.writeRegister destination (left + right) with
      rip := state.rip + 3, flags := addFlags64 state.flags left right }, reads⟩
  | .logicalReg64 operation destination source =>
    let result := operation.eval (state.registers destination) (state.registers source)
    return ⟨.next { state.writeRegister destination result with
      rip := state.rip + 3, flags := logicalFlags64 state.flags result af }, reads⟩
  | .xchgReg64 left right =>
    return ⟨.next { (state.writeRegister left (state.registers right)).writeRegister
      right (state.registers left) with rip := state.rip + 3 }, reads⟩
  | .xchgRax64 other =>
    return ⟨.next { (state.writeRegister .rax (state.registers other)).writeRegister
      other (state.registers .rax) with rip := state.rip + 2 }, reads⟩
  | .loadMem32 destination address =>
    let value ← loadDWord state.memory (address.eval state)
    return ⟨.next { state.writeRegister destination (value.setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 instruction.length }, reads⟩
  | .storeMem32 address source =>
    let memory ← storeDWord state.memory (address.eval state) ((state.registers source).setWidth 32)
    return ⟨.next { state with
      memory := memory
      rip := state.rip + BitVec.ofNat 64 instruction.length }, reads⟩
  | .loadMem64 destination address =>
    let value ← loadQWord state.memory (address.eval state)
    return ⟨.next { state.writeRegister destination value with
      rip := state.rip + BitVec.ofNat 64 instruction.length }, reads⟩
  | .storeMem64 address source =>
    let memory ← storeQWord state.memory (address.eval state) (state.registers source)
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
  | .cmpImm64 left immediate =>
    return ⟨.next { state with
      rip := state.rip + 4
      flags := cmpFlags64 state.flags (state.registers left) (immediate.signExtend 64) }, reads⟩
  | .addMem32 destination address =>
    let value ← loadDWord state.memory (address.eval state)
    let left := (state.registers destination).setWidth 32
    return ⟨.next { state.writeRegister destination ((left + value).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 instruction.length,
      flags := addFlags32 state.flags left value }, reads⟩
  | .addMem64 destination address =>
    let value ← loadQWord state.memory (address.eval state)
    let left := state.registers destination
    return ⟨.next { state.writeRegister destination (left + value) with
      rip := state.rip + BitVec.ofNat 64 instruction.length,
      flags := addFlags64 state.flags left value }, reads⟩
  | .addImm64 destination immediate =>
    let left := state.registers destination
    let right := immediate.signExtend 64
    return ⟨.next { state.writeRegister destination (left + right) with
      rip := state.rip + 4, flags := addFlags64 state.flags left right }, reads⟩
  | .addImm32 destination immediate _ =>
    let left := (state.registers destination).setWidth 32
    let right := immediate.signExtend 32
    return ⟨.next { state.writeRegister destination ((left + right).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 instruction.length
      flags := addFlags32 state.flags left right }, reads⟩
  | .inc32 destination _ =>
    let value := (state.registers destination).setWidth 32
    return ⟨.next { state.writeRegister destination ((value + 1).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 instruction.length
      flags := incFlags32 state.flags value }, reads⟩
  | .inc64 destination =>
    return ⟨.next { state.writeRegister destination (state.registers destination + 1) with
      rip := state.rip + 3, flags := incFlags64 state.flags (state.registers destination) }, reads⟩
  | .dec64 destination =>
    return ⟨.next { state.writeRegister destination (state.registers destination - 1) with
      rip := state.rip + 3, flags := decFlags64 state.flags (state.registers destination) }, reads⟩
  | .je displacement => return ⟨.next (← executeShortBranch state (state.flags.getLsbD 6) displacement), reads⟩
  | .jcc condition displacement =>
    return ⟨.next (← executeShortBranch state (condition.holds state.flags) displacement), reads⟩
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

/-- No-op only under `targetProfile`: 64-bit mode and CET/IBT disabled.
This statement describes the abstract target; decoding does not inspect MSRs. -/
theorem execute_endbr64IbtDisabled (state : State) (af : Bool) :
    execute state .endbr64IbtDisabled af =
      .ok ⟨.next { state with rip := state.rip + 4 }, []⟩ := rfl

theorem execute_nop (state : State) (encoding : NopEncoding) (af : Bool) :
    execute state (.nop encoding) af =
      .ok ⟨.next { state with rip := state.rip + BitVec.ofNat 64 encoding.length }, []⟩ := rfl

/-- These exact observations preserve the entire register file (including
high halves and RSP), RAM and permission maps. No operand read occurs. -/
theorem execute_cmp32 (state : State) (left right : Register) (prefixed af : Bool) :
    execute state (.cmp32 left right prefixed) af =
      .ok ⟨.next { state with
        rip := state.rip + BitVec.ofNat 64 (Instruction.cmp32 left right prefixed).length
        flags := cmpFlags32 state.flags ((state.registers left).setWidth 32)
          ((state.registers right).setWidth 32) }, []⟩ := rfl

theorem execute_cmpReg8 (state : State) (left right : Register) (prefixed af : Bool) :
    execute state (.cmpReg8 left right prefixed) af =
      .ok ⟨.next { state with
        rip := state.rip + BitVec.ofNat 64 (Instruction.cmpReg8 left right prefixed).length
        flags := cmpFlags8 state.flags ((state.registers left).setWidth 8)
          ((state.registers right).setWidth 8) }, []⟩ := rfl

/-- Both register operands are captured before writing, including self-SUB. -/
theorem execute_subReg32 (state : State) (destination source : Register) (prefixed af : Bool) :
    execute state (.subReg32 destination source prefixed) af =
      .ok ⟨.next { state.writeRegister destination
        ((((state.registers destination).setWidth 32) -
          ((state.registers source).setWidth 32)).setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (Instruction.subReg32 destination source prefixed).length
        flags := cmpFlags32 state.flags ((state.registers destination).setWidth 32)
          ((state.registers source).setWidth 32) }, []⟩ := rfl

theorem execute_movzxReg8 (state : State) (destination source : Register) (prefixed af : Bool) :
    execute state (.movzxReg8 destination source prefixed) af =
      .ok ⟨.next { state.writeRegister destination
        ((((state.registers source).setWidth 8).setWidth 32).setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (Instruction.movzxReg8 destination source prefixed).length },
        []⟩ := rfl

/-- The original low32 operand defines both result and all arithmetic flags.
The AF argument is ignored; there is no undefined arithmetic flag for NEG. -/
theorem execute_negReg32 (state : State) (destination : Register) (prefixed af : Bool) :
    execute state (.negReg32 destination prefixed) af =
      .ok ⟨.next { state.writeRegister destination
        ((-((state.registers destination).setWidth 32)).setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (Instruction.negReg32 destination prefixed).length
        flags := cmpFlags32 state.flags 0 ((state.registers destination).setWidth 32) }, []⟩ := rfl

/-- The full64 prestate value is reversed; every flag and all operand memory
are preserved, including when the destination is RSP. -/
theorem execute_bswapReg64 (state : State) (destination : Register) (af : Bool) :
    execute state (.bswapReg64 destination) af =
      .ok ⟨.next { state.writeRegister destination (WordMath.byteSwap64 (state.registers destination)) with
        rip := state.rip + 3 }, []⟩ := rfl

theorem execute_shrOne64 (state : State) (destination : Register) (af : Bool) :
    execute state (.shrOne64 destination) af =
      .ok ⟨.next { state.writeRegister destination (state.registers destination >>> 1) with
        rip := state.rip + 3,
        flags := shrOneFlags64 state.flags (state.registers destination) af }, []⟩ := rfl

/-- DATA1, not DATA4: neither adjacent bytes nor execute/write permissions
are required. Address and source are evaluated entirely in the prestate. -/
theorem execute_movzxMem8 (state : State) (destination : Register) (address : Address)
    (prefixed af : Bool) :
    execute state (.movzxMem8 destination address prefixed) af = do
      let value ← readDataByte state.memory (address.eval state)
      return ⟨.next { state.writeRegister destination ((value.setWidth 32).setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (Instruction.movzxMem8 destination address prefixed).length },
        [⟨.data, address.eval state, 1⟩]⟩ := rfl

theorem execute_movzxMem8_success_iff {state : State} {destination : Register} {address : Address}
    {prefixed af : Bool} {observation : Observation} :
    execute state (.movzxMem8 destination address prefixed) af = .ok observation ↔
      ∃ value, readDataByte state.memory (address.eval state) = .ok value ∧
        observation = ⟨.next { state.writeRegister destination ((value.setWidth 32).setWidth 64) with
          rip := state.rip + BitVec.ofNat 64 (Instruction.movzxMem8 destination address prefixed).length },
          [⟨.data, address.eval state, 1⟩]⟩ := by
  rw [execute_movzxMem8]
  cases loaded : readDataByte state.memory (address.eval state) <;> simp [eq_comm]

theorem execute_movzxMem8_failure {state : State} {destination : Register} {address : Address}
    {prefixed af : Bool} {fault : Error}
    (failed : readDataByte state.memory (address.eval state) = .error fault) :
    execute state (.movzxMem8 destination address prefixed) af = .error fault := by
  simp only [execute_movzxMem8, failed, error_bind]

/-- The successful byte read is the only operand access. All registers, RAM
and its permission maps are preserved, including when base and index alias. -/
theorem execute_cmpMemImm8 (state : State) (address : Address) (immediate : Byte) (af : Bool) :
    execute state (.cmpMemImm8 address immediate) af = do
      let value ← readDataByte state.memory (address.eval state)
      return ⟨.next { state with
        rip := state.rip + BitVec.ofNat 64 (Instruction.cmpMemImm8 address immediate).length
        flags := cmpFlags8 state.flags value immediate }, [⟨.data, address.eval state, 1⟩]⟩ := rfl

theorem execute_cmpMemImm8_success_iff {state : State} {address : Address} {immediate : Byte}
    {af : Bool} {observation : Observation} :
    execute state (.cmpMemImm8 address immediate) af = .ok observation ↔
      ∃ value, readDataByte state.memory (address.eval state) = .ok value ∧
        observation = ⟨.next { state with
          rip := state.rip + BitVec.ofNat 64 (Instruction.cmpMemImm8 address immediate).length
          flags := cmpFlags8 state.flags value immediate }, [⟨.data, address.eval state, 1⟩]⟩ := by
  rw [execute_cmpMemImm8]
  cases loaded : readDataByte state.memory (address.eval state) <;> simp [eq_comm]

theorem execute_cmpMemImm8_context {state final : State} {address : Address} {immediate : Byte}
    {af : Bool} {observation : Observation}
    (success : execute state (.cmpMemImm8 address immediate) af = .ok observation)
    (next : observation.result = .next final) :
    final.registers = state.registers ∧ final.memory = state.memory ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask ∧
      observation.reads = [⟨.data, address.eval state, 1⟩] ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.cmpMemImm8 address immediate).length := by
  obtain ⟨value, _, rfl⟩ := execute_cmpMemImm8_success_iff.mp success
  cases next
  exact ⟨rfl, rfl, cmpFlags8_preserves .., rfl, rfl⟩

/-- Memory is the left operand; only LOW8 of the PRE source participates.
The actual DATA1 primitive supplies every fault and the exact read footprint. -/
theorem execute_cmpMemReg8 (state : State) (address : Address) (source : Register) (af : Bool) :
    execute state (.cmpMemReg8 address source) af = do
      let value ← readDataByte state.memory (address.eval state)
      return ⟨.next { state with
        rip := state.rip + BitVec.ofNat 64 (Instruction.cmpMemReg8 address source).length
        flags := cmpFlags8 state.flags value ((state.registers source).setWidth 8) },
        [⟨.data, address.eval state, 1⟩]⟩ := rfl

theorem execute_cmpMemReg8_success_iff {state : State} {address : Address} {source : Register}
    {af : Bool} {observation : Observation} :
    execute state (.cmpMemReg8 address source) af = .ok observation ↔
      ∃ value, readDataByte state.memory (address.eval state) = .ok value ∧
        observation = ⟨.next { state with
          rip := state.rip + BitVec.ofNat 64 (Instruction.cmpMemReg8 address source).length
          flags := cmpFlags8 state.flags value ((state.registers source).setWidth 8) },
          [⟨.data, address.eval state, 1⟩]⟩ := by
  rw [execute_cmpMemReg8]
  cases loaded : readDataByte state.memory (address.eval state) <;> simp [eq_comm]

/-- No GPR, RAM or permission map changes; all nonarithmetic flags survive.
This includes source/base/index aliases and arbitrary high register bits. -/
theorem execute_cmpMemReg8_context {state final : State} {address : Address} {source : Register}
    {af : Bool} {observation : Observation}
    (success : execute state (.cmpMemReg8 address source) af = .ok observation)
    (next : observation.result = .next final) :
    final.registers = state.registers ∧ final.memory = state.memory ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask ∧
      observation.reads = [⟨.data, address.eval state, 1⟩] ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.cmpMemReg8 address source).length := by
  obtain ⟨value, _, rfl⟩ := execute_cmpMemReg8_success_iff.mp success
  cases next
  exact ⟨rfl, rfl, cmpFlags8_preserves .., rfl, rfl⟩

/-- Register-left LOW8 comparison with precisely one checked DATA1 access.
No destination write occurs; even the address and left-register aliases refer
to the original state. Prefix metadata affects only instruction length. -/
theorem execute_cmpRegMem8 (state : State) (left : Register) (address : Address)
    (prefixed af : Bool) :
    execute state (.cmpRegMem8 left address prefixed) af = do
      let value ← readDataByte state.memory (address.eval state)
      return ⟨.next { state with
        rip := state.rip + BitVec.ofNat 64 (Instruction.cmpRegMem8 left address prefixed).length
        flags := cmpFlags8 state.flags ((state.registers left).setWidth 8) value },
        [⟨.data, address.eval state, 1⟩]⟩ := rfl

theorem execute_cmpRegMem8_success_iff {state : State} {left : Register} {address : Address}
    {prefixed af : Bool} {observation : Observation} :
    execute state (.cmpRegMem8 left address prefixed) af = .ok observation ↔
      ∃ value, readDataByte state.memory (address.eval state) = .ok value ∧
        observation = ⟨.next { state with
          rip := state.rip + BitVec.ofNat 64 (Instruction.cmpRegMem8 left address prefixed).length
          flags := cmpFlags8 state.flags ((state.registers left).setWidth 8) value },
          [⟨.data, address.eval state, 1⟩]⟩ := by
  rw [execute_cmpRegMem8]
  cases loaded : readDataByte state.memory (address.eval state) <;> simp [eq_comm]

theorem execute_cmpRegMem8_context {state final : State} {left : Register} {address : Address}
    {prefixed af : Bool} {observation : Observation}
    (success : execute state (.cmpRegMem8 left address prefixed) af = .ok observation)
    (next : observation.result = .next final) :
    final.registers = state.registers ∧ final.memory = state.memory ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask ∧
      observation.reads = [⟨.data, address.eval state, 1⟩] ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.cmpRegMem8 left address prefixed).length := by
  obtain ⟨value, _, rfl⟩ := execute_cmpRegMem8_success_iff.mp success
  cases next
  exact ⟨rfl, rfl, cmpFlags8_preserves .., rfl, rfl⟩

/-- Memory-left LOW32 comparison with precisely one checked DATA4 access.
Address arithmetic uses full64 registers, independently of comparison width. -/
theorem execute_cmpMemReg32 (state : State) (address : Address) (source : Register) (af : Bool) :
    execute state (.cmpMemReg32 address source) af = do
      let value ← loadDWord state.memory (address.eval state)
      return ⟨.next { state with
        rip := state.rip + BitVec.ofNat 64 (Instruction.cmpMemReg32 address source).length
        flags := cmpFlags32 state.flags value ((state.registers source).setWidth 32) },
        [⟨.data, address.eval state, 4⟩]⟩ := rfl

theorem execute_cmpMemReg32_success_iff {state : State} {address : Address} {source : Register}
    {af : Bool} {observation : Observation} :
    execute state (.cmpMemReg32 address source) af = .ok observation ↔
      ∃ value, loadDWord state.memory (address.eval state) = .ok value ∧
        observation = ⟨.next { state with
          rip := state.rip + BitVec.ofNat 64 (Instruction.cmpMemReg32 address source).length
          flags := cmpFlags32 state.flags value ((state.registers source).setWidth 32) },
          [⟨.data, address.eval state, 4⟩]⟩ := by
  rw [execute_cmpMemReg32]
  cases loaded : loadDWord state.memory (address.eval state) <;> simp [eq_comm]

theorem execute_cmpMemReg32_context {state final : State} {address : Address} {source : Register}
    {af : Bool} {observation : Observation}
    (success : execute state (.cmpMemReg32 address source) af = .ok observation)
    (next : observation.result = .next final) :
    final.registers = state.registers ∧ final.memory = state.memory ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask ∧
      observation.reads = [⟨.data, address.eval state, 4⟩] ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.cmpMemReg32 address source).length := by
  obtain ⟨value, _, rfl⟩ := execute_cmpMemReg32_success_iff.mp success
  cases next
  exact ⟨rfl, rfl, cmpFlags32_preserves .., rfl, rfl⟩

theorem execute_movSignImm32 (state : State) (destination : Register)
    (immediate : BitVec 32) (af : Bool) :
    execute state (.movSignImm32 destination immediate) af =
      .ok ⟨.next { state.writeRegister destination (immediate.signExtend 64) with
        rip := state.rip + 7 }, []⟩ := rfl

/-- Full64 replacement, including RSP; no flags, other GPRs, RAM or permissions
change. There are no operand reads or alignment/canonicality premises. -/
theorem execute_movSignImm32_context (state : State) (destination : Register)
    (immediate : BitVec 32) (af : Bool) :
    ∃ final, execute state (.movSignImm32 destination immediate) af = .ok ⟨.next final, []⟩ ∧
      final.registers destination = immediate.signExtend 64 ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags ∧ final.rip = state.rip + 7 := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

theorem execute_test32 (state : State) (left right : Register) (prefixed af : Bool) :
    execute state (.test32 left right prefixed) af =
      .ok ⟨.next { state with
        rip := state.rip + BitVec.ofNat 64 (Instruction.test32 left right prefixed).length
        flags := logicalFlags32 state.flags
          ((state.registers left).setWidth 32 &&& (state.registers right).setWidth 32) af }, []⟩ := rfl

/-- Every architectural TEST32 flags outcome is represented. AF is the only
freedom; neither choice permits a register write, data read or unrelated flag
change. This is an overapproximation of undefined AF, not a claim that a CPU
must realize both physical values. -/
theorem execute_test32_admissible_iff (state : State) (left right : Register)
    (prefixed : Bool) (actual : Word) :
    (∃ af, execute state (.test32 left right prefixed) af =
      .ok ⟨.next { state with
        rip := state.rip + BitVec.ofNat 64 (Instruction.test32 left right prefixed).length
        flags := actual }, []⟩) ↔
      LogicalFlagsAdmissible state.flags actual
        (evenParity (((state.registers left).setWidth 32 &&&
          (state.registers right).setWidth 32).setWidth 8))
        ((state.registers left).setWidth 32 &&& (state.registers right).setWidth 32 == 0)
        ((state.registers left).setWidth 32 &&& (state.registers right).setWidth 32).msb := by
  rw [logicalFlags32_admissible_iff]
  constructor
  · rintro ⟨af, success⟩
    refine ⟨af, ?_⟩
    rw [execute_test32] at success
    have same := congrArg (fun observation : Observation => match observation.result with
      | .next final => final.flags | _ => 0) (Except.ok.inj success)
    exact same.symm
  · rintro ⟨af, same⟩
    refine ⟨af, ?_⟩
    rw [execute_test32, ←same]

theorem execute_movReg32 (state : State) (destination source : Register) (af : Bool) :
    execute state (.movReg32 destination source) af =
      .ok ⟨.next { state.writeRegister destination
        (((state.registers source).setWidth 32).setWidth 64) with rip := state.rip + 2 }, []⟩ := rfl

theorem execute_movReg64 (state : State) (destination source : Register) (af : Bool) :
    execute state (.movReg64 destination source) af =
      .ok ⟨.next { state.writeRegister destination (state.registers source) with
        rip := state.rip + 3 }, []⟩ := rfl

/-- CMOV reads the incoming flags and full source before assigning the
destination. This operation has no memory-source interpretation. -/
theorem execute_cmovReg64 (state : State) (condition : Condition)
    (destination source : Register) (af : Bool) :
    execute state (.cmovReg64 condition destination source) af =
      .ok ⟨.next { state.writeRegister destination
        (if condition.holds state.flags then state.registers source else state.registers destination) with
        rip := state.rip + 4 }, []⟩ := rfl

/-- Aliases and RSP obey the same pre-state contract. All other GPRs, all
flags, the complete RAM and both permission maps survive, with no operand read. -/
theorem execute_cmovReg64_context (state : State) (condition : Condition)
    (destination source : Register) (af : Bool) :
    ∃ final, execute state (.cmovReg64 condition destination source) af = .ok ⟨.next final, []⟩ ∧
      final.registers destination =
        (if condition.holds state.flags then state.registers source else state.registers destination) ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags ∧ final.rip = state.rip + 4 := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

/-- A false register condition retains the entire register file, including
the high destination half and RSP. Only the instruction pointer advances. -/
theorem execute_cmovReg64_false (state : State) (condition : Condition)
    (destination source : Register) (af : Bool) (conditionFalse : condition.holds state.flags = false) :
    execute state (.cmovReg64 condition destination source) af =
      .ok ⟨.next { state with rip := state.rip + 4 }, []⟩ := by
  rw [execute_cmovReg64, conditionFalse]
  congr 3
  simp only [State.writeRegister, Bool.false_eq_true, ↓reduceIte, State.mk.injEq, and_true]
  funext register
  by_cases same : register = destination <;> simp [same]

/-- CMOV32 selects a pre-state low32 operand and zero-extends it on BOTH
outcomes. In particular a false condition does not retain high destination
bits. No operand memory is read and AF is irrelevant. -/
theorem execute_cmovReg32 (state : State) (condition : Condition)
    (destination source : Register) (prefixed af : Bool) :
    execute state (.cmovReg32 condition destination source prefixed) af =
      .ok ⟨.next { state.writeRegister destination
        ((((if condition.holds state.flags then state.registers source
          else state.registers destination) : Word).setWidth 32).setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (if prefixed then 4 else 3) }, []⟩ := rfl

/-- RSP and aliases obey the same low32 selection rule. Other registers,
complete RAM and permissions, and every flag are preserved. -/
theorem execute_cmovReg32_context (state : State) (condition : Condition)
    (destination source : Register) (prefixed af : Bool) :
    ∃ final, execute state (.cmovReg32 condition destination source prefixed) af =
        .ok ⟨.next final, []⟩ ∧
      final.registers destination =
        ((((if condition.holds state.flags then state.registers source
          else state.registers destination) : Word).setWidth 32).setWidth 64) ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags ∧
      final.rip = state.rip + BitVec.ofNat 64 (if prefixed then 4 else 3) := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

/-- The false path still writes a zero-extended low32 destination. -/
theorem execute_cmovReg32_false (state : State) (condition : Condition)
    (destination source : Register) (prefixed af : Bool)
    (conditionFalse : condition.holds state.flags = false) :
    execute state (.cmovReg32 condition destination source prefixed) af =
      .ok ⟨.next { state.writeRegister destination
        (((state.registers destination).setWidth 32).setWidth 64) with
        rip := state.rip + BitVec.ofNat 64 (if prefixed then 4 else 3) }, []⟩ := by
  rw [execute_cmovReg32, conditionFalse]
  rfl

/-- A mathematical low32 result independent of the destination's original
upper half. This is valid for arbitrary payloads and flags on either branch. -/
theorem execute_cmovReg32_value (state : State) (condition : Condition)
    (destination source : Register) (prefixed af : Bool) :
    ∃ final, execute state (.cmovReg32 condition destination source prefixed) af =
        .ok ⟨.next final, []⟩ ∧
      (final.registers destination).toNat =
        (if condition.holds state.flags then (state.registers source).toNat
          else (state.registers destination).toNat) % 2^32 := by
  obtain ⟨final,actual,value,_⟩ :=
    execute_cmovReg32_context state condition destination source prefixed af
  refine ⟨final,actual,?_⟩
  rw [value]
  simp only [BitVec.toNat_setWidth]
  split <;> exact Nat.mod_eq_of_lt
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

theorem execute_xchgReg64 (state : State) (left right : Register) (af : Bool) :
    execute state (.xchgReg64 left right) af =
      .ok ⟨.next { (state.writeRegister left (state.registers right)).writeRegister
        right (state.registers left) with rip := state.rip + 3 }, []⟩ := rfl

theorem execute_xchgRax64 (state : State) (other : Register) (af : Bool) :
    execute state (.xchgRax64 other) af =
      .ok ⟨.next { (state.writeRegister .rax (state.registers other)).writeRegister
        other (state.registers .rax) with rip := state.rip + 2 }, []⟩ := rfl

/-- Both operands come from the original state. Aliases need no distinctness
premise, all other registers survive, and no operand memory is accessed. -/
theorem execute_xchgReg64_context (state : State) (left right : Register) (af : Bool) :
    ∃ final, execute state (.xchgReg64 left right) af = .ok ⟨.next final, []⟩ ∧
      final.registers left = state.registers right ∧
      final.registers right = state.registers left ∧
      (∀ register, register ≠ left → register ≠ right →
        final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags ∧ final.rip = state.rip + 3 := by
  refine ⟨_, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · by_cases same : left = right <;> simp [State.writeRegister, same]
  · simp [State.writeRegister]
  · intro register differentLeft differentRight
    simp [State.writeRegister, differentLeft, differentRight]

theorem execute_xchgRax64_context (state : State) (other : Register) (af : Bool) :
    ∃ final, execute state (.xchgRax64 other) af = .ok ⟨.next final, []⟩ ∧
      final.registers .rax = state.registers other ∧
      final.registers other = state.registers .rax ∧
      (∀ register, register ≠ .rax → register ≠ other →
        final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags ∧ final.rip = state.rip + 2 := by
  refine ⟨_, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · cases other <;> simp [State.writeRegister]
  · simp [State.writeRegister]
  · intro register differentRax differentOther
    simp [State.writeRegister, differentRax, differentOther]

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

theorem execute_loadMem64 (state : State) (destination : Register) (address : Address) (af : Bool) :
    execute state (.loadMem64 destination address) af = do
      let value ← loadQWord state.memory (address.eval state)
      return ⟨.next { state.writeRegister destination value with
        rip := state.rip + BitVec.ofNat 64 (Instruction.loadMem64 destination address).length },
        [⟨.data, address.eval state, 8⟩]⟩ := rfl

/-- One checked eight-byte DATA read precedes the full-width addition. -/
theorem execute_addMem64 (state : State) (destination : Register) (address : Address) (af : Bool) :
    execute state (.addMem64 destination address) af = do
      let value ← loadQWord state.memory (address.eval state)
      return ⟨.next { state.writeRegister destination (state.registers destination + value) with
        rip := state.rip + BitVec.ofNat 64 (Instruction.addMem64 destination address).length,
        flags := addFlags64 state.flags (state.registers destination) value },
        [⟨.data, address.eval state, 8⟩]⟩ := rfl

theorem execute_storeMem64 (state : State) (address : Address) (source : Register) (af : Bool) :
    execute state (.storeMem64 address source) af = do
      let memory ← storeQWord state.memory (address.eval state) (state.registers source)
      return ⟨.next { state with
        memory := memory
        rip := state.rip + BitVec.ofNat 64 (Instruction.storeMem64 address source).length }, []⟩ := rfl

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

/-- The actual checked load uses the PRE-instruction address, even when the
destination is an address base or index. No distinctness assumption is needed. -/
theorem execute_loadMem64_context {state : State} {destination : Register} {address : Address}
    {value : Word} (af : Bool)
    (loaded : loadQWord state.memory (address.eval state) = .ok value) :
    ∃ final, execute state (.loadMem64 destination address) af =
        .ok ⟨.next final, [⟨.data, address.eval state, 8⟩]⟩ ∧
      final.registers destination = value ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.loadMem64 destination address).length := by
  refine ⟨{ state.writeRegister destination value with
    rip := state.rip + BitVec.ofNat 64 (Instruction.loadMem64 destination address).length },
    ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [execute_loadMem64, loaded, ok_bind, pure_ok]
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

/-- Success exposes the actual eight-byte primitive result; an observation
cannot assert an unchecked or differently addressed load. -/
theorem execute_loadMem64_success_iff {state : State} {destination : Register} {address : Address}
    {af : Bool} {observation : Observation} :
    execute state (.loadMem64 destination address) af = .ok observation ↔
      ∃ value, loadQWord state.memory (address.eval state) = .ok value ∧
        observation = ⟨.next { state.writeRegister destination value with
          rip := state.rip + BitVec.ofNat 64 (Instruction.loadMem64 destination address).length },
          [⟨.data, address.eval state, 8⟩]⟩ := by
  rw [execute_loadMem64]
  cases loaded : loadQWord state.memory (address.eval state) <;> simp [eq_comm]

/-- The checked load and old destination use the PRE-instruction state, even
when the destination aliases the base or index, including RSP. No register
distinctness or address-preservation premise is required. -/
theorem execute_addMem64_context {state : State} {destination : Register} {address : Address}
    {value : Word} (af : Bool)
    (loaded : loadQWord state.memory (address.eval state) = .ok value) :
    ∃ final, execute state (.addMem64 destination address) af =
        .ok ⟨.next final, [⟨.data, address.eval state, 8⟩]⟩ ∧
      final.registers destination = state.registers destination + value ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧
      final.flags = addFlags64 state.flags (state.registers destination) value ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.addMem64 destination address).length := by
  refine ⟨{ state.writeRegister destination (state.registers destination + value) with
    rip := state.rip + BitVec.ofNat 64 (Instruction.addMem64 destination address).length,
    flags := addFlags64 state.flags (state.registers destination) value },
    ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [execute_addMem64, loaded, ok_bind, pure_ok]
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

/-- Independent natural/integer sum, carry and overflow specifications, plus
the remaining four arithmetic flags and the complete nonarithmetic frame.
The same pre-state supplies the address and the old destination under aliasing. -/
theorem execute_addMem64_arithmetic {state : State} {destination : Register} {address : Address}
    {value : Word} (af : Bool)
    (loaded : loadQWord state.memory (address.eval state) = .ok value) :
    ∃ final, execute state (.addMem64 destination address) af =
        .ok ⟨.next final, [⟨.data, address.eval state, 8⟩]⟩ ∧
      (final.registers destination).toNat = ((state.registers destination).toNat + value.toNat) % 2^64 ∧
      (final.flags.getLsbD 0 = true ↔ 2^64 ≤ (state.registers destination).toNat + value.toNat) ∧
      (final.flags.getLsbD 11 = true ↔
        (state.registers destination).toInt + value.toInt < -(2^63 : Int) ∨
          2^63 ≤ (state.registers destination).toInt + value.toInt) ∧
      final.flags.getLsbD 2 = evenParity ((state.registers destination + value).setWidth 8) ∧
      final.flags.getLsbD 4 =
        ((state.registers destination).setWidth 4).uaddOverflow (value.setWidth 4) ∧
      final.flags.getLsbD 6 = (state.registers destination + value == 0) ∧
      final.flags.getLsbD 7 = (state.registers destination + value).msb ∧
      final.flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask := by
  obtain ⟨final, executed, assigned, _, _, flags, _⟩ := execute_addMem64_context af loaded
  refine ⟨final, executed, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [assigned, BitVec.toNat_add]
  · rw [flags]
    exact addFlags64_carry ..
  · rw [flags]
    exact addFlags64_overflow ..
  · rw [flags]
    exact (addFlags64_bits ..).2.1
  · rw [flags]
    exact (addFlags64_bits ..).2.2.1
  · rw [flags]
    exact (addFlags64_bits ..).2.2.2.1
  · rw [flags]
    exact (addFlags64_bits ..).2.2.2.2.1
  · rw [flags]
    exact addFlags64_preserves ..

/-- Every success exposes the actual complete qword load. Failed reads cannot
produce an observation or a continuation. -/
theorem execute_addMem64_success_iff {state : State} {destination : Register} {address : Address}
    {af : Bool} {observation : Observation} :
    execute state (.addMem64 destination address) af = .ok observation ↔
      ∃ value, loadQWord state.memory (address.eval state) = .ok value ∧
        observation = ⟨.next { state.writeRegister destination (state.registers destination + value) with
          rip := state.rip + BitVec.ofNat 64 (Instruction.addMem64 destination address).length,
          flags := addFlags64 state.flags (state.registers destination) value },
          [⟨.data, address.eval state, 8⟩]⟩ := by
  rw [execute_addMem64]
  cases loaded : loadQWord state.memory (address.eval state) <;> simp [eq_comm]

/-- Preserve the primitive's exact error without fabricating a read event. -/
theorem execute_addMem64_fault {state : State} {destination : Register} {address : Address}
    {fault : Error} (af : Bool)
    (failed : loadQWord state.memory (address.eval state) = .error fault) :
    execute state (.addMem64 destination address) af = .error fault := by
  simp only [execute_addMem64, failed, error_bind]

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
  | imulReg64 _ _ | logicalReg32 _ _ _ _ | logicalImm32 _ _ _ _ | cmpImm64 _ _
  | addImm32 _ _ _ | inc32 _ _
  | negReg32 _ _ | bswapReg64 _ | shrOne64 _ | rolCL64 _
  | movzxMem8 _ _ _ | movzxReg8 _ _ _ | cmpReg8 _ _ _ | subReg32 _ _ _
  | movReg32 _ _ | movReg64 _ _ | setcc _ _ _ | movImm8 _ _ _ | movSignImm32 _ _ | cmovReg32 _ _ _ _ | cmovReg64 _ _ _ | lea64 _ _ | addReg64 _ _ | logicalReg64 _ _ _ | xchgReg64 _ _ | xchgRax64 _ | loadMem32 _ _ | loadMem64 _ _ | storeMem64 _ _ | xorSelf32 _ | test32 _ _ _ | cmp32 _ _ _ | endbr64IbtDisabled | nop _ | test64 _ _ | cmp64 _ _ | cmpMemImm8 _ _ | cmpRegMem8 _ _ _ | cmpMemReg8 _ _ | cmpMemReg32 _ _ | addMem32 _ _ | addMem64 _ _
  | addImm64 _ _ | inc64 _ | dec64 _ | je _ | jcc _ _ | jmp _ =>
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

/-- A full-width ordinary store executes exactly the checked eight-byte
primitive using the original address and original source register. -/
theorem execute_storeIntent64 {state : State} {instruction : Instruction} {address value : Word}
    (af : Bool) (intent : instruction.storeIntent64 state = some (address, value)) :
    execute state instruction af = do
      let memory ← storeQWord state.memory address value
      return ⟨.next { state with
        memory := memory
        rip := state.rip + BitVec.ofNat 64 instruction.length }, []⟩ := by
  cases instruction <;>
    simp only [Instruction.storeIntent64, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at intent
  rcases intent with ⟨rfl, rfl⟩
  exact execute_storeMem64 state _ _ af

/-- Successful stores expose the exact checked memory result and empty operand
read footprint. Validation queries never become data reads. -/
theorem execute_storeIntent64_success_iff {state : State} {instruction : Instruction} {address : Word}
    {value : Word} {af : Bool} {observation : Observation}
    (intent : instruction.storeIntent64 state = some (address, value)) :
    execute state instruction af = .ok observation ↔
      ∃ memory, storeQWord state.memory address value = .ok memory ∧
        observation = ⟨.next { state with
          memory := memory
          rip := state.rip + BitVec.ofNat 64 instruction.length }, []⟩ := by
  rw [execute_storeIntent64 af intent]
  cases stored : storeQWord state.memory address value <;> simp [eq_comm]

/-- Complete success/failure behavior: all eight bytes are validated before an
updated state exists. This is a sequential byte update, not an atomicity claim. -/
theorem execute_storeIntent64_checked {state : State} {instruction : Instruction} {address : Word}
    {value : Word} (af : Bool)
    (intent : instruction.storeIntent64 state = some (address, value)) :
    execute state instruction af =
      if canStoreQWord state.memory address then
        .ok ⟨.next { state with
          memory := writeQWordUnchecked state.memory address value
          rip := state.rip + BitVec.ofNat 64 instruction.length }, []⟩
      else .error (.writeDenied address) := by
  rw [execute_storeIntent64 af intent]
  cases allowed : canStoreQWord state.memory address <;> simp [storeQWord, allowed]

/-- Store intent determines the full next state, including preserved registers
and flags. Permission failure produces no partial next-state observation. -/
theorem execute_storeIntent64_next_iff {initial final : State} {instruction : Instruction}
    {address : Word} {value : Word} {af : Bool} {reads : List Read}
    (intent : instruction.storeIntent64 initial = some (address, value)) :
    execute initial instruction af = .ok ⟨.next final, reads⟩ ↔
      canStoreQWord initial.memory address = true ∧
      final = { initial with
        memory := writeQWordUnchecked initial.memory address value
        rip := initial.rip + BitVec.ofNat 64 instruction.length } ∧ reads = [] := by
  rw [execute_storeIntent64_checked af intent]
  cases canStoreQWord initial.memory address <;> simp [eq_comm]

/-- Successful ordinary stores preserve every byte outside their exact
eight-byte footprint and both permission maps, and load back the full source word. -/
theorem execute_storeIntent64_frame {initial final : State} {instruction : Instruction}
    {address : Word} {value : Word} {af : Bool} {observation : Observation}
    (intent : instruction.storeIntent64 initial = some (address, value))
    (success : execute initial instruction af = .ok observation)
    (next : observation.result = .next final) :
    final.registers = initial.registers ∧ final.flags = initial.flags ∧
      final.rip = initial.rip + BitVec.ofNat 64 instruction.length ∧
      loadQWord final.memory address = .ok value ∧
      (∀ query, 8 ≤ (query - address).toNat → final.memory.read query = initial.memory.read query) ∧
      final.memory.executable = initial.memory.executable ∧
      final.memory.writable = initial.memory.writable ∧ observation.reads = [] := by
  rw [execute_storeIntent64_checked af intent] at success
  cases allowed : canStoreQWord initial.memory address with
  | false => simp [allowed] at success
  | true =>
    simp only [allowed, ↓reduceIte, Except.ok.injEq] at success
    cases success
    cases next
    refine ⟨rfl, rfl, rfl, (qword_store_sound _ _ _ allowed).2, ?_, rfl, rfl, rfl⟩
    intro query outside
    exact writeQWord_frame initial.memory address query value outside

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

/-- LEA uses pre-state address registers, never reads operand RAM, and leaves
all flags unchanged. The computed word needs no canonicality premise. -/
theorem execute_lea64 (state : State) (destination : Register) (address : Address) (af : Bool) :
    execute state (.lea64 destination address) af =
      .ok ⟨.next { state.writeRegister destination (address.eval state) with
        rip := state.rip + BitVec.ofNat 64 (Instruction.lea64 destination address).length }, []⟩ := rfl

/-- Both ADD operands are captured before writing even when they alias. -/
theorem execute_addReg64 (state : State) (destination source : Register) (af : Bool) :
    execute state (.addReg64 destination source) af =
      .ok ⟨.next { state.writeRegister destination
        (state.registers destination + state.registers source) with
        rip := state.rip + 3,
        flags := addFlags64 state.flags (state.registers destination) (state.registers source) }, []⟩ := rfl

/-- All logical operands are read from the original register file. AF is an
independent choice; CF/OF clear and SF/ZF/PF follow the full-width result. -/
theorem execute_logicalReg64 (state : State) (operation : LogicalOp)
    (destination source : Register) (af : Bool) :
    execute state (.logicalReg64 operation destination source) af =
      .ok ⟨.next { state.writeRegister destination
        (operation.eval (state.registers destination) (state.registers source)) with
        rip := state.rip + 3,
        flags := logicalFlags64 state.flags
          (operation.eval (state.registers destination) (state.registers source)) af }, []⟩ := rfl

/-- Includes aliases and RSP. The complete RAM and permission maps and all
non-destination registers survive, and there is no operand-memory access. -/
theorem execute_logicalReg64_context (state : State) (operation : LogicalOp)
    (destination source : Register) (af : Bool) :
    ∃ final, execute state (.logicalReg64 operation destination source) af = .ok ⟨.next final, []⟩ ∧
      final.registers destination = operation.eval (state.registers destination) (state.registers source) ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧
      final.flags = logicalFlags64 state.flags
        (operation.eval (state.registers destination) (state.registers source)) af ∧
      final.rip = state.rip + 3 := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

/-- Effective-address arithmetic preserves the entire memory and every flag.
The same pre-state supplies both address registers when either aliases the
destination, including RSP; there are no operand-access premises. -/
theorem execute_lea64_context (state : State) (destination : Register)
    (address : Address) (af : Bool) :
    ∃ final, execute state (.lea64 destination address) af = .ok ⟨.next final, []⟩ ∧
      final.registers destination = address.eval state ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧ final.flags = state.flags ∧
      final.rip = state.rip + BitVec.ofNat 64 (Instruction.lea64 destination address).length := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

/-- Register addition has a modular full64 result and preserves the full
memory and all other registers. Its flags are the existing six-bit arithmetic
contract, independent of the modeled choice for undefined logical AF. -/
theorem execute_addReg64_context (state : State) (destination source : Register) (af : Bool) :
    ∃ final, execute state (.addReg64 destination source) af = .ok ⟨.next final, []⟩ ∧
      final.registers destination = state.registers destination + state.registers source ∧
      (∀ register, register ≠ destination → final.registers register = state.registers register) ∧
      final.memory = state.memory ∧
      final.flags = addFlags64 state.flags (state.registers destination) (state.registers source) ∧
      final.rip = state.rip + 3 := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · simp [State.writeRegister]
  · intro register different
    simp [State.writeRegister, different]

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

theorem execute_jcc (state : State) (condition : Condition) (displacement : Byte) (af : Bool) :
    execute state (.jcc condition displacement) af = do
      return ⟨.next (← executeShortBranch state (condition.holds state.flags) displacement), []⟩ := rfl

/-- Observation footprints cannot be supplied independently of execution. -/
theorem execute_reads {state : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (success : execute state instruction af = .ok observation) :
    observation.reads = instruction.operandReads state := by
  cases instruction with
  | imulReg64 _ _ => simp [execute] at success
  | movzxMem8 destination address prefixed =>
    obtain ⟨value, _, rfl⟩ := execute_movzxMem8_success_iff.mp success
    rfl
  | legacy old =>
    cases result : X86.executeInstruction state old <;> simp only [execute, result, ok_bind, error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at success
    cases success
    rfl
  | cmpMemImm8 address immediate =>
    cases loaded : readDataByte state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success
    rfl
  | cmpRegMem8 left address prefixed =>
    obtain ⟨value, _, rfl⟩ := execute_cmpRegMem8_success_iff.mp success
    rfl
  | cmpMemReg8 address source =>
    obtain ⟨value, _, rfl⟩ := execute_cmpMemReg8_success_iff.mp success
    rfl
  | cmpMemReg32 address source =>
    obtain ⟨value, _, rfl⟩ := execute_cmpMemReg32_success_iff.mp success
    rfl
  | loadMem32 destination address | addMem32 destination address =>
    cases loaded : loadDWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success
    rfl
  | loadMem64 destination address | addMem64 destination address =>
    cases loaded : loadQWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success
    rfl
  | storeMem32 address source =>
    cases stored : storeDWord state.memory (address.eval state) ((state.registers source).setWidth 32) <;>
      simp [execute, stored] at success
    cases success
    rfl
  | storeMem64 address source =>
    cases stored : storeQWord state.memory (address.eval state) (state.registers source) <;>
      simp [execute, stored] at success
    cases success
    rfl
  | je displacement =>
    cases result : executeShortBranch state (state.flags.getLsbD 6) displacement <;>
      simp only [execute, result, ok_bind, error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at success
    cases success
    rfl
  | jcc condition displacement =>
    cases result : executeShortBranch state (condition.holds state.flags) displacement <;>
      simp only [execute, result, ok_bind, error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at success
    cases success
    rfl
  | jmp displacement =>
    cases result : executeShortBranch state true displacement <;> simp only [execute, result, ok_bind, error_bind, pure_ok, Except.ok.injEq, reduceCtorEq] at success
    cases success
    rfl
  | logicalReg32 _ _ _ _ | logicalImm32 _ _ _ _ | cmpImm64 _ _
  | negReg32 destination prefixed | bswapReg64 destination | shrOne64 destination | rolCL64 destination
  | movzxReg8 destination source prefixed
  | movReg32 destination source | movReg64 destination source | setcc condition destination prefixed | movImm8 destination immediate prefixed | movSignImm32 destination immediate | lea64 destination address
  | cmovReg32 condition destination source prefixed | cmovReg64 condition destination source | addReg64 destination source | logicalReg64 operation destination source | xchgReg64 left right | xchgRax64 other
  | cmpReg8 left right prefixed | subReg32 destination source prefixed
  | test32 left right prefixed | cmp32 left right prefixed | endbr64IbtDisabled | nop encoding
  | xorSelf32 destination | test64 left right | cmp64 left right
  | addImm32 destination immediate prefixed | inc32 destination prefixed
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
  | imulReg64 _ _ => simp [execute] at success
  | movzxMem8 destination address prefixed =>
    obtain ⟨value, loaded, _⟩ := execute_movzxMem8_success_iff.mp success
    intro read member
    simp only [Instruction.operandReads, List.mem_singleton] at member
    subst read
    exact ⟨value, loaded⟩
  | legacy old =>
    cases executed : X86.executeInstruction state old with
    | error fault => simp [execute, executed] at success
    | ok result => exact legacy_reads_succeed executed
  | cmpMemImm8 address immediate =>
    cases loaded : readDataByte state.memory (address.eval state) with
    | error fault => simp [execute, loaded] at success
    | ok value =>
      intro read member
      simp only [Instruction.operandReads, List.mem_singleton] at member
      subst read
      exact ⟨value, loaded⟩
  | cmpRegMem8 left address prefixed =>
    obtain ⟨value, loaded, _⟩ := execute_cmpRegMem8_success_iff.mp success
    intro read member
    simp only [Instruction.operandReads, List.mem_singleton] at member
    subst read
    exact ⟨value, loaded⟩
  | cmpMemReg8 address source =>
    obtain ⟨value, loaded, _⟩ := execute_cmpMemReg8_success_iff.mp success
    intro read member
    simp only [Instruction.operandReads, List.mem_singleton] at member
    subst read
    exact ⟨value, loaded⟩
  | cmpMemReg32 address source =>
    obtain ⟨value, loaded, _⟩ := execute_cmpMemReg32_success_iff.mp success
    intro read member
    simp only [Instruction.operandReads, List.mem_singleton] at member
    subst read
    exact ⟨rfl, value, loaded⟩
  | loadMem32 destination address | addMem32 destination address =>
    cases loaded : loadDWord state.memory (address.eval state) with
    | error fault => simp [execute, loaded] at success
    | ok value =>
      intro read member
      simp only [Instruction.operandReads, List.mem_singleton] at member
      subst read
      exact ⟨rfl, value, loaded⟩
  | loadMem64 destination address | addMem64 destination address =>
    cases loaded : loadQWord state.memory (address.eval state) with
    | error fault => simp [execute, loaded] at success
    | ok value =>
      intro read member
      simp only [Instruction.operandReads, List.mem_singleton] at member
      subst read
      exact ⟨value, loaded⟩
  | logicalReg32 _ _ _ _ | logicalImm32 _ _ _ _ | cmpImm64 _ _
  | addImm32 _ _ _ | inc32 _ _
  | negReg32 _ _ | bswapReg64 _ | shrOne64 _ | rolCL64 _
  | movzxReg8 _ _ _ | cmpReg8 _ _ _ | subReg32 _ _ _
  | movReg32 _ _ | movReg64 _ _ | setcc _ _ _ | movImm8 _ _ _ | movSignImm32 _ _ | cmovReg32 _ _ _ _ | cmovReg64 _ _ _ | lea64 _ _ | addReg64 _ _ | logicalReg64 _ _ _ | xchgReg64 _ _ | xchgRax64 _ | storeMem32 _ _ | storeMem64 _ _ | xorSelf32 _ | test32 _ _ _ | cmp32 _ _ _ | endbr64IbtDisabled | nop _ | test64 _ _ | cmp64 _ _
  | addImm64 _ _ | inc64 _ | dec64 _ | je _ | jcc _ _ | jmp _ =>
    simp [Instruction.operandReads]

/-- New operations without either store width preserve the full memory and
permission maps. Both intent premises are essential for ordinary MOV stores. -/
theorem execute_new_memory {state final : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (newInstruction : instruction.isNew = true)
    (noStore : instruction.storeIntent state = none)
    (noStore64 : instruction.storeIntent64 state = none)
    (success : execute state instruction af = .ok observation)
    (next : observation.result = .next final) : final.memory = state.memory := by
  cases instruction with
  | imulReg64 _ _ => simp [execute] at success
  | movzxMem8 destination address prefixed =>
    obtain ⟨value, _, rfl⟩ := execute_movzxMem8_success_iff.mp success
    cases next
    rfl
  | legacy old => simp [Instruction.isNew] at newInstruction
  | cmpMemImm8 address immediate =>
    exact (execute_cmpMemImm8_context success next).2.1
  | cmpRegMem8 left address prefixed =>
    exact (execute_cmpRegMem8_context success next).2.1
  | cmpMemReg8 address source =>
    exact (execute_cmpMemReg8_context success next).2.1
  | cmpMemReg32 address source =>
    exact (execute_cmpMemReg32_context success next).2.1
  | logicalReg32 _ _ _ _ | logicalImm32 _ _ _ _ | cmpImm64 _ _
  | negReg32 destination prefixed | bswapReg64 destination | shrOne64 destination | rolCL64 destination
  | movzxReg8 destination source prefixed
  | movReg32 destination source | movReg64 destination source | setcc condition destination prefixed | movImm8 destination immediate prefixed | movSignImm32 destination immediate | lea64 destination address
  | cmovReg32 condition destination source prefixed | cmovReg64 condition destination source | addReg64 destination source | logicalReg64 operation destination source | xchgReg64 left right | xchgRax64 other
  | cmpReg8 left right prefixed | subReg32 destination source prefixed
  | test32 left right prefixed | cmp32 left right prefixed | endbr64IbtDisabled | nop encoding
  | xorSelf32 destination | test64 left right | cmp64 left right
  | addImm32 destination immediate prefixed | inc32 destination prefixed
  | addImm64 destination immediate | inc64 destination | dec64 destination =>
    cases success
    cases next
    rfl
  | loadMem32 destination address | addMem32 destination address =>
    cases loaded : loadDWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success
    cases next
    rfl
  | loadMem64 destination address | addMem64 destination address =>
    cases loaded : loadQWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success
    cases next
    rfl
  | storeMem32 address source => simp [Instruction.storeIntent] at noStore
  | storeMem64 address source => simp [Instruction.storeIntent64] at noStore64
  | je displacement =>
    cases branched : executeShortBranch state (state.flags.getLsbD 6) displacement with
    | error fault => simp only [execute, branched, error_bind, reduceCtorEq] at success
    | ok result =>
      simp only [execute, branched, ok_bind, pure_ok, Except.ok.injEq] at success
      cases success
      cases next
      exact executeShortBranch_memory branched
  | jcc condition displacement =>
    cases branched : executeShortBranch state (condition.holds state.flags) displacement with
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

/-- Neutral replacement for the former AF-only independence implication.
AF-preserving instructions can still choose OF, so `choosesAF = false` alone
is not a sufficient premise. -/
theorem execute_choice_independent (state : State) (instruction : Instruction) (left right : Bool)
    (noChoice : instruction.choiceFlag state = none) :
    execute state instruction left = execute state instruction right := by
  cases instruction with
  | rolCL64 destination =>
    simp only [Instruction.choiceFlag] at noChoice
    have defined : rolCount64 (state.registers .rcx) ≤ 1 := by
      split at noChoice <;> simp_all <;> omega
    simp only [execute]
    rw [rolFlags64_independent _ _ _ left right defined]
  | _ =>
    simp [Instruction.choiceFlag, Instruction.choosesAF] at noChoice <;> rfl

theorem execute_new_next {state : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (newInstruction : instruction.isNew = true)
    (success : execute state instruction af = .ok observation) :
    ∃ final, observation.result = .next final := by
  cases instruction with
  | imulReg64 _ _ => simp [execute] at success
  | movzxMem8 destination address prefixed =>
    obtain ⟨value, _, rfl⟩ := execute_movzxMem8_success_iff.mp success
    exact ⟨_, rfl⟩
  | legacy old => simp [Instruction.isNew] at newInstruction
  | cmpMemImm8 address immediate =>
    obtain ⟨value, _, rfl⟩ := execute_cmpMemImm8_success_iff.mp success
    exact ⟨_, rfl⟩
  | cmpRegMem8 left address prefixed =>
    obtain ⟨value, _, rfl⟩ := execute_cmpRegMem8_success_iff.mp success
    exact ⟨_, rfl⟩
  | cmpMemReg8 address source =>
    obtain ⟨value, _, rfl⟩ := execute_cmpMemReg8_success_iff.mp success
    exact ⟨_, rfl⟩
  | cmpMemReg32 address source =>
    obtain ⟨value, _, rfl⟩ := execute_cmpMemReg32_success_iff.mp success
    exact ⟨_, rfl⟩
  | logicalReg32 _ _ _ _ | logicalImm32 _ _ _ _ | cmpImm64 _ _
  | negReg32 destination prefixed | bswapReg64 destination | shrOne64 destination | rolCL64 destination
  | movzxReg8 destination source prefixed
  | movReg32 destination source | movReg64 destination source | setcc condition destination prefixed | movImm8 destination immediate prefixed | movSignImm32 destination immediate | lea64 destination address
  | cmovReg32 condition destination source prefixed | cmovReg64 condition destination source | addReg64 destination source | logicalReg64 operation destination source | xchgReg64 left right | xchgRax64 other
  | cmpReg8 left right prefixed | subReg32 destination source prefixed
  | test32 left right prefixed | cmp32 left right prefixed | endbr64IbtDisabled | nop encoding
  | xorSelf32 destination | test64 left right | cmp64 left right
  | addImm32 destination immediate prefixed | inc32 destination prefixed
  | addImm64 destination immediate | inc64 destination | dec64 destination =>
    cases success
    exact ⟨_, rfl⟩
  | loadMem32 destination address | addMem32 destination address =>
    cases loaded : loadDWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success
    exact ⟨_, rfl⟩
  | loadMem64 destination address | addMem64 destination address =>
    cases loaded : loadQWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success
    exact ⟨_, rfl⟩
  | storeMem32 address source =>
    cases stored : storeDWord state.memory (address.eval state) ((state.registers source).setWidth 32) <;>
      simp [execute, stored] at success
    cases success
    exact ⟨_, rfl⟩
  | storeMem64 address source =>
    cases stored : storeQWord state.memory (address.eval state) (state.registers source) <;>
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
  | jcc condition displacement =>
    cases branched : executeShortBranch state (condition.holds state.flags) displacement with
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
  | imulReg64 _ _ => simp [execute] at success
  | movzxMem8 destination address prefixed =>
    obtain ⟨value, _, rfl⟩ := execute_movzxMem8_success_iff.mp success
    cases next
    rfl
  | cmpReg8 left right prefixed =>
    cases success; cases next
    exact cmpFlags8_preserves ..
  | subReg32 destination source prefixed =>
    cases success; cases next
    exact cmpFlags32_preserves ..
  | negReg32 destination prefixed =>
    cases success; cases next
    exact cmpFlags32_preserves ..
  | shrOne64 destination =>
    cases success; cases next
    exact shrOneFlags64_preserves ..
  | logicalReg32 operation destination source prefixed
  | logicalImm32 operation destination immediate prefixed =>
    cases success; cases next
    exact logicalFlags32_preserves ..
  | cmpImm64 left immediate =>
    cases success; cases next
    exact cmpFlags64_preserves ..
  | rolCL64 destination =>
    cases success; cases next
    exact rolFlags64_preserves ..
  | legacy old => simp [Instruction.isNew] at newInstruction
  | cmpMemImm8 address immediate =>
    exact (execute_cmpMemImm8_context success next).2.2.1
  | cmpRegMem8 left address prefixed =>
    exact (execute_cmpRegMem8_context success next).2.2.1
  | cmpMemReg8 address source =>
    exact (execute_cmpMemReg8_context success next).2.2.1
  | cmpMemReg32 address source =>
    exact (execute_cmpMemReg32_context success next).2.2.1
  | bswapReg64 destination
  | movzxReg8 destination source prefixed
  | movReg32 destination source | movReg64 destination source | setcc condition destination prefixed | movImm8 destination immediate prefixed | movSignImm32 destination immediate | lea64 destination address
  | cmovReg32 condition destination source prefixed | cmovReg64 condition destination source | xchgReg64 left right | xchgRax64 other
  | endbr64IbtDisabled | nop encoding =>
    cases success; cases next
    rfl
  | loadMem32 destination address =>
    cases loaded : loadDWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success; cases next
    rfl
  | loadMem64 destination address =>
    cases loaded : loadQWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success; cases next
    rfl
  | storeMem32 address source =>
    cases stored : storeDWord state.memory (address.eval state) ((state.registers source).setWidth 32) <;>
      simp [execute, stored] at success
    cases success; cases next
    rfl
  | storeMem64 address source =>
    cases stored : storeQWord state.memory (address.eval state) (state.registers source) <;>
      simp [execute, stored] at success
    cases success; cases next
    rfl
  | xorSelf32 destination =>
    cases success; cases next
    exact logicalFlags32_preserves ..
  | test32 left right prefixed =>
    cases success; cases next
    exact logicalFlags32_preserves ..
  | cmp32 left right prefixed =>
    cases success; cases next
    exact cmpFlags32_preserves ..
  | test64 left right =>
    cases success; cases next
    exact logicalFlags64_preserves ..
  | cmp64 left right =>
    cases success; cases next
    exact cmpFlags64_preserves ..
  | addReg64 destination source =>
    cases success; cases next
    exact addFlags64_preserves ..
  | logicalReg64 operation destination source =>
    cases success; cases next
    exact logicalFlags64_preserves ..
  | addImm64 destination immediate =>
    cases success; cases next
    exact addFlags64_preserves ..
  | addImm32 destination immediate prefixed =>
    cases success; cases next
    exact addFlags32_preserves ..
  | inc32 destination prefixed =>
    cases success; cases next
    exact incFlags32_preserves ..
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
  | addMem64 destination address =>
    cases loaded : loadQWord state.memory (address.eval state) <;> simp [execute, loaded] at success
    cases success; cases next
    exact addFlags64_preserves ..
  | je displacement =>
    cases branched : executeShortBranch state (state.flags.getLsbD 6) displacement with
    | error fault => simp only [execute, branched, error_bind, reduceCtorEq] at success
    | ok result =>
      simp only [execute, branched, ok_bind, pure_ok, Except.ok.injEq] at success
      cases success; cases next
      rw [shortBranch_flags branched]
  | jcc condition displacement =>
    cases branched : executeShortBranch state (condition.holds state.flags) displacement with
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
