/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Std.Tactic.BVDecide

namespace EDSL.X86

abbrev Word := BitVec 64
abbrev Byte := BitVec 8

inductive Register where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

/-- Accessible bytes and execute permission under the selected userspace profile.
The connection to hardware page tables/permissions is an explicit assumption. -/
structure Memory where
  read : Word → Option Byte
  executable : Word → Bool

structure State where
  registers : Register → Word
  rip : Word
  flags : Word
  memory : Memory

def State.writeRegister (state : State) (register : Register) (value : Word) : State :=
  { state with registers := fun r => if r = register then value else state.registers r }

/-- Four-level paging profile: LA57, CET, exceptions and privilege transitions
are not implemented by this machine. -/
def canonical (address : Word) : Bool :=
  decide (address.toNat < 2^47 ∨ 2^64 - 2^47 ≤ address.toNat)

inductive Error where
  | inaccessibleInstruction (address : Word)
  | unsupportedOpcode (opcode : Byte)
  | unsupportedEncoding
  | inaccessibleStack (address : Word)
  | noncanonicalReturn (address : Word)
  | exhaustedFuel
  deriving DecidableEq, Repr

def fetchByte (memory : Memory) (address : Word) : Except Error Byte :=
  if canonical address && memory.executable address then
    match memory.read address with
    | some byte => .ok byte
    | none => .error (.inaccessibleInstruction address)
  else
    .error (.inaccessibleInstruction address)

def readStackByte (memory : Memory) (address : Word) : Except Error Byte :=
  if canonical address then
    match memory.read address with
    | some byte => .ok byte
    | none => .error (.inaccessibleStack address)
  else
    .error (.inaccessibleStack address)

/-- Little-endian eight-byte read; wrapping a memory operand is outside this profile. -/
def readWord (memory : Memory) (address : Word) : Except Error Word := do
  if address.toNat + 7 ≥ 2^64 then
    throw (.inaccessibleStack address)
  let b0 ← readStackByte memory address
  let b1 ← readStackByte memory (address + 1)
  let b2 ← readStackByte memory (address + 2)
  let b3 ← readStackByte memory (address + 3)
  let b4 ← readStackByte memory (address + 4)
  let b5 ← readStackByte memory (address + 5)
  let b6 ← readStackByte memory (address + 6)
  let b7 ← readStackByte memory (address + 7)
  return b0.setWidth 64 ||| (b1.setWidth 64 <<< 8) |||
    (b2.setWidth 64 <<< 16) ||| (b3.setWidth 64 <<< 24) |||
    (b4.setWidth 64 <<< 32) ||| (b5.setWidth 64 <<< 40) |||
    (b6.setWidth 64 <<< 48) ||| (b7.setWidth 64 <<< 56)

inductive Instruction where
  /-- `8D 47 ib`: LEA EAX, [RDI + sign_extend(disp8)], default 64-bit address size. -/
  | leaEaxRdiDisp8 (displacement : Byte)
  /-- `C3`: near return, with an accessible stack word and canonical target. -/
  | ret
  deriving DecidableEq, Repr

def decodeAt (state : State) : Except Error Instruction := do
  let opcode ← fetchByte state.memory state.rip
  if opcode = 0xc3 then
    return .ret
  else if opcode = 0x8d then
    let modrm ← fetchByte state.memory (state.rip + 1)
    if modrm ≠ 0x47 then
      throw .unsupportedEncoding
    let displacement ← fetchByte state.memory (state.rip + 2)
    return .leaEaxRdiDisp8 displacement
  else
    throw (.unsupportedOpcode opcode)

def executeLea (state : State) (displacement : Byte) : State :=
  let address := state.registers .rdi + displacement.signExtend 64
  let result := (address.setWidth 32).setWidth 64
  { state.writeRegister .rax result with rip := state.rip + 3 }

def executeRet (state : State) : Except Error State := do
  let target ← readWord state.memory (state.registers .rsp)
  if canonical target then
    return { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target }
  else
    throw (.noncanonicalReturn target)

inductive StepResult where
  | next (state : State)
  | returned (state : State)

def step (state : State) : Except Error StepResult := do
  match ← decodeAt state with
  | .leaEaxRdiDisp8 displacement => return .next (executeLea state displacement)
  | .ret => return .returned (← executeRet state)

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
    | .next next =>
      let result ← run fuel next
      return { result with instructions := result.instructions + 1 }

/-- Binds the proof to accessible executable bytes at the entry address. -/
def CodeAt (memory : Memory) (base : Word) (bytes : List Byte) : Prop :=
  base.toNat + bytes.length ≤ 2^64 ∧
  ∀ offset byte, bytes[offset]? = some byte →
    fetchByte memory (base + BitVec.ofNat 64 offset) = .ok byte

end EDSL.X86
