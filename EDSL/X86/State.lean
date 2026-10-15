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

/-- Accessible bytes, execute permission and write permission for sequential,
ordinary RAM accesses. The physical interpretation assumes alignment checking
is disabled; page tables, device memory and concurrent visibility are external. -/
structure Memory where
  read : Word → Option Byte
  executable : Word → Bool
  writable : Word → Bool := fun _ => false

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
  | inaccessibleData (address : Word)
  | writeDenied (address : Word)
  | noncanonicalReturn (address : Word)
  | noncanonicalBranch (address : Word)
  | syscallBoundary
  | unexpectedReturn
  | exhaustedFuel
  deriving DecidableEq, Repr

@[simp] theorem ok_bind (value : α) (continuation : α → Except ε β) :
    (Except.ok value >>= continuation) = continuation value := rfl

@[simp] theorem error_bind (error : ε) (continuation : α → Except ε β) :
    (Except.error error >>= continuation) = .error error := rfl

@[simp] theorem pure_ok (value : α) : (pure value : Except ε α) = .ok value := rfl

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

/-- Binds the proof to accessible executable bytes at the entry address. -/
def CodeAt (memory : Memory) (base : Word) (bytes : List Byte) : Prop :=
  base.toNat + bytes.length ≤ 2^64 ∧
  ∀ offset byte, bytes[offset]? = some byte →
    fetchByte memory (base + BitVec.ofNat 64 offset) = .ok byte

end EDSL.X86
