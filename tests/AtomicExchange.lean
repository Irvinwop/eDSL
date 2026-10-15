/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Compiler.Exchange
import EDSL.X86.Invocation
import EDSL.Audit

namespace EDSL.Tests.AtomicExchange
open X86

/-- Owned code, a return stack, an independently specified little-endian old
word, and neighboring guard bytes. The upper argument/register halves differ
so width and operand-selection mistakes change the observable result. -/
def memory (old : BitVec 32) : Memory where
  read address :=
    match address.toNat with
    | 4096 => some 0x89
    | 4097 => some 0xf0
    | 4098 => some 0x87
    | 4099 => some 0x07
    | 4100 => some 0xc3
    | 32768 => some 0
    | 32769 => some 0x20
    | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some 0
    | 65535 => some 0x5a
    | 65536 => some (old.extractLsb' 0 8)
    | 65537 => some (old.extractLsb' 8 8)
    | 65538 => some (old.extractLsb' 16 8)
    | 65539 => some (old.extractLsb' 24 8)
    | 65540 => some 0xa5
    | _ => none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4101)
  writable address := decide (65536 ≤ address.toNat ∧ address.toNat < 65540)

def entry (old : BitVec 32) (replacement : Word) : State where
  registers register := if register = .rdi then 65536
    else if register = .rsp then 32768
    else if register = .rsi then replacement
    else if register = .rax then 0xdeadbeef76543210
    else 0x13579bdf2468ace0
  rip := 4096
  flags := 0x8d7
  memory := memory old

private theorem code (old : BitVec 32) :
    CodeAt (memory old) 4096 Examples.Compiler.Exchange.bytes := by
  refine ⟨by decide, ?_⟩
  intro offset byte present
  match offset with
  | 0 | 1 | 2 | 3 | 4 =>
    simp [Examples.Compiler.Exchange.bytes] at present
    subst byte
    rfl
  | offset + 5 => simp [Examples.Compiler.Exchange.bytes] at present

private theorem old_word (old : BitVec 32) :
    loadDWord (memory old) 65536 = .ok old := by
  change Except.ok (joinDWord (old.extractLsb' 0 8) (old.extractLsb' 8 8)
    (old.extractLsb' 16 8) (old.extractLsb' 24 8)) = .ok old
  rw [join_extracts]

private theorem code_disjoint : DWordDisjoint 65536 4096 5 := by
  intro offset bound
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨ offset = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem stack_disjoint : DWordDisjoint 65536 32768 8 := by
  intro offset bound
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
    offset = 4 ∨ offset = 5 ∨ offset = 6 ∨ offset = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The exact three-instruction contract is satisfiable for every old 32-bit
word and every 64-bit argument, including nonzero upper argument bits. -/
theorem every_input_executes (old : BitVec 32) (replacement : Word) :
    AtomicExecutes (entry old replacement)
      (Examples.Compiler.Exchange.finalState (entry old replacement) old 8192) 3
      [⟨65536, old, replacement.setWidth 32⟩] := by
  apply Examples.Compiler.Exchange.atomic_execution
  · exact code old
  · change atomicAddressable 65536 = true
    decide
  · rfl
  · exact old_word old
  · exact code_disjoint
  · exact stack_disjoint
  · rfl
  · rfl

structure Observation where
  event : AtomicEvent
  rax : Word
  rdi : Word
  rsi : Word
  r8 : Word
  rsp : Word
  rip : Word
  flags : Word
  data : List (Option Byte)
  codeExecutable : Bool
  dataWritable : Bool
  deriving DecidableEq, Repr

/-- Ordinary steps are deliberately excluded: replacing the labeled RMW with
an ordinary load/store transition must fail this observation. -/
def observeAtomic (initial : State) : Option Observation := do
  let outcome ← (step initial).toOption
  match outcome with
  | .atomic event result =>
    return ⟨event, result.registers .rax, result.registers .rdi, result.registers .rsi,
      result.registers .r8, result.registers .rsp, result.rip, result.flags,
      [65535, 65536, 65537, 65538, 65539, 65540].map result.memory.read,
      result.memory.executable 4098, result.memory.writable 65539⟩
  | _ => none

def atExchange : State :=
  { entry 0x98badcfe 0xfeedface11223344 with
    rip := 4098
    registers := fun register => if register = .rax then 0x7654321089abcdef
      else (entry 0x98badcfe 0xfeedface11223344).registers register }

-- Checks old/new ordering, low32 width, EAX zero extension, endian order,
-- flags/register preservation, neighboring bytes and permission preservation.
example : observeAtomic atExchange = some {
    event := ⟨65536, 0x98badcfe, 0x89abcdef⟩
    rax := 0x98badcfe
    rdi := 65536
    rsi := 0xfeedface11223344
    r8 := 0x13579bdf2468ace0
    rsp := 32768
    rip := 4100
    flags := 0x8d7
    data := [some 0x5a, some 0xef, some 0xcd, some 0xab, some 0x89, some 0xa5]
    codeExecutable := true
    dataWritable := true } := by decide

def observeProgram : Option (Word × Word × Word × Word × Nat × List (Option Byte)) := do
  let result ← (run 3 (entry 0x98badcfe 0xfeedface11223344)).toOption
  return (result.state.registers .rax, result.state.registers .rsp, result.state.rip,
    result.state.flags, result.instructions,
    [65535, 65536, 65537, 65538, 65539, 65540].map result.state.memory.read)

-- The preceding MOV must select RSI, clear its upper half, and count as one
-- instruction; RET consumes the unchanged return word after the atomic step.
example : observeProgram = some (0x98badcfe, 32776, 8192, 0x8d7, 3,
    [some 0x5a, some 0x44, some 0x33, some 0x22, some 0x11, some 0xa5]) := by rfl
example : run 2 (entry 0x98badcfe 0xfeedface11223344) = .error .exhaustedFuel := by rfl

def syscallAfterExchange : State :=
  { atExchange with memory := { atExchange.memory with
    read := fun address => if address = 4100 then some 0x0f
      else if address = 4101 then some 0x05 else atExchange.memory.read address
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4102) } }

def observeSyscall : Option (Nat × Word × Word × Except Error (BitVec 32)) := do
  let result ← (runToSyscall 2 syscallAfterExchange).toOption
  return (result.instructions, result.request.user.registers .rax,
    result.request.continuation,
    loadDWord result.request.user.memory 65536)

-- First-syscall evaluation must continue across an atomic result and retain
-- its changed memory and old-value register, counting the boundary instruction.
example : observeSyscall = some (2, 0x98badcfe, 4102, .ok 0x89abcdef) := by rfl
example : runToSyscall 1 syscallAfterExchange = .error .exhaustedFuel := by rfl

def fullyAccessible : Memory where
  read := fun _ => some 0xa5
  executable := fun _ => false
  writable := fun _ => true

-- Accessible bytes do not override this profile's address restrictions.
example : exchangeDWord fullyAccessible 65537 0 =
    .error (.unsupportedAtomicAddress 65537) := by rfl
example : exchangeDWord fullyAccessible 0x800000000000 0 =
    .error (.unsupportedAtomicAddress 0x800000000000) := by rfl
example : exchangeDWord fullyAccessible 0xffffffffffffffff 0 =
    .error (.unsupportedAtomicAddress 0xffffffffffffffff) := by rfl

-- Both canonical halves are supported, including the final nonwrapping word.
example : atomicAddressable 0x7ffffffffffc = true := by decide
example : atomicAddressable 0xffff800000000000 = true := by decide
example : atomicAddressable 0xfffffffffffffffc = true := by decide

def lastByteDenied : State :=
  { atExchange with memory := { atExchange.memory with
    writable := fun address => decide (address ≠ 65539) } }

def lastByteUnmapped : State :=
  { atExchange with memory := { atExchange.memory with
    read := fun address => if address = 65539 then none else atExchange.memory.read address } }

-- Check the entire destination before emitting an RMW event or result.
example : step lastByteDenied = .error (.writeDenied 65536) := by rfl
example : step lastByteUnmapped = .error (.writeDenied 65536) := by rfl

def unsupportedModRM : State :=
  { atExchange with memory := { atExchange.memory with
    read := fun address => if address = 4099 then some 0xf8 else atExchange.memory.read address } }

def lockPrefix : State :=
  { atExchange with memory := { atExchange.memory with
    read := fun address => if address = 4098 then some 0xf0 else atExchange.memory.read address } }

def missingModRM : State :=
  { atExchange with memory := { atExchange.memory with
    read := fun address => if address = 4099 then none else atExchange.memory.read address } }

example : step unsupportedModRM = .error .unsupportedEncoding := by rfl
example : step lockPrefix = .error (.unsupportedOpcode 0xf0) := by rfl
example : step missingModRM = .error (.inaccessibleInstruction 4099) := by rfl

end EDSL.Tests.AtomicExchange

#audit_edsl
