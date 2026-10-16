/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Execution
import EDSL.Audit

namespace EDSL.Tests.SequentialExecution
open X86

-- XOR EAX,EAX; TEST RSI,RSI; RET. TEST overwrites XOR's undefined AF.
def logicalBytes : List Byte := [0x31, 0xc0, 0x48, 0x85, 0xf6, 0xc3]

-- The defined flags of ADD EAX,[RDI] make the two AF histories reconverge.
def addBytes : List Byte := [0x31, 0xc0, 0x48, 0x85, 0xf6, 0x03, 0x07, 0xc3]

def memory (bytes : List Byte) : Memory where
  read address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length then
      bytes[address.toNat - 4096]?
    else if 12288 ≤ address.toNat ∧ address.toNat < 12292 then
      [0, 0, 0, 0x80][address.toNat - 12288]?
    else if 32768 ≤ address.toNat ∧ address.toNat < 32776 then
      [0, 0x20, 0, 0, 0, 0, 0, 0][address.toNat - 32768]?
    else none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length)
  writable address := decide (12288 ≤ address.toNat ∧ address.toNat < 12292)

def entry (bytes : List Byte) : State where
  registers register := match register with
    | .rax => 0xdeadbeeffeed1234
    | .rsi => 1
    | .rdi => 12288
    | .rsp => 32768
    | _ => 0xfaded000000000000
  rip := 4096
  flags := 0xa02
  memory := memory bytes

def falseThenTrue : Sequential.Choices := fun index => decide (index ≠ 0)
def trueThenFalse : Sequential.Choices := fun index => decide (index = 0)

def observe (choices : Sequential.Choices) (fuel : Nat) (initial : State) :
    Option (Word × Word × Word × Word × Nat × List Sequential.Read) := do
  let result ← (Sequential.run choices fuel initial).toOption
  return (result.state.registers .rax, result.state.flags, result.state.rip,
    result.state.registers .rsp, result.instructions, result.reads)

-- Flags are the architectural TEST(1,1) result plus preserved non-status
-- bits and the SECOND instruction's AF. Reusing choices 0 fails these checks.
example : observe falseThenTrue 3 (entry logicalBytes) =
    some (0, 0x212, 8192, 32776, 3, [⟨.stack, 32768, 8⟩]) := by rfl

example : observe trueThenFalse 3 (entry logicalBytes) =
    some (0, 0x202, 8192, 32776, 3, [⟨.stack, 32768, 8⟩]) := by rfl

-- ADD zero + 0x80000000 has SF and PF set, with CF/AF/ZF/OF clear.
-- EAX is zero extended, and only the data operand and RET stack are reads.
example : observe falseThenTrue 4 (entry addBytes) =
    some (0x80000000, 0x286, 8192, 32776, 4,
      [⟨.data, 12288, 4⟩, ⟨.stack, 32768, 8⟩]) := by rfl

-- This compares the complete result, including all registers and memory.
example : Sequential.run falseThenTrue 4 (entry addBytes) = Sequential.run trueThenFalse 4 (entry addBytes) := by rfl

example : Sequential.run falseThenTrue 3 (entry addBytes) = .error .exhaustedFuel := by rfl

-- A continuation cannot hide a fault simply because another stream succeeds.
-- Here both streams encounter the actual missing memory operand.
def missingData : State := { entry addBytes with memory := {
  memory addBytes with read := fun address =>
    if 12288 ≤ address.toNat ∧ address.toNat < 12292 then none else (memory addBytes).read address } }

example : Sequential.run falseThenTrue 4 missingData = .error (.inaccessibleData 12288) := by rfl
example : Sequential.run trueThenFalse 4 missingData = .error (.inaccessibleData 12288) := by rfl

-- The missing ModRM byte is a fetch error, never an operand-read event.
example : Sequential.run falseThenTrue 1 (entry [0x48, 0x85]) =
    .error (.inaccessibleInstruction 4098) := by rfl

example : Sequential.run falseThenTrue 1 (entry [0x67]) = .error (.unsupportedOpcode 0x67) := by rfl
example : Sequential.run falseThenTrue 1 (entry [0x0f, 0x05]) = .error .syscallBoundary := by rfl

-- Legacy atomic outcomes continue execution and count once, retaining their
-- successful four-byte operand read and their actual memory write.
def atomicObservation : Option (Word × BitVec 32 × Nat × List Sequential.Read) := do
  let result ← (Sequential.run trueThenFalse 2 (entry [0x87, 0x07, 0xc3])).toOption
  let stored ← (loadDWord result.state.memory 12288).toOption
  return (result.state.registers .rax, stored, result.instructions, result.reads)

example : atomicObservation = some (0x80000000, 0xfeed1234, 2,
    [⟨.data, 12288, 4⟩, ⟨.stack, 32768, 8⟩]) := by rfl

end EDSL.Tests.SequentialExecution

#audit_edsl
