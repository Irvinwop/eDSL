/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Machine
import EDSL.Audit

namespace EDSL.Tests.MutexISA
open X86

def memory (code : List Byte) : Memory where
  read address := if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length then
    code[address.toNat - 4096]?
    else match address.toNat with
      | 65535 => some 0xa5
      | 65536 => some 0x78 | 65537 => some 0x56 | 65538 => some 0x34 | 65539 => some 0x92
      | 65540 => some 0x5a | _ => none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length)
  writable address := decide (65536 ≤ address.toNat ∧ address.toNat < 65540)

def entry (code : List Byte) (value flags : Word) : State where
  registers register := if register = .rax then value else if register = .rsi then 65536
    else if register = .rdi then 65535 else 0xdeadbeefcafebabe
  rip := 4096
  flags := flags
  memory := memory code

def next (state : State) : Option State := do
  match ← (step state).toOption with
  | .next result => some result
  | _ => none

-- EAX is zero-extended from the four little-endian bytes at RSI. RDI points
-- elsewhere, so selecting the old operand register changes this observation.
example : (next (entry [0x8b, 0x06] 0xfeedfaceffffffff 0x8d7)).map
    (fun state => (state.registers .rax, state.registers .rsi, state.registers .rdi,
      state.flags, state.rip, state.memory.read 65535, state.memory.read 65540)) =
    some (0x92345678, 65536, 65535, 0x8d7, 4098, some 0xa5, some 0x5a) := by rfl

example : (next (entry [0x89, 0x06] 0xfeedface10203040 0x8d7)).map
    (fun state => ((loadDWord state.memory 65536).toOption, state.registers .rax,
      state.registers .rsi, state.flags, state.rip, state.memory.read 65535, state.memory.read 65540)) =
    some (some 0x10203040, 0xfeedface10203040, 65536, 0x8d7, 4098, some 0xa5, some 0x5a) := by rfl

-- The fourth operand byte is required for both access directions. Store
-- permission is checked for the full word before any resulting state exists.
example : executeLoadRsi { entry [0x8b, 0x06] 0 0 with memory := {
    memory [0x8b, 0x06] with read := fun address =>
      if address = 65539 then none else (memory [0x8b, 0x06]).read address } } =
    .error (.inaccessibleData 65539) := by rfl

example : executeStoreRsi { entry [0x89, 0x06] 99 0 with memory := {
    memory [0x89, 0x06] with writable := fun address => decide (address ≠ 65539) } } =
    .error (.writeDenied 65536) := by rfl

example : executeLoadRsi { entry [] 0 0 with registers := fun _ => 0xffffffffffffffff } =
    .error (.inaccessibleData 0xffffffffffffffff) := by rfl
example : executeStoreRsi { entry [] 0 0 with registers := fun _ => 0xffffffffffffffff } =
    .error (.writeDenied 0xffffffffffffffff) := by rfl

def compare (value : Word) : Option (Word × Word × Word × Word) :=
  (next (entry [0x83, 0xf8, 0] value 0xffffffffffffffff)).map fun state =>
    (state.flags &&& arithmeticFlagMask, state.flags &&& ~~~arithmeticFlagMask,
      state.registers .rax, state.rip)

-- Fixed status masks independently distinguish zero/sign/parity and show that
-- CMP clears previous carry, auxiliary carry and overflow. High RAX is ignored
-- for flag calculation but preserved because CMP never writes its operand.
example : compare 0xfeedface00000000 = some (0x44, 0xfffffffffffff72a, 0xfeedface00000000, 4099) := by decide
example : compare 1 = some (0, 0xfffffffffffff72a, 1, 4099) := by decide
example : compare 3 = some (4, 0xfffffffffffff72a, 3, 4099) := by decide
example : compare 0x80000000 = some (0x84, 0xfffffffffffff72a, 0x80000000, 4099) := by decide
example : compare 0xffffffff = some (0x84, 0xfffffffffffff72a, 0xffffffff, 4099) := by decide

theorem compare_preserves_resources (state : State) :
    (executeCmpEaxZero state).registers = state.registers ∧
    (executeCmpEaxZero state).memory = state.memory := ⟨rfl, rfl⟩

-- JNZ reads only ZF. In particular RCX=nonzero and RAX=nonzero must not force
-- a taken edge when ZF is set. Displacements are signed from the next RIP.
example : (next (entry [0x75, 0xf4] 99 0x8d7)).map
    (fun state => (state.rip, state.flags, state.registers .rax, state.registers .rcx)) =
    some (4098, 0x8d7, 99, 0xdeadbeefcafebabe) := by decide
example : (next (entry [0x75, 0xf4] 0 0x897)).map
    (fun state => (state.rip, state.flags, state.registers .rax, state.registers .rcx)) =
    some (4086, 0x897, 0, 0xdeadbeefcafebabe) := by decide
example : (next (entry [0x75, 0x7f] 0 0)).map State.rip = some 4225 := by decide
example : executeJnz { entry [] 0 0 with rip := 0x7ffffffffffe } 1 =
    .error (.noncanonicalBranch 0x800000000001) := by rfl
example : (executeJnz { entry [] 0 0x40 with rip := 0x7ffffffffffe } 1).toOption.map State.rip =
    some 0x800000000000 := by decide

example : decodeAt (entry [0x83, 0xf8, 1] 0 0) = .error .unsupportedEncoding := by rfl
example : decodeAt (entry [0x83, 0xf9, 0] 0 0) = .error .unsupportedEncoding := by rfl
example : decodeAt (entry [0x8b, 0x05] 0 0) = .error .unsupportedEncoding := by rfl
example : decodeAt (entry [0x89, 0x05] 0 0) = .error .unsupportedEncoding := by rfl
example : decodeAt (entry [0x66, 0x83, 0xf8, 0] 0 0) = .error (.unsupportedOpcode 0x66) := by rfl
example : decodeAt (entry [0x48, 0x8b, 0x06] 0 0) = .error (.unsupportedOpcode 0x48) := by rfl
example : decodeAt (entry [0x67, 0x75, 0] 0 0) = .error (.unsupportedOpcode 0x67) := by rfl
example : decodeAt (entry [0x83, 0xf8] 0 0) = .error (.inaccessibleInstruction 4098) := by rfl
example : decodeAt (entry [0x75] 0 0) = .error (.inaccessibleInstruction 4097) := by rfl
example : decodeAt (entry [0x8b] 0 0) = .error (.inaccessibleInstruction 4097) := by rfl

end EDSL.Tests.MutexISA

#audit_edsl
