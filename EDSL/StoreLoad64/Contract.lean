/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory64
import EDSL.X86.Sequential.CFGTransport
import EDSL.X86.Sequential.Execution

set_option warningAsError true

namespace EDSL.StoreLoad64
open X86 X86.Sequential

/-- Full-width mathematical arguments, independent of instruction selection. -/
structure Input where
  address : Word
  argument : Word
  oldValue : Word
  returnAddress : Word

/-- Present machine facts only: complete executable code, eight writable and
readable target bytes, and the actual eight-byte caller return slot. -/
structure Pre (bytes : List Byte) (input : Input) (initial : State) : Prop where
  code : CodeAt initial.memory initial.rip bytes
  pointer : initial.registers .rdi = input.address
  source : initial.registers .rsi = input.argument
  oldValue : loadQWord initial.memory input.address = .ok input.oldValue
  writable : canStoreQWord initial.memory input.address = true
  codeDisjoint : QWordDisjoint input.address initial.rip bytes.length
  stackDisjoint : QWordDisjoint input.address (initial.registers .rsp) 8
  stack : readWord initial.memory (initial.registers .rsp) = .ok input.returnAddress
  returnCanonical : canonical input.returnAddress = true
  stackBound : (initial.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : canonical (initial.registers .rsp + 8) = true

/-- SysV AMD64 callee-saved general registers; RSP has its own return rule. -/
def calleeSaved : List Register := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- The full 64-bit argument is stored and returned. The frame covers every
byte outside the eight-byte target, all machine write/execute permissions,
all callee-saved registers, every flag, and the actual caller return. -/
structure Post (input : Input) (initial final : State) : Prop where
  result : final.registers .rax = input.argument
  value : loadQWord final.memory input.address = .ok input.argument
  outside : ∀ query, 8 ≤ (query - input.address).toNat →
    final.memory.read query = initial.memory.read query
  writable : final.memory.writable = initial.memory.writable
  executable : final.memory.executable = initial.memory.executable
  returnAddress : final.rip = input.returnAddress
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register ∈ calleeSaved, final.registers register = initial.registers register
  flags : final.flags = initial.flags

theorem Pre.target_addressable {bytes input initial} (pre : Pre bytes input initial) :
    qwordAddressable input.address = true := (Bool.and_eq_true_iff.mp pre.writable).1

/-- This exact window is supplied by the native fixture. No C or volatile
source preservation claim is part of the machine-code theorem. -/
def bytes : List Byte := [0x48, 0x89, 0x37, 0x48, 0x8b, 0x07, 0xc3]

def ResultContract (input : Input) (initial : State) (result : Result) : Prop :=
  Post input initial result.state ∧ result.instructions = 3 ∧
    result.reads = [⟨.data, input.address, 8⟩, ⟨.stack, initial.registers .rsp, 8⟩]

end EDSL.StoreLoad64
