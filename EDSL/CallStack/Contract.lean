/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Ownership.Model
import EDSL.X86.Sequential.ConditionFlags

set_option warningAsError true

namespace EDSL.CallStack
open X86 X86.Sequential OS.AddressSpace

/-- A complete code window with its selected entry. Helpers may precede the
entry; a proof must bind their bytes as well as those of the caller. -/
structure Program where
  bytes : List Byte
  entry : Nat

def Program.codeBase (program : Program) (initial : State) : Word :=
  initial.rip - BitVec.ofNat 64 program.entry

theorem Program.entry_address (program : Program) (initial : State) :
    program.codeBase initial + BitVec.ofNat 64 program.entry = initial.rip :=
  BitVec.sub_add_cancel ..

/-- Full containment uses natural addresses, never a wrapping interval. -/
def PrivateSlot (region : Region) (address : Word) : Prop :=
  region.base.toNat ≤ address.toNat ∧
    address.toNat + 8 ≤ region.base.toNat + region.length

instance (region : Region) (address : Word) : Decidable (PrivateSlot region address) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure Input where
  value : Word
  target : Word
  frame : Region

/-- Two mathematical unsigned increments, with reduction only at the end. The
result does not depend on a helper, compiler, instruction count or call shape. -/
def resultNat (value : Word) : Nat := (value.toNat + 2) % 2^64

theorem resultNat_lt (value : Word) : resultNat value < 2^64 :=
  Nat.mod_lt _ (by decide)

theorem two_additions (value : Word) :
    ((value + 1) + 1).toNat = resultNat value := by
  simp only [BitVec.toNat_add, resultNat]
  rw [Nat.mod_add_mod]
  congr 1

/-- Present code, external ABI inputs, private stack capacity and the original
caller slot. Writable qwords are current permission facts; no future step or
helper result is assumed. The private frame may retain changed bytes on return.
Sixteen bytes support the selected programs, independently of their encoding. -/
structure Pre (program : Program) (input : Input) (initial : State) : Prop where
  code : CodeAt initial.memory (program.codeBase initial) program.bytes
  entry : program.entry < program.bytes.length
  argument : initial.registers .rdi = input.value
  frameValid : input.frame.valid = true
  frameTop : input.frame.base.toNat + input.frame.length = (initial.registers .rsp).toNat
  capacity : 16 ≤ input.frame.length
  writable : ∀ address, PrivateSlot input.frame address →
    canStoreQWord initial.memory address = true
  codeSeparate : OS.Ownership.Disjoint input.frame
    ⟨program.codeBase initial, program.bytes.length⟩
  stack : readWord initial.memory (initial.registers .rsp) = .ok input.target
  canonicalTarget : canonical input.target = true
  stackBound : (initial.registers .rsp).toNat + 8 < 2^64
  canonicalStackAfter : canonical (initial.registers .rsp + 8) = true
  alignment : (initial.registers .rsp).toNat % 16 = 8

/-- The ordinary System V integer caller-saved set, plus the consumed return
slot's stack-pointer update. The six callee-saved GPRs must survive. -/
def clobbers : List Register :=
  [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp]

structure Post (input : Input) (initial final : State) : Prop where
  value : (final.registers .rax).toNat = resultNat input.value
  outside : ∀ query, ¬input.frame.Contains query →
    final.memory.read query = initial.memory.read query
  executable : final.memory.executable = initial.memory.executable
  writable : final.memory.writable = initial.memory.writable
  returnAddress : final.rip = input.target
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register, register ∉ clobbers →
    final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

/-- Every contained private write remains below the original caller slot. -/
theorem Pre.slot_below_caller {program input initial address}
    (pre : Pre program input initial) (inside : PrivateSlot input.frame address) :
    address.toNat + 8 ≤ (initial.registers .rsp).toNat := by
  rw [← pre.frameTop]
  exact inside.2

end EDSL.CallStack
