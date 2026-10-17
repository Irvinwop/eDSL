/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Contract

set_option warningAsError true

namespace EDSL.X86

/-- An already enabled ordinary qword store remains enabled after replacing
the same eight bytes. The premise supplies both mapping and permissions;
unchecked writes alone do not establish write authority. -/
theorem canStoreQWord_after_write (memory : Memory) (address value : Word)
    (allowed : canStoreQWord memory address = true) :
    canStoreQWord (writeQWordUnchecked memory address value) address = true := by
  have addressable := (Bool.and_eq_true_iff.mp allowed).1
  have writable := (Bool.and_eq_true_iff.mp allowed).2
  simp only [qwordWritable, Bool.and_eq_true] at writable
  simpa [canStoreQWord, addressable, qwordWritable, writeQWordUnchecked,
    storedQWordByte] using writable.1

end EDSL.X86

namespace EDSL.X86.Sequential
open EDSL.OS

/-- A complete positive instruction span inside admitted code is a real
nonwrapping subregion. This does not assume the instruction decodes. -/
theorem code_fetch_span {memory : Memory} {base : Word} {bytes : List Byte}
    (code : CodeAt memory base bytes) (before : State) (instruction : Instruction)
    (offset : Nat) (pc : before.rip = base + BitVec.ofNat 64 offset)
    (span : offset + instruction.length ≤ bytes.length) :
    Borrowing.Subregion ⟨before.rip, instruction.length⟩ ⟨base, bytes.length⟩ := by
  have limit := code.1
  have positive := instruction.length_pos
  have small : offset < 2^64 := by omega
  have total : base.toNat + offset < 2^64 := by omega
  have natural : (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
  change base.toNat ≤ before.rip.toNat ∧
    before.rip.toNat + instruction.length ≤ base.toNat + bytes.length
  rw [pc, natural]
  omega

end EDSL.X86.Sequential
