/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Memory

namespace EDSL.X86

/-- A readable, nonwrapping byte snapshot, independent of execute permission.
The caller keeps these bytes stable throughout the synchronous operation. -/
def BufferAt (memory : Memory) (base : Word) (bytes : List Byte) : Prop :=
  base.toNat + bytes.length ≤ 2^64 ∧
  ∀ offset byte, bytes[offset]? = some byte →
    readDataByte memory (base + BitVec.ofNat 64 offset) = .ok byte

/-- Executable bytes are also readable in the current memory interface. -/
theorem CodeAt.readable {memory : Memory} {base : Word} {bytes : List Byte}
    (code : CodeAt memory base bytes) : BufferAt memory base bytes := by
  refine ⟨code.1, ?_⟩
  intro offset byte present
  have fetched := code.2 offset byte present
  unfold fetchByte at fetched
  split at fetched
  next allowed =>
    have canonical := (Bool.and_eq_true_iff.mp allowed).1
    cases read : memory.read (base + BitVec.ofNat 64 offset) with
    | none => simp [read] at fetched
    | some observed =>
      have same := Except.ok.inj (by simpa only [read] using fetched)
      cases same
      simp [readDataByte, canonical, read]
  next => cases fetched

/-- Executable subrange binding retains the parent window's nonwrapping bound. -/
theorem CodeAt.window {memory : Memory} {base : Word} {bytes part : List Byte}
    (code : CodeAt memory base bytes) (offset : Nat)
    (inside : offset + part.length ≤ bytes.length)
    (start : base.toNat + offset < 2^64)
    (matching : ∀ index byte, part[index]? = some byte → bytes[offset + index]? = some byte) :
    CodeAt memory (base + BitVec.ofNat 64 offset) part := by
  have baseNat : (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have small : offset < 2^64 := by omega
    rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt start]
  refine ⟨by rw [baseNat]; have bound := code.1; omega, ?_⟩
  intro index byte present
  have fetched := code.2 (offset + index) byte (matching index byte present)
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using fetched

end EDSL.X86
