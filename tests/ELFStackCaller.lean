/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.CallerResources.Stack

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ELFStackCaller
open X86 OS OS.AddressSpace
open ELF.CallerResources

-- An unaligned upper-half slot and independently specified nonzero high bytes.
private def high : Space := Stack.prior 0xffff800000001003 0xfedcba9876543210

example : loadDWord (toMemory high) 0xffff800000001003 = .ok 0x76543210 ∧
    loadDWord (toMemory high) 0xffff800000001007 = .ok 0xfedcba98 := ⟨rfl, rfl⟩

-- Real protection must hide the last byte from the complete RET read without
-- losing its contents; restoring permission must recover the original word.
private def protectedReturn : Except AddressSpace.Fault
    (Except X86.Error Word × Option Byte × Except X86.Error Word) := do
  let hidden ← AddressSpace.protect high ⟨0xffff80000000100a, 1⟩ inaccessible
  let restored ← AddressSpace.protect hidden ⟨0xffff80000000100a, 1⟩ readOnly
  return (readWord (toMemory hidden) 0xffff800000001003,
    contents hidden 0xffff80000000100a,
    readWord (toMemory restored) 0xffff800000001003)

example : protectedReturn = .ok
    (.error (.inaccessibleStack 0xffff80000000100a), some 0xfe, .ok 0xfedcba9876543210) := by rfl

example : allUnmapped high ⟨0xffff800000001002, 1⟩ = true ∧
    allUnmapped high ⟨0xffff80000000100b, 1⟩ = true ∧
    readStackByte (toMemory high) 0xffff80000000100b =
      .error (.inaccessibleStack 0xffff80000000100b) ∧
    fetchByte (toMemory high) 0xffff800000001003 =
      .error (.inaccessibleInstruction 0xffff800000001003) ∧
    AddressSpace.writeByte high 0xffff800000001003 0 = .error .denied :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- A one-byte LOAD ends exactly at the next page. Extending its BSS by one byte
-- occupies that entire next rounded page, even far beyond the exact segment.
private def tail : ELF.Segment := ⟨0xfff, 0x6fffff, 1, 1, 5, 4096⟩
private def adjacent : ELF.Image := ⟨0x6fffff, [tail]⟩
private def overlapping : ELF.Image := ⟨0x6fffff, [{ tail with memorySize := 2 }]⟩

example : Stack.check adjacent 0x700000 = true ∧
    Stack.check overlapping 0x700008 = false := by decide

-- Without page validity, this wrapping interval would look disjoint from a
-- low slot even though its enumerated addresses wrap into that slot.
example : Stack.check ⟨0, [⟨0, 0xfffffffffffff000, 0, 8192, 4, 4096⟩]⟩ 0x100 = false ∧
    Stack.check adjacent 0x800000000000 = false := by decide

-- Prove actual freshness through the sufficient check, avoiding 4096 bytes.
example : ELF.fresh adjacent (Stack.prior 0x700000 0x654321) = true :=
  Stack.check_sound adjacent 0x700000 0x654321 (by decide)

-- The original predicate really rejects rounded-page overlap. Its rejection is
-- established from one mapped byte, without reducing an entire page list.
example : ELF.fresh overlapping (Stack.prior 0x700008 0x654321) = false := by
  cases observed : ELF.fresh overlapping (Stack.prior 0x700008 0x654321) with
  | false => rfl
  | true =>
    unfold ELF.fresh at observed
    have unmapped : allUnmapped (Stack.prior 0x700008 0x654321)
        ({ tail with memorySize := 2 } : ELF.Segment).pageRegion = true :=
      List.all_eq_true.mp observed _ List.mem_cons_self
    have absent := allUnmapped_inside _ _ unmapped 0x700008 (by decide)
    change some (⟨0x21, readOnly⟩ : Cell) = none at absent
    cases absent

-- A canonical-hole slot and a wrapping eight-byte slot cannot acquire Facts.
example (target : Word) : ¬(Stack.caller 1 2 3 0x800000000000 target).Facts := by
  intro claimed
  exact (by decide : ¬(Stack.region 0x800000000000).valid = true) claimed.valid

example (target : Word) : ¬(Stack.caller 1 2 3 0xfffffffffffffffc target).Facts := by
  intro claimed
  exact (by decide : ¬(Stack.region 0xfffffffffffffffc).valid = true) claimed.valid

-- Even a complete readable slot at the final eight addresses cannot satisfy
-- the strict post-return stack bound. Crossing the canonical hole also fails.
example (target : Word) : ¬(Stack.caller 1 2 3 0xfffffffffffffff8 target).Facts := by
  intro claimed
  exact (by decide : ¬(0xfffffffffffffff8 : Word).toNat + 8 < 2^64) claimed.stackBound

example (target : Word) : ¬(Stack.caller 1 2 3 0x7ffffffffff8 target).Facts := by
  intro claimed
  exact (by decide : ¬canonical ((0x7ffffffffff8 : Word) + 8) = true) claimed.postStackCanonical

example : ¬(Stack.caller 1 2 3 0x700008 0x800000000000).Facts := by
  intro claimed
  exact (by decide : ¬canonical (0x800000000000 : Word) = true) claimed.returnCanonical

end EDSL.Tests.ELFStackCaller
