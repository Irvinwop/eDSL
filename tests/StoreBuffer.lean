/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.StoreBuffer
import EDSL.Audit

namespace EDSL.Tests.StoreBuffer
open X86 X86.StoreBuffer

/-- Ordinary RAM with a deliberately denied fourth byte and one unmapped byte. -/
def ram : Memory where
  read address := if address = 0x3000 then none else some 0xa5
  executable := fun _ => false
  writable address := decide (address ≠ 0x2003)

def first : Store := ⟨0x1000, 0x11223344⟩
def overlapping : Store := ⟨0x1001, 0xaabbccdd⟩
def replacement : Store := ⟨0x1000, 0x76543210⟩

-- Independent little-endian expectations expose the order of overlapping
-- stores and the distinction between byte forwarding and whole-word matching.
example : loadDWord (view ram [first, overlapping]) 0x1000 = .ok 0xbbccdd44 := by rfl
example : loadDWord (view ram [overlapping, first]) 0x1000 = .ok 0x11223344 := by rfl
example : loadDWord (view ram [first, overlapping]) 0x1002 = .ok 0xa5aabbcc := by rfl
example : loadDWord (view ram (enqueue [first, overlapping] replacement)) 0x1000 =
    .ok 0x76543210 := by rfl

-- A FIFO publication removes the oldest entry while retaining the same
-- overlapping-byte observation, including the byte only present in global RAM.
example : loadDWord
    (view (writeDWordUnchecked ram first.address first.value) [overlapping]) 0x1000 =
    .ok 0xbbccdd44 := by rfl
example : loadDWord
    (view (writeDWordUnchecked ram first.address first.value) [overlapping]) 0x1002 =
    .ok 0xa5aabbcc := by rfl

-- Buffered stores cannot grant permission to a denied fourth byte or make an
-- unrelated missing byte accessible. Both fail at the complete-word check.
example : canStoreDWord (view ram [first, overlapping]) 0x2000 = false := by rfl
example : storeDWord (view ram [first, overlapping]) 0x2000 7 =
    .error (.writeDenied 0x2000) := by rfl
example : canStoreDWord (view ram [first, overlapping]) 0x3000 = false := by rfl
example : loadDWord (view ram [first, overlapping]) 0x3000 =
    .error (.inaccessibleData 0x3000) := by rfl

theorem separate_data : Separate 0x1000 0x2000 := by
  intro query
  by_cases outside : 4 ≤ (query - (0x1000 : Word)).toNat
  · exact Or.inl outside
  · right
    have offsets : (query - (0x1000 : Word)).toNat = 0 ∨
        (query - (0x1000 : Word)).toNat = 1 ∨
        (query - (0x1000 : Word)).toNat = 2 ∨
        (query - (0x1000 : Word)).toNat = 3 := by omega
    rcases offsets with h | h | h | h
    · rw [query_of_offset 0x1000 query 0 (by decide) h]
      decide
    · rw [query_of_offset 0x1000 query 1 (by decide) h]
      decide
    · rw [query_of_offset 0x1000 query 2 (by decide) h]
      decide
    · rw [query_of_offset 0x1000 query 3 (by decide) h]
      decide

-- This observation combines global publication, a pending own write and
-- independence. The quantified commutation proof moves publication past the
-- overlay before checking the independently specified payload value.
example (initial : Memory) (payload published : BitVec 32) :
    loadDWord (view (writeDWordUnchecked initial 0x2000 published)
      [⟨0x1000, payload⟩]) 0x1000 = .ok payload := by
  rw [view_write_commute _ _ _ _ (by
    intro store member
    simp only [List.mem_singleton] at member
    subst store
    exact separate_data)]
  apply (loadDWord_congr _ _ _ (writeDWord_agrees _ _ _ _ _ (by
    intro offset bound
    have outside : 4 ≤ ((0x1000 : Word) + BitVec.ofNat 64 offset - 0x2000).toNat := by
      rcases show offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 by omega with
        h | h | h | h <;> subst offset <;> decide
    exact outside))).trans
  exact load_after_write initial 0x1000 payload (by decide)

end EDSL.Tests.StoreBuffer

#audit_edsl
