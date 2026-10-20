/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Logical64.Algebra

set_option warningAsError true

namespace EDSL.Logical64
open X86 X86.Sequential

local instance (word : Word) (index : Fin 64) : Decidable (HasBit word index) :=
  inferInstanceAs (Decidable (word.toNat.testBit index = true))

theorem HasBit.and_iff (left right : Word) (index : Fin 64) :
    HasBit (left &&& right) index ↔ HasBit left index ∧ HasBit right index := by
  simp [HasBit, BitVec.testBit_toNat]

theorem HasBit.xor_iff (left right : Word) (index : Fin 64) :
    HasBit (left ^^^ right) index ↔
      (HasBit left index ∧ ¬HasBit right index) ∨
      (HasBit right index ∧ ¬HasBit left index) := by
  exact eval_mathematical .symmetricDifference left right index

/-- Pure value folding establishes no atomicity, lifetime or schedule fact.
The checked OS trace must supply the masks and current-before chain. -/
def intersectMasks : Word → List Word → Word
  | initial, [] => initial
  | initial, mask :: rest => intersectMasks (initial &&& mask) rest

def xorMasks : Word → List Word → Word
  | initial, [] => initial
  | initial, mask :: rest => xorMasks (initial ^^^ mask) rest

/-- Intersection keeps an initial bit exactly when every actual mask has it.
The empty list keeps the entire initial word. -/
theorem intersectMasks_membership (initial : Word) (masks : List Word) (index : Fin 64) :
    HasBit (intersectMasks initial masks) index ↔
      HasBit initial index ∧ ∀ mask ∈ masks, HasBit mask index := by
  induction masks generalizing initial with
  | nil => simp [intersectMasks]
  | cons mask rest induction =>
    rw [intersectMasks, induction, HasBit.and_iff]
    simp only [List.mem_cons, forall_eq_or_imp]
    exact and_assoc

/-- Cardinality of actual mask occurrences containing a bit. Duplicates count;
unlike union/intersection, two equal XOR updates cancel. This definition uses
natural-number bit membership, not a machine XOR or a folded implementation. -/
def bitOccurrences (masks : List Word) (index : Fin 64) : Nat :=
  masks.countP (fun mask => mask.toNat.testBit index)

@[simp] theorem bitOccurrences_nil (index : Fin 64) : bitOccurrences [] index = 0 := rfl

theorem bitOccurrences_cons (mask : Word) (rest : List Word) (index : Fin 64) :
    bitOccurrences (mask :: rest) index =
      bitOccurrences rest index + if HasBit mask index then 1 else 0 := by
  simp only [bitOccurrences, List.countP_cons]
  congr 1

/-- Symmetric difference is specified by odd cardinality of the initial bit
and all actual mask occurrences. No distinctness or nonzero mask is assumed. -/
theorem xorMasks_membership (initial : Word) (masks : List Word) (index : Fin 64) :
    HasBit (xorMasks initial masks) index ↔
      ((if HasBit initial index then 1 else 0) + bitOccurrences masks index) % 2 = 1 := by
  induction masks generalizing initial with
  | nil => by_cases bit : HasBit initial index <;> simp [xorMasks, bit]
  | cons mask rest induction =>
    rw [xorMasks, induction, bitOccurrences_cons]
    have bit := HasBit.xor_iff initial mask index
    by_cases left : HasBit initial index <;> by_cases right : HasBit mask index <;>
      simp [left, right] at bit ⊢ <;> simp [bit] <;> omega

/-- Mixed operations are retained in order. The homogeneous membership
theorems apply only when a checked trace proves the corresponding op tags. -/
def applyUpdates : Word → List (LogicalOp × Word) → Word
  | initial, [] => initial
  | initial, (op, mask) :: rest => applyUpdates (op.eval initial mask) rest

theorem applyUpdates_intersection (initial : Word) (masks : List Word) :
    applyUpdates initial (masks.map (fun mask => (.band, mask))) = intersectMasks initial masks := by
  induction masks generalizing initial with
  | nil => rfl
  | cons mask rest induction =>
    exact induction (initial &&& mask)

theorem applyUpdates_union (initial : Word) (masks : List Word) :
    applyUpdates initial (masks.map (fun mask => (.bor, mask))) = unionMasks initial masks := by
  induction masks generalizing initial with
  | nil => rfl
  | cons mask rest induction =>
    exact induction (initial ||| mask)

theorem applyUpdates_symmetricDifference (initial : Word) (masks : List Word) :
    applyUpdates initial (masks.map (fun mask => (.bxor, mask))) = xorMasks initial masks := by
  induction masks generalizing initial with
  | nil => rfl
  | cons mask rest induction =>
    exact induction (initial ^^^ mask)

end EDSL.Logical64
