/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Logical64.Contract

set_option warningAsError true

namespace EDSL.Logical64
open X86 X86.Sequential

/-- An implementation adapter kept outside the independent contract. -/
def Operation.toLogicalOp : Operation → LogicalOp
  | .intersection => .band
  | .union => .bor
  | .symmetricDifference => .bxor

theorem eval_mathematical (operation : Operation) (left right : Word) :
    MathematicalResult operation left right (operation.toLogicalOp.eval left right) := by
  cases operation <;> intro index <;>
    simp [Operation.toLogicalOp,LogicalOp.eval,HasBit,BitVec.testBit_toNat]
  cases left[index.val] <;> cases right[index.val] <;> decide

theorem HasBit.or_iff (left right : Word) (index : Fin 64) :
    HasBit (left ||| right) index ↔ HasBit left index ∨ HasBit right index := by
  simp [HasBit,BitVec.testBit_toNat]

/-- Value folding alone does not establish atomicity or a valid event history.
A later history proof must bind this list to its actual current-state events. -/
def unionMasks : Word → List Word → Word
  | initial, [] => initial
  | initial, mask :: rest => unionMasks (initial ||| mask) rest

/-- Every bit after a union fold came from the initial word or an actual list
member, and every such bit survives, including duplicate and overlapping masks. -/
theorem unionMasks_membership (initial : Word) (masks : List Word) (index : Fin 64) :
    HasBit (unionMasks initial masks) index ↔
      HasBit initial index ∨ ∃ mask ∈ masks, HasBit mask index := by
  induction masks generalizing initial with
  | nil => simp [unionMasks]
  | cons mask rest induction =>
    rw [unionMasks,induction,HasBit.or_iff]
    constructor
    · intro membership
      rcases membership with (fromInitial | fromMask) | ⟨other,member,fromOther⟩
      · exact Or.inl fromInitial
      · exact Or.inr ⟨mask,by simp,fromMask⟩
      · exact Or.inr ⟨other,List.mem_cons_of_mem _ member,fromOther⟩
    · intro membership
      rcases membership with fromInitial | ⟨other,member,fromOther⟩
      · exact Or.inl (Or.inl fromInitial)
      · rcases List.mem_cons.mp member with same | tail
        · subst other
          exact Or.inl (Or.inr fromOther)
        · exact Or.inr ⟨other,tail,fromOther⟩

end EDSL.Logical64
