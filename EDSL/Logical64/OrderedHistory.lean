/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Logical64.Contract

set_option warningAsError true

namespace EDSL.Logical64
open X86 X86.Sequential

/-- Independent ordered set-operation semantics. Every request occurrence has
its own intermediate full64 word and bit-membership contract. No instruction,
machine evaluator, folded implementation, count restriction or scheduling fact
is part of this relation. In particular unchanged requests remain present. -/
inductive OrderedMathematicalResult : Word → List (Operation × Word) → Word → Prop where
  | nil {initial} : OrderedMathematicalResult initial [] initial
  | cons {initial operation mask intermediate rest final}
      (head : MathematicalResult operation initial mask intermediate)
      (tail : OrderedMathematicalResult intermediate rest final) :
      OrderedMathematicalResult initial ((operation, mask) :: rest) final

theorem OrderedMathematicalResult.nil_iff {initial final : Word} :
    OrderedMathematicalResult initial [] final ↔ final = initial := by
  constructor
  · intro result
    cases result
    rfl
  · intro same
    subst final
    exact .nil

theorem OrderedMathematicalResult.cons_iff
    {initial final mask : Word} {operation : Operation} {rest : List (Operation × Word)} :
    OrderedMathematicalResult initial ((operation, mask) :: rest) final ↔
      ∃ intermediate, MathematicalResult operation initial mask intermediate ∧
        OrderedMathematicalResult intermediate rest final := by
  constructor
  · intro result
    cases result with
    | cons head tail => exact ⟨_, head, tail⟩
  · rintro ⟨intermediate, head, tail⟩
    exact .cons head tail

/-- An exact request list fixes the answer, even for mixed operations. This
does not permit reordering the list or replacing it by a homogeneous task. -/
theorem OrderedMathematicalResult.unique
    {initial first second : Word} {requests : List (Operation × Word)}
    (left : OrderedMathematicalResult initial requests first)
    (right : OrderedMathematicalResult initial requests second) : first = second := by
  induction left generalizing second with
  | nil => exact (nil_iff.mp right).symm
  | cons head _ induction =>
    obtain ⟨intermediate, otherHead, otherTail⟩ := cons_iff.mp right
    have same := head.unique otherHead
    subst intermediate
    exact induction otherTail

theorem OrderedMathematicalResult.append
    {initial intermediate final : Word} {earlier later : List (Operation × Word)}
    (first : OrderedMathematicalResult initial earlier intermediate)
    (second : OrderedMathematicalResult intermediate later final) :
    OrderedMathematicalResult initial (earlier ++ later) final := by
  induction first with
  | nil => exact second
  | cons head _ induction => exact .cons head (induction second)

/-- Composition also splits at every occurrence boundary; neither cancelled
updates nor operations with an unchanged result are discarded. -/
theorem OrderedMathematicalResult.append_iff
    {initial final : Word} {earlier later : List (Operation × Word)} :
    OrderedMathematicalResult initial (earlier ++ later) final ↔
      ∃ intermediate, OrderedMathematicalResult initial earlier intermediate ∧
        OrderedMathematicalResult intermediate later final := by
  constructor
  · induction earlier generalizing initial with
    | nil => intro result; exact ⟨initial, .nil, result⟩
    | cons request rest induction =>
      intro result
      obtain ⟨intermediate, head, tail⟩ := cons_iff.mp result
      obtain ⟨boundary, first, last⟩ := induction tail
      exact ⟨boundary, .cons head first, last⟩
  · rintro ⟨intermediate, first, second⟩
    exact first.append second

/-- A mathematical XOR request followed immediately by the same request
cancels. The intermediate occurrence still exists in the ordered relation. -/
theorem MathematicalResult.symmetricDifference_cancel
    {initial intermediate final mask : Word}
    (first : MathematicalResult .symmetricDifference initial mask intermediate)
    (second : MathematicalResult .symmetricDifference intermediate mask final) : final = initial := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index inside
  have left := first ⟨index, inside⟩
  have right := second ⟨index, inside⟩
  have membership : HasBit final ⟨index, inside⟩ ↔ HasBit initial ⟨index, inside⟩ := by
    by_cases initialBit : HasBit initial ⟨index, inside⟩ <;>
      by_cases maskBit : HasBit mask ⟨index, inside⟩ <;>
      simp_all
  exact Bool.coe_iff_coe.mp (by simpa only [HasBit, BitVec.testBit_toNat] using membership)

theorem OrderedMathematicalResult.symmetricDifference_pair
    {initial final mask : Word}
    (result : OrderedMathematicalResult initial
      [(.symmetricDifference, mask), (.symmetricDifference, mask)] final) : final = initial := by
  obtain ⟨middle, first, rest⟩ := cons_iff.mp result
  obtain ⟨last, second, done⟩ := cons_iff.mp rest
  have same := nil_iff.mp done
  subst final
  exact first.symmetricDifference_cancel second

/-- The uninterrupted three-request body still solves union. This says
nothing about a peer request inserted between the final two occurrences. -/
theorem OrderedMathematicalResult.union_xor_xor
    {initial final mask : Word}
    (result : OrderedMathematicalResult initial
      [(.union, mask), (.symmetricDifference, mask), (.symmetricDifference, mask)] final) :
    MathematicalResult .union initial mask final := by
  obtain ⟨middle, first, rest⟩ := cons_iff.mp result
  have same := rest.symmetricDifference_pair
  subst final
  exact first

end EDSL.Logical64
