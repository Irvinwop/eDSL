/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.ModuloCounter

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Arithmetic transport under chronological relabeling.

Changing a sequential call's identity or thread does not change its arithmetic
contract. The relation below pairs occurrences in order, including repeated
values; it does not supply a permutation or a complete-call protocol.
-/

namespace EDSL.Concurrency.ModuloCounter

/-- Project-scoped heterogeneous list relation. The pinned Lean core has no
`List.Forall₂`; keep this small equivalent out of the core `List` namespace. -/
inductive Forall₂ {α β : Type} (relation : α → β → Prop) : List α → List β → Prop where
  | nil : Forall₂ relation [] []
  | cons {left : α} {right : β} {lefts : List α} {rights : List β}
      (head : relation left right) (tail : Forall₂ relation lefts rights) :
      Forall₂ relation (left :: lefts) (right :: rights)

theorem Forall₂.of_map {α β γ : Type} {relation : β → γ → Prop}
    (left : α → β) (right : α → γ) (items : List α)
    (related : ∀ item, relation (left item) (right item)) :
    Forall₂ relation (items.map left) (items.map right) := by
  induction items with
  | nil => exact .nil
  | cons item items ih => exact .cons (related item) ih

/-- Both operation arguments and entire replies agree. Identities and thread
labels may change independently, even to different types. -/
def SameValues {width : Nat} {Id Thread Id' Thread' : Type}
    (left : Call width Id Thread) (right : Call width Id' Thread') : Prop :=
  left.input = right.input ∧ left.output = right.output

/-- Preserve the exact initial/final words and all chronological occurrences.
No injectivity, actor interpretation, id uniqueness or protocol is required. -/
theorem Sequential.relabel {width : Nat} {Id Thread Id' Thread' : Type}
    {prior final : BitVec width} {calls : List (Call width Id Thread)}
    {relabeled : List (Call width Id' Thread')}
    (legal : Sequential prior calls final)
    (related : Forall₂ SameValues calls relabeled) :
    Sequential prior relabeled final := by
  induction related generalizing prior with
  | nil =>
    cases legal with
    | nil => exact .nil _
  | cons same _ ih =>
    cases legal with
    | cons step tail =>
      refine .cons ?_ (ih tail)
      rw [← same.1, ← same.2]
      exact step

#print axioms Forall₂.of_map
#print axioms Sequential.relabel

end EDSL.Concurrency.ModuloCounter

#audit_edsl
