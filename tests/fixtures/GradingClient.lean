/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known

set_option warningAsError true

namespace GradingExportClientFixture
open EDSL EDSL.Grading

-- A fresh type dependency in a constructor header, rather than only in a
-- theorem body. Header is parameterized and universe-polymorphic.
def Target : Prop := Claim .pair32 Pair32.bytes

inductive Header (α : Type u) : Type u where
  | checked (payload : α) (proof : Target) : Header α

opaque sealed : Header Unit := Header.checked () Known.pair

noncomputable def unpack {α : Type u} (header : Header α) : Subtype (fun _ : α => Target) :=
  Header.rec (motive := fun _ => Subtype (fun _ : α => Target))
    (fun payload proof => ⟨payload, proof⟩) header

theorem extract {α : Type u} (header : Header α) : Target :=
  (unpack header).property

mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | step {n : Nat} : Odd n → Even (n + 1)
  inductive Odd : Nat → Prop where
    | step {n : Nat} : Even n → Odd (n + 1)
end

theorem witness : Even 2 := Even.step (Odd.step Even.zero)

theorem release (_ : Even 2) (header : Header Unit) : Target := extract header

theorem pair : Claim .pair32 Pair32.bytes := release witness sealed

/-- An unapplied client assumption is not a proof of the fixed task contract. -/
theorem extraHypothesis (hypothesis : Claim .pair32 Pair32.bytes) :
    Claim .pair32 Pair32.bytes := hypothesis

theorem polymorphic {α : Type u} (value : α) : value = value := rfl

-- Its use as a proof dependency must produce an explicit unsupported result.
inductive Nested where
  | node : List Nested → Nested

theorem afterNested (_ : Nested) : Target := Known.pair

theorem nestedPair : Claim .pair32 Pair32.bytes := afterNested (.node [])

#print axioms pair

end GradingExportClientFixture
