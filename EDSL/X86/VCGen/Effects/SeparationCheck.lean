/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects.Frames

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Finite reflection of the existing `CodeSeparated` authorization predicate.
The shared footprint check uses exactly the modular byte-address differences
in `DWordDisjoint` and `QWordDisjoint`, including wrapped and empty windows.
It requires no address ordering, no-wrap or memory-permission premise.

Ordinary stores reuse their actual prestate intent descriptors. The two legacy
atomic instructions use their exact four-byte prestate RDI footprints. Readonly
and footprint branches are independent alternatives, without an exclusivity
assumption. Neither store values nor final-memory equality authorize a write.
A false result is refusal of this policy, never evidence of a defect.

The separate `codeSeparatedPolicy_codeFrame` theorem remains the code-frame
bridge. This checker supplies no OS, scheduling, TSO, linearizability, hardware
or corpus claim.
-/

namespace EDSL.X86.VCGen.Effects

/-- Check every byte of the selected window against a modular write footprint.
The width is measured in bytes, independently of the stored value. -/
def checkCodeFootprint (width : Nat) (address base : Word) (length : Nat) : Bool :=
  (List.range length).all fun offset =>
    decide (width ≤ ((base + BitVec.ofNat 64 offset) - address).toNat)

/-- Finite checking is equivalent to the exact universal bounded footprint
condition, without imposing any additional address or length bounds. -/
theorem checkCodeFootprint_iff (width : Nat) (address base : Word) (length : Nat) :
    checkCodeFootprint width address base length = true ↔
      ∀ offset, offset < length →
        width ≤ ((base + BitVec.ofNat 64 offset) - address).toNat := by
  simp only [checkCodeFootprint, List.all_eq_true, List.mem_range, decide_eq_true_eq]

theorem checkCodeFootprint_dword_iff (address base : Word) (length : Nat) :
    checkCodeFootprint 4 address base length = true ↔ DWordDisjoint address base length :=
  checkCodeFootprint_iff 4 address base length

theorem checkCodeFootprint_qword_iff (address base : Word) (length : Nat) :
    checkCodeFootprint 8 address base length = true ↔ QWordDisjoint address base length :=
  checkCodeFootprint_iff 8 address base length

/-- Decide separation through any existing authorization constructor. Store
addresses come from the actual instruction and prestate; stored values are
ignored. A false result refuses this policy and makes no defect claim. -/
def checkCodeSeparated (bytes : List Byte) (base : Word) (before : State)
    (instruction : Sequential.Instruction) : Bool :=
  Sequential.CFG.readOnly instruction ||
    ((instruction.storeIntent before).any (fun intent =>
        checkCodeFootprint 4 intent.1 base bytes.length) ||
      ((instruction.storeIntent64 before).any (fun intent =>
          checkCodeFootprint 8 intent.1 base bytes.length) ||
        ((decide (instruction = .legacy .exchangeEaxRdi) ||
            decide (instruction = .legacy .fetchAddEaxRdi)) &&
          checkCodeFootprint 4 (before.registers .rdi) base bytes.length)))

/-- Soundness and completeness for all five constructors, even when several
constructors authorize the same instruction and window. -/
theorem checkCodeSeparated_iff (bytes : List Byte) (base : Word) (before : State)
    (instruction : Sequential.Instruction) :
    checkCodeSeparated bytes base before instruction = true ↔
      CodeSeparated bytes base before instruction := by
  simp only [checkCodeSeparated, Bool.or_eq_true_iff, Bool.and_eq_true_iff,
    decide_eq_true_eq, Option.any_eq_true, checkCodeFootprint_dword_iff,
    checkCodeFootprint_qword_iff]
  constructor
  · rintro (allowed | store32 | store64 | atomic)
    · exact CodeSeparated.readOnly allowed
    · rcases store32 with ⟨⟨address, value⟩, intent, disjoint⟩
      exact CodeSeparated.store32 intent disjoint
    · rcases store64 with ⟨⟨address, value⟩, intent, disjoint⟩
      exact CodeSeparated.store64 intent disjoint
    · rcases atomic with ⟨exchange | fetchAdd, disjoint⟩
      · subst instruction
        exact CodeSeparated.exchange disjoint
      · subst instruction
        exact CodeSeparated.fetchAdd disjoint
  · intro separated
    cases separated with
    | readOnly allowed => exact Or.inl allowed
    | @store32 instruction address value intent disjoint =>
      exact Or.inr (Or.inl ⟨(address, value), intent, disjoint⟩)
    | @store64 instruction address value intent disjoint =>
      exact Or.inr (Or.inr (Or.inl ⟨(address, value), intent, disjoint⟩))
    | exchange disjoint =>
      exact Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, disjoint⟩))
    | fetchAdd disjoint =>
      exact Or.inr (Or.inr (Or.inr ⟨Or.inr rfl, disjoint⟩))

/-- A computational decision obtained only from the Boolean checker and its
 equivalence with the existing predicate. -/
def decidableCodeSeparated (bytes : List Byte) (base : Word) (before : State)
    (instruction : Sequential.Instruction) : Decidable (CodeSeparated bytes base before instruction) :=
  if checked : checkCodeSeparated bytes base before instruction = true then
    isTrue ((checkCodeSeparated_iff bytes base before instruction).mp checked)
  else
    isFalse (fun separated =>
      checked ((checkCodeSeparated_iff bytes base before instruction).mpr separated))

#print axioms checkCodeFootprint
#print axioms checkCodeFootprint_iff
#print axioms checkCodeFootprint_dword_iff
#print axioms checkCodeFootprint_qword_iff
#print axioms checkCodeSeparated
#print axioms checkCodeSeparated_iff
#print axioms decidableCodeSeparated

end EDSL.X86.VCGen.Effects

#audit_edsl
