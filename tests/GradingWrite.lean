/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Write32.Accounting
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.GradingWrite
open X86 X86.Sequential Grading OS

-- Unsupported code is not filtered out of the current resource domain by an
-- assumed decoder/CFG/run result. Its real initial-prefix obligation rejects.
theorem unsupported_not_claim : ¬Claim .write32 [0xff] := by
  intro claim
  let witness := Write32.Domain.unsupported
  let resource : Write32.Resources :=
    ⟨witness.shared, witness.call, witness.initial.registers .rsi, witness.oldValue⟩
  have pre : Write32.ResourcePre [0xff] resource witness.initial :=
    ⟨witness.current, witness.raw.codeBytes, witness.raw.entry, witness.raw.stackPointer,
      witness.raw.targetPointer, rfl, witness.raw.old⟩
  have policy := (claim.1.machine (Write32.resourceInput resource) witness.initial pre.machine).2
  obtain ⟨_, decoded, _, _⟩ := policy.prefix (Block.nil (choices := fun _ => false))
  rw [Write32.Domain.unsupported_rejected] at decoded
  cases decoded

-- A RET-only candidate has a real admitted caller and completes successfully,
-- but cannot implement the independently required change of target value.
theorem no_op_not_claim : ¬Claim .write32 [0xc3] := by
  intro claim
  let witness := Write32.Domain.candidate [0xc3] (by decide) (by decide)
  let resource : Write32.Resources :=
    ⟨witness.shared, witness.call, witness.initial.registers .rsi, witness.oldValue⟩
  have pre : Write32.ResourcePre [0xc3] resource witness.initial :=
    ⟨witness.current, witness.raw.codeBytes, witness.raw.entry, witness.raw.stackPointer,
      witness.raw.targetPointer, rfl, witness.raw.old⟩
  let final := WordResources.returnAfter witness.initial witness.call.returnAddress
  have first := pre.machine.code.2 0 0xc3 (by decide)
  simp only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] at first
  have decoded : Sequential.decodeAt witness.initial = .ok (.legacy .ret) := by
    apply decodeAt_legacy
    simp [X86.decodeAt, first]
  have actual := (WordResources.current_ret_step pre.current decoded pre.stack false).1
  obtain ⟨result, execution, post⟩ :=
    (claim.1.machine (Write32.resourceInput resource) witness.initial pre.machine).1 (fun _ => false)
  have same := Sequential.Executes.fixed_choices_unique execution
    (Sequential.Executes.ret (choices := fun _ => false) actual)
  rw [same] at post
  exact Write32.useful_requires_memory_change pre.machine witness.raw.useful post rfl

-- The real mutation gate checks the whole borrowed allocation, even when a
-- store is disjoint from the particular subregion of one live loan.
theorem borrowed_allocation_rejected {shared : Borrowing.State} {identifier : Nat}
    {loan : Borrowing.Loan} {ticket : Ownership.Ticket}
    (valid : Borrowing.WellFormed shared)
    (live : shared.loans identifier = some loan)
    (same : ticket.identifier = loan.ticket.identifier)
    (owner : Nat) (address : Word) (value : BitVec 32) :
    Borrowing.mutate shared (.store owner ticket address value) = .error .borrowed := by
  have blocked : Borrowing.allowed shared (.store owner ticket address value) ≠ true := by
    intro checked
    have excluded := Borrowing.allowed_sound shared (.store owner ticket address value)
      valid checked identifier loan live
    exact excluded (by simp [Ownership.Mutation.target, same])
  have denied : Borrowing.allowed shared (.store owner ticket address value) = false :=
    Bool.eq_false_iff.mpr blocked
  simp [Borrowing.mutate, denied]

end EDSL.Tests.GradingWrite

#audit_edsl
