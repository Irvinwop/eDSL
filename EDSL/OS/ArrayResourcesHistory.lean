/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.ArrayResourcesArithmetic

namespace EDSL.OS.ArrayResources
open X86 AddressSpace

theorem surviving_loan {before after : Borrowing.State} {worker identifier : Nat} {region : Region}
    (loan : Threads.HasLoan before worker identifier region) (valid : Borrowing.WellFormed before)
    (history : Borrowing.History before after) (survives : (after.loans identifier).isSome = true) :
    after.loans identifier = before.loans identifier := by
  obtain ⟨record, live, _, _⟩ := loan
  cases endpoint : after.loans identifier with
  | none => simp [endpoint] at survives
  | some finalLoan =>
    have below := (valid.2 identifier record live).1
    exact (history.loan_stable valid identifier below finalLoan endpoint).1.symm

/-- All current cells and all their permissions are framed through actual
managed histories. Nothing asserts global memory equality across peer work. -/
theorem Protected.frame {before after : Borrowing.State} {call : Call}
    (held : Protected before call) (valid : Borrowing.WellFormed before)
    (history : Borrowing.History before after) (kept : Retained after call) :
    Protected after call ∧
    AgreesOn after.resources.space before.resources.space call.code call.bytes.length ∧
    AgreesOn after.resources.space before.resources.space call.stack 8 ∧
    (call.values ≠ [] →
      AgreesOn after.resources.space before.resources.space call.base (4 * call.values.length)) := by
  obtain ⟨codeAfter, codeCells⟩ := held.code.frame valid history
    (surviving_loan held.code valid history kept.code)
  obtain ⟨stackAfter, stackCells⟩ := held.stack.frame valid history
    (surviving_loan held.stack valid history kept.stack)
  have inputFrame := fun nonempty => (held.input nonempty).frame valid history
    (surviving_loan (held.input nonempty) valid history (kept.input nonempty))
  exact ⟨⟨codeAfter, stackAfter, fun nonempty => (inputFrame nonempty).1,
    held.code_stack, held.input_code, held.input_stack⟩,
    codeCells, stackCells, fun nonempty => (inputFrame nonempty).2⟩

theorem currentArrayAt_frame {before after : Borrowing.State} {base : Word}
    {values : List (BitVec 32)}
    (cells : AgreesOn after.resources.space before.resources.space base (4 * values.length))
    (current : currentArrayAt before base values) : currentArrayAt after base values := by
  intro index value present
  obtain ⟨inside, _⟩ := List.getElem_of_getElem? present
  apply (loadDWord_congr _ _ _ ?_).trans (current index value present)
  intro offset byte
  have offsetSum : 4 * index + offset < 4 * values.length := by omega
  have pointer : (base + BitVec.ofNat 64 (4 * index)) + BitVec.ofNat 64 offset =
      base + BitVec.ofNat 64 (4 * index + offset) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [pointer]
  exact (toMemory_agrees_at _ _ _ (cells _ offsetSum)).1

/-- Actual current code, complete readWord return slot, and currentArrayAt are
preserved together. Empty input frames without consulting its unused loan ID. -/
theorem Contract.frame {before after : Borrowing.State} {call : Call}
    (contract : Contract before call) (history : Borrowing.History before after)
    (kept : Retained after call) : Contract after call := by
  obtain ⟨held, codeCells, stackCells, inputCells⟩ :=
    contract.held.frame contract.wellFormed history kept
  refine ⟨history.wellFormed contract.wellFormed, held,
    agrees_code _ _ _ _ codeCells contract.code,
    (readWord_congr _ _ _ (agrees_read _ _ _ _ stackCells)).trans contract.stack,
    ?_, contract.bound, contract.returnCanonical, contract.stackBound, contract.postStackCanonical⟩
  by_cases empty : call.values = []
  · rw [empty]
    exact currentArrayAt_nil _ _
  · exact currentArrayAt_frame (inputCells empty) contract.array

/-- The Atomics wrappers enforce their actual reservation/borrowing guards;
their histories project to the same checked loan-preserving resource frame.
This theorem grants no execution of the sequential extension in old TSO. -/
theorem Contract.frame_atomics {before after : Atomics.State} {call : Call}
    (contract : Contract before.shared call) (history : Atomics.History before after)
    (kept : Retained after.shared call) : Contract after.shared call :=
  contract.frame history.borrowing kept

end EDSL.OS.ArrayResources
