/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordResources64.Bridge
import EDSL.OS.Borrowing.Read64

set_option warningAsError true

namespace EDSL.OS.WordResources64
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS

private theorem qword_byte_permissions {memory : Memory} {target : Word}
    (checked : canStoreQWord memory target = true) (offset : Nat) (bound : offset < 8) :
    canonical (target + BitVec.ofNat 64 offset) = true ∧
      memory.writable (target + BitVec.ofNat 64 offset) = true ∧
      (memory.read (target + BitVec.ofNat 64 offset)).isSome = true := by
  simp only [canStoreQWord, qwordAddressable, qwordWritable, Bool.and_eq_true,
    decide_eq_true_eq] at checked
  rcases checked with ⟨⟨_, ⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩⟩,
    ⟨⟨⟨⟨⟨⟨⟨w0, w1⟩, w2⟩, w3⟩, w4⟩, w5⟩, w6⟩, w7⟩,
    ⟨⟨⟨⟨⟨⟨⟨r0, r1⟩, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩, r7⟩⟩
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
      offset = 4 ∨ offset = 5 ∨ offset = 6 ∨ offset = 7 := by omega
  rcases cases with h | h | h | h | h | h | h | h <;> subst offset <;> simp_all

/-- Complete permissions for a contained four-byte operand follow from the
eight-byte permission check, including canonicality and nonwrapping. -/
theorem canStoreDWord_of_canStoreQWord {memory : Memory} {target address : Word}
    (checked : canStoreQWord memory target = true)
    (span : Borrowing.Subregion (AddressSpace.wordRegion address) (AddressSpace.qwordRegion target)) :
    canStoreDWord memory address = true := by
  have nonwrap : target.toNat + 7 < 2^64 := by
    have addressable := (Bool.and_eq_true_iff.mp checked).1
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp addressable).1
  have lower : target.toNat ≤ address.toNat := span.1
  have upper : address.toNat + 4 ≤ target.toNat + 8 := span.2
  let delta := address.toNat - target.toNat
  have small : delta < 2^64 := by dsimp [delta]; omega
  have total : target.toNat + delta < 2^64 := by dsimp [delta]; omega
  have atBase : target + BitVec.ofNat 64 delta = address := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]
    dsimp [delta]
    omega
  have point (offset : Nat) (bound : offset < 4) :
      canonical (address + BitVec.ofNat 64 offset) = true ∧
        memory.writable (address + BitVec.ofNat 64 offset) = true ∧
        (memory.read (address + BitVec.ofNat 64 offset)).isSome = true := by
    have below : delta + offset < 8 := by dsimp [delta]; omega
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, atBase] using
      qword_byte_permissions checked (delta + offset) below
  obtain ⟨c0, w0, r0⟩ := point 0 (by decide)
  obtain ⟨c1, w1, r1⟩ := point 1 (by decide)
  obtain ⟨c2, w2, r2⟩ := point 2 (by decide)
  obtain ⟨c3, w3, r3⟩ := point 3 (by decide)
  simp only [BitVec.add_zero] at c0 w0 r0
  simp only [canStoreDWord, dwordAddressable, dwordWritable, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨⟨by omega, ⟨⟨⟨c0, c1⟩, c2⟩, c3⟩⟩,
    ⟨⟨⟨w0, w1⟩, w2⟩, w3⟩, ⟨⟨⟨r0, r1⟩, r2⟩, r3⟩⟩

theorem loadDWord_of_canStoreQWord {memory : Memory} {target address : Word}
    (checked : canStoreQWord memory target = true)
    (span : Borrowing.Subregion (AddressSpace.wordRegion address) (AddressSpace.qwordRegion target)) :
    ∃ value, loadDWord memory address = .ok value :=
  Atomics.load_exists_of_canStore _ _ (canStoreDWord_of_canStoreQWord checked span)

/-- The same owner, ticket and allocation authorize a contained subword.
This creates neither a second allocation nor a target loan. -/
theorem WordValid.subword {shared : Shared} {owner : Nat} {ticket : Ownership.Ticket}
    {target address : Word} (word : WordValid shared owner ticket target)
    (span : Borrowing.Subregion (AddressSpace.wordRegion address) (AddressSpace.qwordRegion target)) :
    Mutex.WordValid shared owner ticket address := by
  obtain ⟨allocation, found, owns, epoch, fits, writable⟩ := word
  have contains : allocation.region.base.toNat ≤ target.toNat ∧
      target.toNat + 8 ≤ allocation.region.base.toNat + allocation.region.length := of_decide_eq_true fits
  have lower := span.1
  have upper := span.2
  change target.toNat ≤ address.toNat at lower
  change address.toNat + 4 ≤ target.toNat + 8 at upper
  refine ⟨allocation, found, owns, epoch, ?_, canStoreDWord_of_canStoreQWord writable span⟩
  apply decide_eq_true
  constructor <;> omega

/-- A narrow checked mutation retains the exact wide frame by span inclusion;
the history records its actual `.store` operation, with no width conversion. -/
theorem Frame.store32 {shared evolved : Shared} {owner : Nat} {ticket : Ownership.Ticket}
    {target address : Word} {value : BitVec 32}
    (span : Borrowing.Subregion (AddressSpace.wordRegion address) (AddressSpace.qwordRegion target))
    (success : Borrowing.mutate shared (.store owner ticket address value) = .ok (evolved, none)) :
    Frame target shared evolved := by
  have effect := Mutex.store_effect success
  exact ⟨.next (.mutate success) .refl, effect.allocations, effect.frontier,
    effect.loans, effect.nextLoan, effect.permissions,
    fun query outside => effect.outside query
      (fun inside => outside (Borrowing.subregion_inside span inside))⟩

/-- Checked frame transport preserves present resources and every loan's exact
contents even when several ordinary store widths appear in the history. -/
theorem Contract.frame {call : Call} {shared evolved : Shared}
    (contract : Contract call shared) (frame : Frame call.targetPointer shared evolved) :
    Contract call evolved := by
  obtain ⟨codeLoan, codeCells⟩ := contract.codeLoan.frame contract.wellFormed frame.history
    (congrFun frame.loans call.codeLoan)
  obtain ⟨stackLoan, stackCells⟩ := contract.stackLoan.frame contract.wellFormed frame.history
    (congrFun frame.loans call.stackLoan)
  exact ⟨frame.history.wellFormed contract.wellFormed, codeLoan, stackLoan,
    AddressSpace.agrees_code _ _ _ _ codeCells contract.code,
    (readWord_congr _ _ _ (AddressSpace.agrees_read _ _ _ _ stackCells)).trans contract.stack,
    contract.word.permissions frame.allocations frame.permissions,
    fun identifier loan live => contract.unborrowed identifier loan (by rwa [← frame.loans]),
    contract.codeDisjoint, contract.stackDisjoint, contract.returnCanonical,
    contract.stackBound, contract.postStackCanonical⟩

theorem current_store32_enabled {call : Call} {shared : Shared} {before : State}
    {address : Word} (current : Current call shared before)
    (span : Borrowing.Subregion (AddressSpace.wordRegion address) (AddressSpace.qwordRegion call.targetPointer))
    (value : BitVec 32) :
    ∃ evolved, Borrowing.mutate shared
      (.store (Threads.principal call.worker) call.ticket address value) = .ok (evolved, none) :=
  Mutex.store_admitted _ _ _ _ _ (current.contract.word.subword span) current.contract.unborrowed

/-- Present wide ownership and an actual decoded narrow intent derive the
successful checked mutation, machine step, current wide authority and frame. -/
theorem current_store32_step {call : Call} {shared : Shared} {before : State}
    {instruction : SeqInstruction} {address : Word} {value : BitVec 32}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok instruction)
    (intent : instruction.storeIntent before = some (address, value))
    (span : Borrowing.Subregion (AddressSpace.wordRegion address) (AddressSpace.qwordRegion call.targetPointer))
    (af : Bool) :
    ∃ evolved,
      Borrowing.mutate shared (.store (Threads.principal call.worker) call.ticket address value) =
        .ok (evolved, none) ∧
      step af before = .ok ⟨.next (storeAfterLength before evolved instruction.length), []⟩ ∧
      Current call evolved (storeAfterLength before evolved instruction.length) ∧
      Mutex.StoreEffect shared evolved address value ∧
      Frame call.targetPointer shared evolved ∧
      (∀ identifier loan, shared.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = shared.resources.space.cells query) := by
  obtain ⟨evolved, stored⟩ := current_store32_enabled current span value
  obtain ⟨actual, effect⟩ := WordResources.actual_store_bridge current.coupled decoded intent stored af
  have frame := Frame.store32 span stored
  exact ⟨evolved, stored, actual, ⟨current.contract.frame frame, rfl⟩,
    effect, frame, fun _ _ live => frame.loan_contents current.contract.wellFormed live⟩

end EDSL.OS.WordResources64
