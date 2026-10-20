/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex.Preservation
import EDSL.OS.Threads.Framing

namespace EDSL.OS.Mutex
open X86 AddressSpace

theorem ValidMutex.frame {before after : State} {record : Registered}
    (valid : ValidMutex before record) (world : Ownership.WellFormed before.shared.resources)
    (lock : Ownership.PreservesAllocation before.shared.resources after.shared.resources record.config.lockTicket.identifier)
    (data : Ownership.PreservesAllocation before.shared.resources after.shared.resources record.config.dataTicket.identifier)
    (readers : NoReaders after.shared record.config) (frontier : before.nextLease = after.nextLease) :
    ValidMutex after record := by
  refine ⟨valid.lock.frame world lock, valid.data.frame world data, valid.separate, valid.atomic, readers, ?_⟩
  have lockValue := valid.lock.load_frame world lock
  have dataValue := valid.data.load_frame world data
  cases held : record.holder with
  | none =>
    have phase := valid.phase
    rw [held] at phase
    obtain ⟨value, observed, invariant⟩ := phase.2
    exact ⟨lockValue.trans phase.1, value, dataValue.trans observed, invariant⟩
  | some lease =>
    have phase := valid.phase
    rw [held] at phase
    exact ⟨by simpa only [← frontier] using phase.1, lockValue.trans phase.2⟩

theorem mutate_wellFormed (state : State) (operation : Ownership.Mutation) (result : State × Option Ownership.Ticket)
    (valid : WellFormed state) (success : mutate state operation = .ok result) : WellFormed result.1 := by
  obtain ⟨allowed, shared, changed, same⟩ := mutate_ok _ _ _ success
  obtain ⟨_, resources, mutation, sharedEq⟩ := Borrowing.mutate_ok _ _ _ changed
  rw [same]
  refine ⟨Borrowing.mutate_wellFormed _ _ _ valid.1 changed, ?_⟩
  intro record live
  have mutex := valid.2 _ live
  have different := allowed_sound _ _ _ live allowed
  have lock := operation.run_preserves _ _ _ valid.1.1 mutation different.1
  have data := operation.run_preserves _ _ _ valid.1.1 mutation different.2
  have lockFrame : Ownership.PreservesAllocation state.shared.resources shared.1.resources record.config.lockTicket.identifier := by
    rw [sharedEq]
    exact lock
  have dataFrame : Ownership.PreservesAllocation state.shared.resources shared.1.resources record.config.dataTicket.identifier := by
    rw [sharedEq]
    exact data
  have readers : NoReaders shared.1 record.config := by
    rw [sharedEq]
    exact mutex.noReaders
  exact mutex.frame valid.1.1 lockFrame dataFrame readers rfl

theorem readBorrow_wellFormed (state : State) (lender : Nat) (ticket : Ownership.Ticket) (borrower : Nat)
    (region : Region) (result : State × Nat) (valid : WellFormed state)
    (success : readBorrow state lender ticket borrower region = .ok result) : WellFormed result.1 := by
  obtain ⟨gate, shared, borrowed, same⟩ := readBorrow_ok _ _ _ _ _ _ success
  have resources := Threads.readBorrow_resources borrowed
  obtain ⟨_, _, _, _, _, installed⟩ := Borrowing.readBorrow_ok _ _ _ _ _ _ borrowed
  rw [same]
  refine ⟨(Borrowing.readBorrow_wellFormed _ _ _ _ _ _ valid.1 borrowed).1, ?_⟩
  intro record live
  have mutex := valid.2 _ live
  have different := allowed_sound _ _ _ live gate
  have readers : NoReaders shared.1 record.config := by
    rw [installed]
    intro identifier loan atLoan
    by_cases fresh : identifier = state.shared.nextLoan
    · subst identifier
      simp [Borrowing.installLoan] at atLoan
      cases atLoan
      constructor
      · intro equal; exact different.1 (congrArg some equal)
      · intro equal; exact different.2 (congrArg some equal)
    · exact mutex.noReaders _ _ (by simpa [Borrowing.installLoan, fresh] using atLoan)
  apply mutex.frame (after := { state with shared := shared.1 }) valid.1.1 _ _ readers rfl
  all_goals rw [resources]; exact Ownership.PreservesAllocation.refl _ _

theorem finishLoan_wellFormed (state : State) (borrower identifier : Nat) (after : State)
    (valid : WellFormed state) (success : finishLoan state borrower identifier = .ok after) : WellFormed after := by
  obtain ⟨shared, finished, same⟩ := finishLoan_ok _ _ _ _ success
  obtain ⟨_, _, installed⟩ := Borrowing.finishLoan_ok _ _ _ _ finished
  rw [same]
  refine ⟨(Borrowing.finishLoan_wellFormed _ _ _ _ valid.1 finished).1, ?_⟩
  intro record live
  have mutex := valid.2 _ live
  have readers : NoReaders shared record.config := by
    rw [installed]
    intro query loan atLoan
    by_cases removed : query = identifier
    · simp [removed] at atLoan
    · exact mutex.noReaders _ _ (by simpa [removed] using atLoan)
  apply mutex.frame (after := { state with shared := shared }) valid.1.1 _ _ readers rfl
  all_goals rw [installed]; exact Ownership.PreservesAllocation.refl _ _

end EDSL.OS.Mutex
