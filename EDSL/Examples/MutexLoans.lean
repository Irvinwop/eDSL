/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.MutexWorkers
import EDSL.OS.MutexReplay.Loans

namespace EDSL.Examples.MutexWorkers
open X86 OS OS.AddressSpace OS.MutexReplay

theorem spawnMany_loanReady (state : MutexReplay.State) (start : Start) (count : Nat)
    (after : MutexReplay.State) (config : Mutex.Config) (valid : Invariant config state)
    (ready : LoanReady state) (success : spawnMany state start count = .ok after) : LoanReady after := by
  induction count generalizing state with
  | zero => simp [spawnMany] at success; cases success; exact ready
  | succ count induction =>
    cases spawned : spawn state start with
    | error fault => simp [spawnMany, spawned] at success
    | ok next =>
      have tail : spawnMany next start count = .ok after := by simpa [spawnMany, spawned] using success
      exact induction next (spawn_invariant _ _ _ _ valid spawned)
        (spawn_loanReady _ _ _ valid.shared ready spawned) tail

/-- The fixture's loan provenance comes from its actual checked setup and
spawn sequence, for every successfully admitted predicate, word and count. -/
theorem cohort_loanReady (predicate : BitVec 32 → Bool) (old : BitVec 32) (count : Nat)
    (state : MutexReplay.State) (success : cohort predicate old count = .ok state) : LoanReady state := by
  cases prepared : setupIn (seed old) predicate with
  | error fault => simp [cohort, prepared] at success
  | ok pair =>
    have next : spawnMany pair.1 pair.2 count = .ok state := by simpa [cohort, prepared] using success
    obtain ⟨valid, empty⟩ := setupIn_valid _ _ _ prepared
    have ready : LoanReady pair.1 := by
      intro identifier worker live
      rw [empty] at live
      cases live
    exact spawnMany_loanReady _ _ _ _ _ valid ready next

theorem admitted_loanReady (old : BitVec 32) : LoanReady (admitted old) :=
  cohort_loanReady _ _ _ _ (admitted_success old)

end EDSL.Examples.MutexWorkers
