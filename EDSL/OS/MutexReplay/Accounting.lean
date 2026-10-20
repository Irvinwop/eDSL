/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Tracking

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

def stores (worker : Worker) : Nat :=
  if worker.phase = .storingFirst ∨ worker.phase = .storingSecond then 1 else 0

theorem action_store (worker : Worker) (lease : Mutex.Lease)
    (selected : action worker = .ok (.store lease)) :
    (worker.phase = .storingFirst ∨ worker.phase = .storingSecond) ∧ worker.guard = some lease := by
  cases phase : worker.phase <;> cases guard : worker.guard <;> simp [action, phase, guard] at selected ⊢
  all_goals cases selected; rfl

theorem advance_credit (state : State) (identifier : Nat) (worker : Worker) (result : Result)
    (success : advance state identifier worker = .ok result) :
    credit (evolved worker result) = credit worker + stores worker := by
  obtain ⟨_, operation, selected, _, _⟩ := advance_ok _ _ _ _ success
  cases phase : worker.phase <;> simp [action, phase] at selected
  all_goals first
    | rfl
    | (by_cases target : result.context.rip = worker.entry.rip <;>
      simp [credit, evolved, nextPhase, stores, phase, target])

theorem action_nonstore (worker : Worker) (operation : Action)
    (selected : action worker = .ok operation) (nonstore : ∀ lease, operation ≠ .store lease) : stores worker = 0 := by
  cases phase : worker.phase <;> cases guard : worker.guard <;> simp [action, phase, guard] at selected
  all_goals first
    | (solve | simp [stores, phase])
    | (exact False.elim (nonstore _ selected.symm))

theorem credit_sum_set (workers : List Worker) (identifier : Nat) (before after : Worker)
    (live : workers[identifier]? = some before) :
    ((workers.set identifier after).map credit).sum + credit before =
      (workers.map credit).sum + credit after := by
  induction workers generalizing identifier with
  | nil => simp at live
  | cons first rest induction =>
    cases identifier with
    | zero => simp at live; cases live; simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    | succ index =>
      have tail : rest[index]? = some before := by simpa using live
      have result := induction index tail
      simp only [List.set, List.map_cons, List.sum_cons]
      omega

theorem dispatch_credits (state : State) (identifier : Nat) (worker : Worker)
    (result : State × Option AtomicEvent) (live : state.workers[identifier]? = some worker)
    (success : dispatch state identifier = .ok result) :
    credits result.1 = credits state + stores worker := by
  obtain ⟨actual, output, found, advanced, same⟩ := dispatch_ok _ _ _ success
  have equal := Option.some.inj (found.symm.trans live)
  subst actual
  have sum := credit_sum_set state.workers identifier worker (evolved worker output) live
  have count := advance_credit _ _ _ _ advanced
  rw [same]
  dsimp only [credits]
  omega

theorem completed_credits (state : State) (done : completed state = true) : credits state = 2 * state.workers.length := by
  have each : ∀ worker ∈ state.workers, credit worker = 2 := by
    intro worker member
    have phase := (of_decide_eq_true (List.all_eq_true.mp done worker member)).1
    simp [credit, phase]
  rw [credits, List.map_eq_replicate_iff.mpr each]
  generalize state.workers.length = count
  induction count with
  | zero => rfl
  | succ count induction => simp [List.replicate_succ, induction]; omega

theorem entry_credits (state : State) (entry : ∀ worker ∈ state.workers, worker.phase = .entry) : credits state = 0 := by
  have each : ∀ worker ∈ state.workers, credit worker = 0 := by
    intro worker member
    simp [credit, entry worker member]
  rw [credits, List.map_eq_replicate_iff.mpr each]
  generalize state.workers.length = count
  induction count with
  | zero => rfl
  | succ count induction => simp [List.replicate_succ, induction]

end EDSL.OS.MutexReplay
