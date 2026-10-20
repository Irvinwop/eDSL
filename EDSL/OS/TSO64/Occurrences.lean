/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Invariant

namespace EDSL.OS.TSO64
open X86

def Worker.storeCursor (worker : Worker) : Queue.Cursor := ⟨worker.pending, worker.nextStore⟩

/-- Numerical integrity of the actual worker FIFOs. Current authority remains
the separate WellFormed invariant. This predicate alone supplies no past events
for a nonempty initial queue and no global reads-from relation. -/
def Sequenced (state : State) : Prop :=
  ∀ worker ∈ state.workers, worker.storeCursor.Ordered

private theorem install_sequenced {state : State} {tid : Nat} {world : World} {worker : Worker}
    (sequenced : Sequenced state) (ordered : worker.storeCursor.Ordered) :
    Sequenced (install state tid world worker) := by
  intro other member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact sequenced other old
  · exact ordered

/-- Actual successful execution preserves ordered, nonduplicate pending IDs.
The proof follows real admission/finish/drain effects rather than testing the
desired successor invariant in the executable scheduler. -/
theorem step_sequenced {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} (sequenced : Sequenced state)
    (success : step state action profile = .ok result) : Sequenced result.1 := by
  cases action with
  | issue tid af =>
      obtain ⟨worker, live, _, _, _, instruction, _, effect⟩ := issue_effect success
      have ordered := sequenced worker (List.mem_of_getElem? live)
      cases instruction with
      | ordinary instruction =>
          cases effect with
          | intro supported bounds decoded reads queue actual finish =>
              have nextOrdered := queue.ordered ordered
              cases finish <;> exact install_sequenced sequenced nextOrdered
      | locked instruction =>
          cases effect with
          | blocked => exact sequenced
          | rmw => exact install_sequenced sequenced ordered
  | drain tid =>
      obtain ⟨worker, head, tail, output, live, pending, _, _, same⟩ := drain_effect success
      have ordered := sequenced worker (List.mem_of_getElem? live)
      have remaining := worker.storeCursor.dropHead_ordered ordered
      rw [same]
      apply install_sequenced sequenced
      simpa only [Worker.storeCursor, Queue.Cursor.dropHead, pending, List.tail_cons] using remaining

theorem schedule_sequenced {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} (sequenced : Sequenced state)
    (success : schedule state actions profile = .ok result) : Sequenced result.1 := by
  induction actions generalizing state result with
  | nil =>
      have same : (state, []) = result := Except.ok.inj success
      subst result
      exact sequenced
  | cons action rest ih =>
      obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok success
      rw [same]
      exact ih (result := tail) (step_sequenced sequenced first) following

theorem makeWorker_sequenced {world : World} {actor : Nat} {entry : Context} {codeId callerId : Nat}
    {grants : List Ownership.Ticket} {atomics : List Atomics64.HandleId64} {worker : Worker}
    (success : makeWorker world actor entry codeId callerId grants atomics = .ok worker) :
    worker.storeCursor.Ordered := by
  have empty := (makeWorker_valid success).2.2.1
  have counter := makeWorker_nextStore success
  change Queue.Cursor.Ordered ⟨worker.pending, worker.nextStore⟩
  rw [empty, counter]
  exact Queue.Cursor.empty_ordered

theorem attach_sequenced {state : State} {actor : Nat} {entry : Context} {codeId callerId : Nat}
    {grants : List Ownership.Ticket} {atomics : List Atomics64.HandleId64} {after : State}
    (sequenced : Sequenced state)
    (success : attach state actor entry codeId callerId grants atomics = .ok after) : Sequenced after := by
  cases made : makeWorker state.world actor entry codeId callerId grants atomics with
  | error fault => simp [attach, made] at success
  | ok worker =>
      simp only [attach, made, ok_bind, pure_ok, Except.ok.injEq] at success
      subst after
      intro other member
      rcases List.mem_append.mp member with old | fresh
      · exact sequenced other old
      · have same := List.mem_singleton.mp fresh
        subst other
        exact makeWorker_sequenced made

theorem sequenced_empty (world : World) : Sequenced ⟨world, []⟩ := by
  intro worker member
  cases member

/-- Shared authority and queue numbering remain distinct, composable invariants.
Complete issue/publication/read history is a separate contract. -/
def SharedValid (state : State) : Prop := WellFormed state .sharedCell ∧ Sequenced state

theorem step_sharedValid {state : State} {action : Action} {result : State × Observation}
    (valid : SharedValid state) (success : step state action .sharedCell = .ok result) :
    SharedValid result.1 := ⟨step_wellFormed valid.1 success, step_sequenced valid.2 success⟩

theorem schedule_sharedValid {state : State} {actions : List Action}
    {result : State × List Observation} (valid : SharedValid state)
    (success : schedule state actions .sharedCell = .ok result) : SharedValid result.1 :=
  ⟨schedule_wellFormed valid.1 success, schedule_sequenced valid.2 success⟩

end EDSL.OS.TSO64
