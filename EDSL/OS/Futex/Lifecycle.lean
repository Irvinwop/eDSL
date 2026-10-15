/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Invariant

namespace EDSL.OS.Futex.Lifecycle
open X86

/-- Explicit cohort resources. Borrowers and actors remain logical principals.
Unlisted resources, including unrelated live loans, are retained. -/
structure Plan where
  loans : List (Nat × Nat)
  producers : List (Nat × Nat)
  deriving DecidableEq, Repr

def LoansLive (state : Atomics.State) (references : List (Nat × Nat)) : Prop :=
  ∀ borrower identifier, (borrower, identifier) ∈ references →
    ∃ loan, state.shared.loans identifier = some loan ∧ loan.borrower = borrower

def HandlesLive (state : Atomics.State) (references : List (Nat × Nat)) : Prop :=
  ∀ actor identifier, (actor, identifier) ∈ references →
    ∃ handle, state.handles identifier = some handle ∧ handle.actor = actor

def finishLoans (state : Atomics.State) : List (Nat × Nat) → Except Atomics.Fault Atomics.State
  | [] => .ok state
  | (borrower, identifier) :: rest => do finishLoans (← Atomics.finishLoan state borrower identifier) rest

def closeHandles (state : Atomics.State) : List (Nat × Nat) → Except Atomics.Fault Atomics.State
  | [] => .ok state
  | (actor, identifier) :: rest => do closeHandles (← Atomics.close state actor identifier) rest

theorem history_trans {before middle after : Atomics.State}
    (head : Atomics.History before middle) (tail : Atomics.History middle after) : Atomics.History before after := by
  induction head with
  | refl => exact tail
  | next first _ ih => exact .next first (ih tail)

theorem finishLoans_enabled (state : Atomics.State) (references : List (Nat × Nat))
    (distinct : (references.map Prod.snd).Nodup) (live : LoansLive state references) :
    ∃ after, finishLoans state references = .ok after := by
  induction references generalizing state with
  | nil => exact ⟨state, rfl⟩
  | cons reference rest ih =>
    rcases reference with ⟨borrower, identifier⟩
    obtain ⟨loan, found, owns⟩ := live borrower identifier (by simp)
    let middle : Atomics.State := { state with shared := { state.shared with
      loans := fun query => if query = identifier then none else state.shared.loans query } }
    have first : Atomics.finishLoan state borrower identifier = .ok middle := by
      simp [Atomics.finishLoan, Borrowing.finishLoan, Borrowing.authorize, found, owns, Except.mapError, middle]
    have nodup := List.nodup_cons.mp distinct
    have remaining : LoansLive middle rest := by
      intro other query member
      obtain ⟨current, currentFound, currentOwns⟩ := live other query (by simp [member])
      have different : query ≠ identifier := by
        intro same
        apply nodup.1
        exact List.mem_map.mpr ⟨(other, query), member, same⟩
      exact ⟨current, by simpa [middle, different] using currentFound, currentOwns⟩
    obtain ⟨after, tail⟩ := ih _ nodup.2 remaining
    exact ⟨after, by simp [finishLoans, first, tail]⟩

theorem closeHandles_enabled (state : Atomics.State) (references : List (Nat × Nat))
    (distinct : (references.map Prod.snd).Nodup) (live : HandlesLive state references) :
    ∃ after, closeHandles state references = .ok after := by
  induction references generalizing state with
  | nil => exact ⟨state, rfl⟩
  | cons reference rest ih =>
    rcases reference with ⟨actor, identifier⟩
    obtain ⟨handle, found, owns⟩ := live actor identifier (by simp)
    let middle : Atomics.State := { state with
      handles := fun query => if query = identifier then none else state.handles query }
    have first : Atomics.close state actor identifier = .ok middle := by
      simp [Atomics.close, Atomics.authorize, found, owns, middle]
    have nodup := List.nodup_cons.mp distinct
    have remaining : HandlesLive middle rest := by
      intro other query member
      obtain ⟨current, currentFound, currentOwns⟩ := live other query (by simp [member])
      have different : query ≠ identifier := by
        intro same
        apply nodup.1
        exact List.mem_map.mpr ⟨(other, query), member, same⟩
      exact ⟨current, by simpa [middle, different] using currentFound, currentOwns⟩
    obtain ⟨after, tail⟩ := ih _ nodup.2 remaining
    exact ⟨after, by simp [closeHandles, first, tail]⟩

theorem finishLoans_effect {state after : Atomics.State} {references : List (Nat × Nat)}
    (success : finishLoans state references = .ok after) :
    after.shared.resources = state.shared.resources ∧ after.handles = state.handles ∧
      after.nextHandle = state.nextHandle ∧ after.shared.nextLoan = state.shared.nextLoan ∧
      (∀ query, after.shared.loans query =
        if query ∈ references.map Prod.snd then none else state.shared.loans query) ∧
      Atomics.History state after := by
  induction references generalizing state with
  | nil => simp [finishLoans] at success; subst after; exact ⟨rfl, rfl, rfl, rfl, by simp, .refl⟩
  | cons reference rest ih =>
    rcases reference with ⟨borrower, identifier⟩
    cases first : Atomics.finishLoan state borrower identifier with
    | error fault => simp [finishLoans, first] at success
    | ok middle =>
      have tail : finishLoans middle rest = .ok after := by simpa [finishLoans, first] using success
      obtain ⟨resources, handles, frontier, loans, removed, history⟩ := ih tail
      obtain ⟨shared, finished, same⟩ := Atomics.finishLoan_ok _ _ _ _ first
      obtain ⟨_, _, sharedEq⟩ := Borrowing.finishLoan_ok _ _ _ _ finished
      refine ⟨resources.trans ?_, handles.trans ?_, frontier.trans ?_, loans.trans ?_, ?_, .next (.finishLoan first) history⟩
      · rw [same, sharedEq]
      · rw [same]
      · rw [same]
      · rw [same, sharedEq]
      · intro query
        rw [removed, same, sharedEq]
        by_cases head : query = identifier <;> by_cases member : query ∈ rest.map Prod.snd <;> simp [head, member]

theorem closeHandles_effect {state after : Atomics.State} {references : List (Nat × Nat)}
    (success : closeHandles state references = .ok after) :
    after.shared = state.shared ∧ after.nextHandle = state.nextHandle ∧
      (∀ query, after.handles query =
        if query ∈ references.map Prod.snd then none else state.handles query) ∧
      Atomics.History state after := by
  induction references generalizing state with
  | nil => simp [closeHandles] at success; subst after; exact ⟨rfl, rfl, by simp, .refl⟩
  | cons reference rest ih =>
    rcases reference with ⟨actor, identifier⟩
    cases first : Atomics.close state actor identifier with
    | error fault => simp [closeHandles, first] at success
    | ok middle =>
      have tail : closeHandles middle rest = .ok after := by simpa [closeHandles, first] using success
      obtain ⟨shared, frontier, removed, history⟩ := ih tail
      obtain ⟨_, _, same⟩ := Atomics.close_ok _ _ _ _ first
      refine ⟨shared.trans ?_, frontier.trans ?_, ?_, .next (.close first) history⟩
      · rw [same]
      · rw [same]
      · intro query
        rw [removed, same]
        by_cases head : query = identifier <;> by_cases member : query ∈ rest.map Prod.snd <;> simp [head, member]

/-- Actual returns and empty FIFOs are checked before any cleanup. The finite
scans also check current pending/call records, under their existing frontier
invariants. No cleanup operation occurs on an unsuccessful guard. -/
def ready (state : State) : Bool :=
  state.suspended.machine.workers.all (fun worker => worker.returned && worker.buffer.isEmpty) &&
  (List.range state.suspended.machine.workers.length).all (fun worker => (state.suspended.pending worker).isNone) &&
  (List.range state.suspended.nextCall).all (fun invocation => (state.calls invocation).isNone) && state.queue.isEmpty

inductive Fault where
  | busy | unregistered | resources (fault : Atomics.Fault)
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

def collect (plan : Plan) (state : State) : Except Fault State := do
  if !ready state then throw .busy
  let some registration := state.registration | throw .unregistered
  let loanFree ← (finishLoans state.authority plan.loans).mapError Fault.resources
  let handleFree ← (closeHandles loanFree
    (plan.producers ++ [(registration.actor, registration.keeper)])).mapError Fault.resources
  return { state with authority := handleFree, registration := none }

theorem collect_busy (plan : Plan) (state : State) (busy : ready state = false) :
    collect plan state = .error .busy := by simp [collect, busy]

theorem ready_of_completed (state : State) (finished : Suspend.Finished state.suspended)
    (calls : ∀ invocation, state.calls invocation = none) (empty : state.queue = []) : ready state = true := by
  have workers : state.suspended.machine.workers.all
      (fun worker => worker.returned && worker.buffer.isEmpty) = true := by
    apply List.all_eq_true.mpr
    intro worker member
    simp [(finished.1.1 worker member), (finished.1.2 worker member)]
  have pending : (List.range state.suspended.machine.workers.length).all
      (fun worker => (state.suspended.pending worker).isNone) = true := by simp [finished.2]
  simp [ready, workers, pending, calls, empty]

/-- Under the established invocation invariants, passing the finite guard
means every actual worker returned with an empty FIFO and no actual pending
syscall or service record remains, even at indices outside the guard's scans. -/
theorem ready_completed {config : Config} {state : State} (valid : WellFormed config state)
    (checked : ready state = true) :
    Suspend.Finished state.suspended ∧ (∀ invocation, state.calls invocation = none) ∧ state.queue = [] := by
  simp only [ready, Bool.and_eq_true] at checked
  obtain ⟨⟨⟨workers, _⟩, _⟩, empty⟩ := checked
  have returned : TSO.Returned state.suspended.machine := by
    intro worker member
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp workers worker member)).1
  have quiescent : TSO.Quiescent state.suspended.machine := by
    intro worker member
    simpa using (Bool.and_eq_true_iff.mp (List.all_eq_true.mp workers worker member)).2
  have pending : ∀ worker, state.suspended.pending worker = none := by
    intro worker
    cases found : state.suspended.pending worker with
    | none => rfl
    | some saved =>
      obtain ⟨selected, live, unreturned, _⟩ := (valid.suspended.pending worker saved found).live
      have finished := returned selected (List.mem_of_getElem? live)
      rw [unreturned] at finished
      cases finished
  refine ⟨⟨⟨returned, quiescent⟩, pending⟩, ?_, by simpa using empty⟩
  intro invocation
  cases found : state.calls invocation with
  | none => rfl
  | some call =>
    obtain ⟨saved, actual, _⟩ := valid.bound found
    rw [pending] at actual
    cases actual

/-- Enabled collection follows from current live, distinct cohort records.
There is no successful future cleanup premise. -/
theorem collect_enabled (plan : Plan) (state : State) (registration : Resources.Registration)
    (quiescent : ready state = true) (registered : state.registration = some registration)
    (loanDistinct : (plan.loans.map Prod.snd).Nodup) (loans : LoansLive state.authority plan.loans)
    (handleDistinct : ((plan.producers ++ [(registration.actor, registration.keeper)]).map Prod.snd).Nodup)
    (handles : HandlesLive state.authority (plan.producers ++ [(registration.actor, registration.keeper)])) :
    ∃ after, collect plan state = .ok after := by
  obtain ⟨loanFree, finished⟩ := finishLoans_enabled state.authority plan.loans loanDistinct loans
  have frame := finishLoans_effect finished
  have handlesLive : HandlesLive loanFree (plan.producers ++ [(registration.actor, registration.keeper)]) := by
    simpa [HandlesLive, frame.2.1] using handles
  obtain ⟨handleFree, closed⟩ := closeHandles_enabled loanFree _ handleDistinct handlesLive
  exact ⟨{state with authority := handleFree, registration := none}, by
    simp [collect, quiescent, registered, finished, closed, Except.mapError]⟩

theorem collect_effect {plan : Plan} {state after : State}
    (success : collect plan state = .ok after) :
    ready state = true ∧ ∃ registration,
      state.registration = some registration ∧ after.registration = none ∧
      after.suspended = state.suspended ∧ after.calls = state.calls ∧ after.queue = state.queue ∧
      after.authority.shared.resources = state.authority.shared.resources ∧
      after.authority.shared.nextLoan = state.authority.shared.nextLoan ∧
      after.authority.nextHandle = state.authority.nextHandle ∧
      (∀ query, after.authority.shared.loans query =
        if query ∈ plan.loans.map Prod.snd then none else state.authority.shared.loans query) ∧
      (∀ query, after.authority.handles query =
        if query ∈ (plan.producers ++ [(registration.actor, registration.keeper)]).map Prod.snd
          then none else state.authority.handles query) ∧
      Atomics.History state.authority after.authority := by
  by_cases quiescent : ready state = true
  · cases registered : state.registration with
    | none => simp [collect, quiescent, registered] at success
    | some registration =>
      cases finished : finishLoans state.authority plan.loans with
      | error fault => simp [collect, quiescent, registered, finished, Except.mapError] at success
      | ok loanFree =>
        cases closed : closeHandles loanFree (plan.producers ++ [(registration.actor, registration.keeper)]) with
        | error fault => simp [collect, quiescent, registered, finished, closed, Except.mapError] at success
        | ok handleFree =>
          simp [collect, quiescent, registered, finished, closed, Except.mapError] at success
          subst after
          have loanFrame := finishLoans_effect finished
          have handleFrame := closeHandles_effect closed
          refine ⟨quiescent, registration, rfl, rfl, rfl, rfl, rfl, ?_, ?_, handleFrame.2.1.trans loanFrame.2.2.1, ?_, ?_, ?_⟩
          · exact (congrArg Borrowing.State.resources handleFrame.1).trans loanFrame.1
          · exact (congrArg Borrowing.State.nextLoan handleFrame.1).trans loanFrame.2.2.2.1
          · intro query
            rw [handleFrame.1]
            exact loanFrame.2.2.2.2.1 query
          · intro query
            rw [handleFrame.2.2.1, loanFrame.2.1]
          · exact history_trans loanFrame.2.2.2.2.2 handleFrame.2.2.2
  · simp [collect, quiescent] at success

theorem collect_wellFormed {config : Config} {plan : Plan} {state after : State}
    (valid : WellFormed config state) (success : collect plan state = .ok after) :
    WellFormed config after := by
  obtain ⟨guard, _, _, _, machine, calls, queue, _, _, _, _, _, history⟩ := collect_effect success
  obtain ⟨finished, absent, empty⟩ := ready_completed valid guard
  refine ⟨by rw [machine]; exact valid.suspended, history.wellFormed valid.authority, ?_, ?_, ?_, ?_, ?_⟩
  · intro identifier call found
    rw [calls, absent] at found
    cases found
  · intro worker saved found
    rw [machine, finished.2] at found
    cases found
  · simp [queue, empty]
  · intro identifier
    simp [queue, empty, calls, absent]
  · intro left a right b found
    rw [calls, absent] at found
    cases found

end EDSL.OS.Futex.Lifecycle
