/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.StoreHistory

set_option autoImplicit false

namespace EDSL.OS.TSO64.StoreHistory
open X86

private theorem install_worker_present {state : State} {tid thread : Nat} {world : World}
    {prior replacement : Worker} (priorLive : state.workers[thread]? = some prior) :
    ∃ current, (install state tid world replacement).workers[thread]? = some current := by
  by_cases same : thread = tid
  · subst thread
    exact ⟨replacement, List.getElem?_set_self (List.getElem_of_getElem? priorLive).1⟩
  · exact ⟨prior, (install_peer same).trans priorLive⟩

private theorem install_nextStore {state : State} {tid : Nat} {world : World}
    {prior replacement current : Worker}
    (priorLive : state.workers[tid]? = some prior)
    (currentLive : (install state tid world replacement).workers[tid]? = some current) :
    current.nextStore = replacement.nextStore := by
  have installed : (install state tid world replacement).workers[tid]? = some replacement :=
    List.getElem?_set_self (List.getElem_of_getElem? priorLive).1
  exact congrArg Worker.nextStore (Option.some.inj (currentLive.symm.trans installed))

private theorem install_nextStore_le {state : State} {tid thread : Nat} {world : World}
    {subject replacement prior current : Worker}
    (subjectLive : state.workers[tid]? = some subject)
    (priorLive : state.workers[thread]? = some prior)
    (currentLive : (install state tid world replacement).workers[thread]? = some current)
    (growth : subject.nextStore ≤ replacement.nextStore) :
    prior.nextStore ≤ current.nextStore := by
  by_cases same : thread = tid
  · subst thread
    have priorEq : prior = subject := Option.some.inj (priorLive.symm.trans subjectLive)
    rw [priorEq, install_nextStore subjectLive currentLive]
    exact growth
  · rw [install_peer same] at currentLive
    have currentEq : current = prior := Option.some.inj (currentLive.symm.trans priorLive)
    simpa only [currentEq] using Nat.le_refl prior.nextStore

private theorem finish_nextStore {state : State} {tid : Nat} {worker current : Worker}
    {pending : List Pending} {observation : Sequential.Observation}
    {result : State × Observation} {nextStore : Nat}
    (live : state.workers[tid]? = some worker)
    (finish : FinishEffect state tid worker pending observation result nextStore)
    (currentLive : result.1.workers[tid]? = some current) :
    current.nextStore = nextStore := by
  cases finish <;> exact install_nextStore live currentLive

/-- A successful scheduler action retains every existing worker slot. This
also covers blocked issues and returned workers whose queues can still drain;
there is no well-formedness or empty-initial-queue premise. -/
theorem step_worker_present {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} (success : step state action profile = .ok result)
    {thread : Nat} {prior : Worker} (priorLive : state.workers[thread]? = some prior) :
    ∃ current, result.1.workers[thread]? = some current := by
  cases step_origin (profile := profile) success with
  | ordinary live running code caller fetched effect =>
      cases effect with
      | intro supported bounds decoded reads queue executed finish =>
          cases finish <;> exact install_worker_present priorLive
  | blocked => exact ⟨prior, priorLive⟩
  | rmw live running code caller fetched bounds empty grant effect =>
      exact install_worker_present priorLive
  | drained live fifo gate changed effect => exact install_worker_present priorLive

/-- Every successful action leaves each worker's store counter unchanged or
increases it. This follows actual queue and finish effects: blocked issues,
locked RMWs and drains preserve it, while an ordinary enqueue advances it. No
numerical integrity invariant or counter-bound oracle is assumed. -/
theorem step_nextStore_le {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} (success : step state action profile = .ok result)
    {thread : Nat} {prior current : Worker}
    (priorLive : state.workers[thread]? = some prior)
    (currentLive : result.1.workers[thread]? = some current) :
    prior.nextStore ≤ current.nextStore := by
  cases step_origin (profile := profile) success with
  | ordinary live running code caller fetched effect =>
      cases effect with
      | intro supported bounds decoded reads queue executed finish =>
          cases queue with
          | unchanged intent =>
              cases finish <;>
                exact install_nextStore_le live priorLive currentLive (Nat.le_refl _)
          | enqueued intent admission =>
              cases finish <;>
                exact install_nextStore_le live priorLive currentLive (Nat.le_succ _)
  | blocked =>
      have currentEq : current = prior := Option.some.inj (currentLive.symm.trans priorLive)
      simpa only [currentEq] using Nat.le_refl prior.nextStore
  | rmw live running code caller fetched bounds empty grant effect =>
      exact install_nextStore_le live priorLive currentLive (Nat.le_refl _)
  | drained live fifo gate changed effect =>
      exact install_nextStore_le live priorLive currentLive (Nat.le_refl _)

/-- An actual successful ordinary store issue advances its own worker's
counter by exactly one. The issue witness already retains the successful step,
actual admission and committed finish; endpoint workers are identified by
their real scheduler slots rather than by matching counter values. -/
theorem Issued.nextStore_succ {state : State} {action : Action}
    {result : State × Observation} {profile : Profile} {tid : Nat} {entry : Pending}
    (issued : Issued state action result profile tid entry)
    {prior current : Worker} (priorLive : state.workers[tid]? = some prior)
    (currentLive : result.1.workers[tid]? = some current) :
    current.nextStore = prior.nextStore + 1 := by
  cases issued with
  | ordinary issuing success live fetched effect intent admission committed =>
      have priorEq := Option.some.inj (priorLive.symm.trans live)
      rw [priorEq]
      exact finish_nextStore live committed currentLive

/-- A finite successful schedule preserves every existing worker slot. No
future-success, fairness or returned-state assumption is needed. -/
theorem schedule_worker_present {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    (success : schedule state actions profile = .ok result)
    {thread : Nat} {prior : Worker} (priorLive : state.workers[thread]? = some prior) :
    ∃ current, result.1.workers[thread]? = some current := by
  induction actions generalizing state result prior with
  | nil =>
      have same : (state, []) = result := Except.ok.inj success
      subst result
      exact ⟨prior, priorLive⟩
  | cons action rest ih =>
      obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok (profile := profile) success
      obtain ⟨middle, middleLive⟩ := step_worker_present first priorLive
      obtain ⟨current, currentLive⟩ := ih following middleLive
      rw [same]
      exact ⟨current, currentLive⟩

/-- A worker's issue counter never decreases along an actual successful
schedule. The intermediate worker slots and inequalities are derived from
each concrete scheduler step, without a supplied history invariant. -/
theorem schedule_nextStore_le {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    (success : schedule state actions profile = .ok result)
    {thread : Nat} {prior current : Worker}
    (priorLive : state.workers[thread]? = some prior)
    (currentLive : result.1.workers[thread]? = some current) :
    prior.nextStore ≤ current.nextStore := by
  induction actions generalizing state result prior with
  | nil =>
      have same : (state, []) = result := Except.ok.inj success
      subst result
      have currentEq : current = prior := Option.some.inj (currentLive.symm.trans priorLive)
      simpa only [currentEq] using Nat.le_refl prior.nextStore
  | cons action rest ih =>
      obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok (profile := profile) success
      obtain ⟨middle, middleLive⟩ := step_worker_present first priorLive
      have tailLive : tail.1.workers[thread]? = some current := by
        simpa only [same] using currentLive
      exact Nat.le_trans (step_nextStore_le first priorLive middleLive)
        (ih following middleLive tailLive)

end EDSL.OS.TSO64.StoreHistory
