/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.StoreHistory

/-!
Forward conservation of an exact FIFO entry through the existing scheduler.
A successful action retains the entry at its original scheduler thread or
observes that exact entry as the published FIFO head. These results neither
identify entries by equal values nor assert uniqueness of issue/publication.
Initial queues and successful runs need no additional provenance assumption.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.StoreHistory
open X86

private theorem flow_queued_install {state : State} {tid : Nat} {world : World}
    {prior replacement : Worker} {entry : Pending}
    (live : state.workers[tid]? = some prior) (member : entry ∈ replacement.pending) :
    Queued (install state tid world replacement) tid entry := by
  exact ⟨replacement, List.getElem?_set_self (List.getElem_of_getElem? live).1, member⟩

private theorem flow_finish_queued {state : State} {tid : Nat} {worker : Worker}
    {pending : List Pending} {observation : Sequential.Observation}
    {result : State × Observation} {nextStore : Nat} {entry : Pending}
    (live : state.workers[tid]? = some worker)
    (finish : FinishEffect state tid worker pending observation result nextStore)
    (member : entry ∈ pending) : Queued result.1 tid entry := by
  cases finish <;> exact flow_queued_install live member

/-- A real issue commits its exact admitted entry to the issuing FIFO, including
the original descriptor, width, word and managed occurrence when present. -/
theorem Issued.queued {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {tid : Nat} {entry : Pending}
    (issued : Issued state action result profile tid entry) : Queued result.1 tid entry := by
  cases issued with
  | ordinary _issuing _success live _fetched _effect _intent _admission committed =>
    exact flow_finish_queued live committed (List.mem_append.mpr (.inr List.mem_cons_self))

/-- An exact pending entry cannot disappear from a successful step: it remains
at the original thread or is the actual head reported by that step's drain. -/
theorem step_pending_retained_or_drained {state : State} {action : Action}
    {result : State × Observation} {profile : Profile} {tid : Nat} {entry : Pending}
    (success : step state action profile = .ok result) (queued : Queued state tid entry) :
    Queued result.1 tid entry ∨ result.2 = .drained tid entry := by
  cases action with
  | issue issuer af =>
    by_cases same : tid = issuer
    · subst tid
      obtain ⟨worker, live, _running, _code, _caller, instruction, _fetched, effect⟩ :=
        issue_effect (profile := profile) success
      obtain ⟨prior, priorLive, member⟩ := queued
      have equal : prior = worker := Option.some.inj (priorLive.symm.trans live)
      subst prior
      cases instruction with
      | ordinary instruction =>
        cases effect with
        | intro _supported _bounds _decoded _reads queue _executed finish =>
          cases queue with
          | unchanged _intent => exact .inl (flow_finish_queued live finish member)
          | enqueued _intent _admission =>
            exact .inl (flow_finish_queued live finish (List.mem_append.mpr (.inl member)))
      | locked instruction =>
        cases effect with
        | blocked => exact .inl ⟨worker, live, member⟩
        | rmw => exact .inl (flow_queued_install live member)
    · obtain ⟨worker, live, member⟩ := queued
      have unchanged := step_peer (profile := profile) success same
      exact .inl ⟨worker, unchanged.trans live, member⟩
  | drain issuer =>
    by_cases same : tid = issuer
    · subst tid
      obtain ⟨worker, head, tail, output, live, fifo, _gate, _changed, resultEq⟩ :=
        drain_effect (profile := profile) success
      obtain ⟨prior, priorLive, member⟩ := queued
      have equal : prior = worker := Option.some.inj (priorLive.symm.trans live)
      subst prior
      rw [fifo] at member
      rcases List.mem_cons.mp member with published | remaining
      · exact .inr (by rw [resultEq, published])
      · exact .inl (by rw [resultEq]; exact flow_queued_install live remaining)
    · obtain ⟨worker, live, member⟩ := queued
      have unchanged := step_peer (profile := profile) success same
      exact .inl ⟨worker, unchanged.trans live, member⟩

/-- Successful scheduling conserves an initial exact entry as a final pending
entry or as an actual publication observation at its original thread. -/
theorem schedule_pending_retained_or_drained {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid : Nat} {entry : Pending}
    (success : schedule state actions profile = .ok result) (queued : Queued state tid entry) :
    Queued result.1 tid entry ∨ .drained tid entry ∈ result.2 := by
  induction actions generalizing state result with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    exact .inl queued
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    rcases step_pending_retained_or_drained stepped queued with retained | drained
    · rcases ih following retained with pending | published
      · exact .inl (by simpa only [same] using pending)
      · exact .inr (by rw [same]; exact List.mem_cons_of_mem _ published)
    · exact .inr (by rw [same, drained]; exact List.mem_cons_self)

/-- Any real issued entry is either still pending after that same run or has
an actual drain observation in its observation stream. No uniqueness is claimed. -/
theorem IssuedIn.pending_or_published {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid : Nat} {entry : Pending}
    (history : IssuedIn profile tid entry state actions result) :
    Queued result.1 tid entry ∨ .drained tid entry ∈ result.2 := by
  induction history with
  | head _stepped following issued =>
    rcases schedule_pending_retained_or_drained following issued.queued with pending | published
    · exact .inl pending
    · exact .inr (List.mem_cons_of_mem _ published)
  | later _stepped _following _issued ih =>
    rcases ih with pending | published
    · exact .inl pending
    · exact .inr (List.mem_cons_of_mem _ published)

/-- At an empty final FIFO boundary, an actual issued entry must have been
published during the same successful schedule. Return alone is not this premise. -/
theorem IssuedIn.published_of_quiescent {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid : Nat} {entry : Pending}
    (history : IssuedIn profile tid entry state actions result) (empty : Quiescent result.1) :
    .drained tid entry ∈ result.2 := by
  rcases history.pending_or_published with pending | published
  · obtain ⟨worker, live, member⟩ := pending
    have none := empty worker (List.mem_of_getElem? live)
    rw [none] at member
    cases member
  · exact published

end EDSL.OS.TSO64.StoreHistory
