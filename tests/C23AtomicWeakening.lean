/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Weakening
import tests.C23AtomicCheck
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.C23AtomicWeakening
open Concurrency.C23Atomic
open Concurrency.C23Atomic.Check

/-- A foreign RMW leaves the stored bits unchanged. Sparse ranks and explicit
RF distinguish the release, RMW and final reader despite equal values. -/
def sparse (write : WriteOrder) (rmw : RMWOrder) (read : ReadOrder) : Table Nat Nat where
  events := [⟨none, 0, .initialize 0⟩, ⟨some 11, 0, .store write 7⟩,
    ⟨some 12, 0, .rmw rmw 7 7⟩, ⟨some 13, 0, .load read 7⟩]
  sources := C23AtomicCheck.sparseRMW.sources
  ranks := C23AtomicCheck.sparseRMW.ranks

theorem maximal_sparse_graph_is_legal :
    Legal (sparse .release .acqRel .acquire).toCandidate :=
  certify_sound _ (by decide)

/-- The relation checks every event, including absent indices, while requiring
the exact original RF and rank functions rather than recomputing them by value. -/
theorem maximal_sparse_labels_weaken (write : WriteOrder) (rmw : RMWOrder) (read : ReadOrder) :
    Candidate.Weakens (sparse .release .acqRel .acquire).toCandidate
      (sparse write rmw read).toCandidate := by
  refine ⟨?_, rfl, rfl⟩
  intro index
  match index with
  | 0 => exact .some ⟨rfl, rfl, .initial 0⟩
  | 1 => exact .some ⟨rfl, rfl, .store (fun _ => rfl)⟩
  | 2 => exact .some ⟨rfl, rfl, .rmw (fun _ => rfl) (fun _ => rfl)⟩
  | 3 => exact .some ⟨rfl, rfl, .load (fun _ => rfl)⟩
  | _ + 4 => exact .none

/-- One maximal-order proof admits every typed relabeling of this graph. The
RMW may lose acquire, release, or both without losing its writer identity. -/
theorem sparse_legal_after_weakening (write : WriteOrder) (rmw : RMWOrder) (read : ReadOrder) :
    Legal (sparse write rmw read).toCandidate :=
  maximal_sparse_graph_is_legal.weaken (maximal_sparse_labels_weaken write rmw read)

theorem either_rmw_flag_can_be_removed_independently :
    Legal (sparse .relaxed .acquire .relaxed).toCandidate ∧
    Legal (sparse .relaxed .release .relaxed).toCandidate ∧
    Legal (sparse .relaxed .relaxed .relaxed).toCandidate :=
  ⟨sparse_legal_after_weakening _ _ _, sparse_legal_after_weakening _ _ _,
    sparse_legal_after_weakening _ _ _⟩

/-- Relabeling cannot turn an equal-valued RMW read into a read from the earlier
plain store. The modified RF graph may have matching object/value data, but it
is a different execution and must fail the weakening relation. -/
def changedRF : Table Nat Nat :=
  { sparse .relaxed .relaxed .relaxed with sources := [none, none, some 1, some 1] }

theorem equal_value_rf_identity_cannot_change_during_weakening :
    ¬ Candidate.Weakens (sparse .release .acqRel .acquire).toCandidate
      changedRF.toCandidate := by
  intro labels
  have same := congrFun labels.readsFrom_eq 3
  change some (2 : Nat) = some 1 at same
  cases same

/-- Changing a sparse modification rank is also a different execution, even
when it keeps every pair of modifications in the same relative order. -/
def changedRank : Table Nat Nat :=
  { sparse .relaxed .relaxed .relaxed with ranks := [0, 7, 20, 0] }

theorem weakening_preserves_sparse_ranks_exactly :
    ¬ Candidate.Weakens (sparse .release .acqRel .acquire).toCandidate
      changedRank.toCandidate := by
  intro labels
  have same := congrFun labels.rank_eq 2
  change (19 : Nat) = 20 at same
  cases same

theorem a_relaxed_store_cannot_gain_release :
    ¬ Access.Weakens (.store .relaxed (7 : Nat)) (.store .release 7) := by
  intro labels
  cases labels with
  | store release =>
      have impossible := release rfl
      cases impossible

theorem a_relaxed_load_cannot_gain_acquire :
    ¬ Access.Weakens (.load .relaxed (7 : Nat)) (.load .acquire 7) := by
  intro labels
  cases labels with
  | load acquire =>
      have impossible := acquire rfl
      cases impossible

theorem one_rmw_flag_cannot_be_exchanged_for_the_other :
    (¬ Access.Weakens (.rmw .acquire (7 : Nat) 7) (.rmw .release 7 7)) ∧
    (¬ Access.Weakens (.rmw .release (7 : Nat) 7) (.rmw .acquire 7 7)) := by
  constructor
  · intro labels
    cases labels with
    | rmw _ release =>
        have impossible := release rfl
        cases impossible
  · intro labels
    cases labels with
    | rmw acquire _ =>
        have impossible := acquire rfl
        cases impossible

theorem weaker_candidate_cannot_be_strengthened_by_the_relation :
    ¬ Candidate.Weakens (sparse .relaxed .relaxed .relaxed).toCandidate
      (sparse .release .acqRel .acquire).toCandidate := by
  intro labels
  obtain ⟨event, live, related⟩ := labels.event_of_strong (index := 1) rfl
  have same : event = ⟨some 11, 0, .store .release 7⟩ := Option.some.inj live.symm
  subst event
  exact a_relaxed_store_cannot_gain_release related.access

/-- Classic stale message passing with only the flag store/load labels changed
to relaxed. Payload operations, threads, indices, RF and ranks are unchanged. -/
def relaxedStale : Table Nat Nat where
  events := [⟨none, 0, .initialize 0⟩, ⟨none, 1, .initialize 0⟩,
    ⟨some 11, 0, .store .relaxed 42⟩, ⟨some 11, 1, .store .relaxed 1⟩,
    ⟨some 12, 1, .load .relaxed 1⟩, ⟨some 12, 0, .load .relaxed 0⟩]
  sources := C23AtomicCheck.stalePayload.sources
  ranks := C23AtomicCheck.stalePayload.ranks

theorem stale_message_passing_is_legal_when_relaxed : Legal relaxedStale.toCandidate :=
  certify_sound _ (by decide)

theorem stale_graph_changes_only_memory_order_flags :
    Candidate.Weakens C23MessagePassing.stale relaxedStale.toCandidate := by
  refine ⟨?_, ?_, ?_⟩
  · intro index
    match index with
    | 0 => exact .some (Event.Weakens.refl _)
    | 1 => exact .some (Event.Weakens.refl _)
    | 2 => exact .some (Event.Weakens.refl _)
    | 3 => exact .some ⟨rfl, rfl, .store (fun _ => rfl)⟩
    | 4 => exact .some ⟨rfl, rfl, .load (fun _ => rfl)⟩
    | 5 => exact .some (Event.Weakens.refl _)
    | _ + 6 => exact .none
  · funext index
    match index with
    | 0 | 1 | 2 | 3 | 4 | 5 => rfl
    | _ + 6 => rfl
  · funext index
    match index with
    | 0 | 1 | 2 | 3 | 4 | 5 => rfl
    | _ + 6 => rfl

/-- Weakening is deliberately one-way. Strengthening this legal relaxed graph
creates a release/acquire path which forbids the observed old payload. The
negative result is the independent semantic message-passing theorem. -/
theorem strengthening_a_legal_graph_can_destroy_legality :
    Legal relaxedStale.toCandidate ∧ ¬ Legal C23MessagePassing.stale :=
  ⟨stale_message_passing_is_legal_when_relaxed,
    C23MessagePassing.qualifying_acquire_rejects_stale_payload⟩

end EDSL.Tests.C23AtomicWeakening

#print axioms EDSL.Concurrency.C23Atomic.Legal.weaken
#print axioms EDSL.Tests.C23AtomicWeakening.sparse_legal_after_weakening
#print axioms EDSL.Tests.C23AtomicWeakening.stale_message_passing_is_legal_when_relaxed
#print axioms EDSL.Tests.C23AtomicWeakening.strengthening_a_legal_graph_can_destroy_legality
#audit_edsl
