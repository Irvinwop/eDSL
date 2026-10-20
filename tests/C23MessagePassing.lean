/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.C23MessagePassing
open Concurrency.C23Atomic

/-- The writer stores payload=42 then releases flag=1. The reader acquires
flag=1 from that release, then reads the initial payload=0. Initial writes are
separate identities for the two objects. This is the forbidden stale-payload
outcome, expressed as source events rather than an expected execution input. -/
def stale : Candidate Nat Nat where
  events := [⟨none, 0, .initialize 0⟩, ⟨none, 1, .initialize 0⟩,
    ⟨some 11, 0, .store .relaxed 42⟩, ⟨some 11, 1, .store .release 1⟩,
    ⟨some 12, 1, .load .acquire 1⟩, ⟨some 12, 0, .load .relaxed 0⟩]
  readsFrom index := if index = 4 then some 3 else if index = 5 then some 0 else none
  rank index := if index = 2 ∨ index = 3 then 1 else 0

/-- The generic source rule rejects the classic message-passing outcome in
which an acquire observes the release but the subsequent payload read is older
than the writer's preceding payload store. No source/machine mapping is assumed. -/
theorem qualifying_acquire_rejects_stale_payload : ¬ Legal stale := by
  intro legal
  have payload : Writes stale 2 0 42 := ⟨_, rfl, rfl, rfl⟩
  have beforeRelease : SeqBefore stale 2 3 :=
    ⟨by decide, _, _, 11, rfl, rfl, rfl, rfl⟩
  have acquired : Acquires stale 4 := ⟨_, rfl, rfl⟩
  have flagSource : ReadsFrom stale 4 3 :=
    ⟨rfl, 1, 1, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩⟩
  have member : ReleaseMember stale 3 3 :=
    releaseMember_self ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl, rfl⟩
  have afterAcquire : SeqBefore stale 4 5 :=
    ⟨by decide, _, _, 12, rfl, rfl, rfl, rfl⟩
  have observed : Reads stale 5 0 0 := ⟨_, rfl, rfl, rfl⟩
  have payloadSource : ReadsFrom stale 5 0 :=
    ⟨rfl, 0, 0, observed, ⟨_, rfl, rfl, rfl⟩⟩
  have impossible : stale.rank 2 ≤ stale.rank 0 :=
    legal.message_passing_not_older payload beforeRelease acquired flagSource member
      afterAcquire observed payloadSource
  exact (by decide : ¬ (1 ≤ 0)) impossible

/-- A relaxed RMW reads the initial value despite an intervening modification
in the same object’s MO. Sparse ranks emphasize order rather than adjacency. -/
def skippedPredecessor : Candidate Nat Nat where
  events := [⟨none, 0, .initialize 0⟩,
    ⟨some 11, 0, .store .relaxed 1⟩, ⟨some 12, 0, .rmw .relaxed 0 2⟩]
  readsFrom index := if index = 2 then some 0 else none
  rank index := if index = 0 then 0 else if index = 1 then 7 else 19

/-- Matching the observed bits is insufficient: RMW must select the immediate
preceding modification, even when there is no synchronizes-with edge. -/
theorem rmw_cannot_skip_actual_predecessor : ¬ Legal skippedPredecessor := by
  intro legal
  have rmw : IsRMW skippedPredecessor 2 := ⟨_, rfl, rfl⟩
  have source : ReadsFrom skippedPredecessor 2 0 :=
    ⟨rfl, 0, 0, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩⟩
  have before : ModBefore skippedPredecessor 0 1 :=
    ⟨0, 0, 1, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩, by decide⟩
  have after : ModBefore skippedPredecessor 1 2 :=
    ⟨0, 1, 2, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩, by decide⟩
  exact (legal.rmwPredecessor rmw source).2 1 before after

end EDSL.Tests.C23MessagePassing

#print axioms EDSL.Concurrency.C23Atomic.Legal.message_passing_value
#audit_edsl
