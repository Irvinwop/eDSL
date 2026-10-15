/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientCoverage
import EDSL.Examples.FutexClient
import EDSL.Audit

namespace EDSL.Tests.FutexClientCoverage
open X86 OS OS.Futex OS.Futex.Clients Examples.FutexClient
open Examples.Futex (checked checked_ok)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- These steps run only the ordinary physical decoder/scheduler. No managed
-- adapter result or successful managed schedule is used to construct them.
def peerMove := checked (Suspend.issue initial.suspended 2) (by rfl)
def peerStore := checked (Suspend.issue peerMove.1 2) (by rfl)
def peerReturn := checked (Suspend.issue peerStore.1 2) (by rfl)
def payloadMove := checked (Suspend.issue peerReturn.1 1) (by rfl)
def payloadStore := checked (Suspend.issue payloadMove.1 1) (by rfl)
def replacementMove := checked (Suspend.issue payloadStore.1 1) (by rfl)
def blocked := checked (Suspend.issue replacementMove.1 1) (by rfl)
def ownDrain := checked (Suspend.drain blocked.1 1) (by rfl)
def exchanged := checked (Suspend.issue ownDrain.1 1) (by rfl)

def actions : List Runtime.Action :=
  [.issue 2, .issue 2, .issue 2, .issue 1, .issue 1, .issue 1, .issue 1, .drain 1, .issue 1]

def observations : List Runtime.Observation :=
  [peerMove.2, peerStore.2, peerReturn.2, payloadMove.2, payloadStore.2,
   replacementMove.2, blocked.2, ownDrain.2, exchanged.2].map .physical

theorem physical_prefix : MachineTrace initial.suspended actions observations exchanged.1 :=
  .issue (checked_ok _ (by rfl)) (.issue (checked_ok _ (by rfl)) (.issue (checked_ok _ (by rfl))
    (.issue (checked_ok _ (by rfl)) (.issue (checked_ok _ (by rfl)) (.issue (checked_ok _ (by rfl))
      (.issue (checked_ok _ (by rfl)) (.drain (checked_ok _ (by rfl)) (.issue (checked_ok _ (by rfl)) .nil))))))))

-- This catches accidental eager STORE publication, syscall-style flushing,
-- or allowing XCHG past its own nonempty FIFO. The peer is already returned.
example : loadDWord blocked.1.machine.memory 262144 = .ok 0 ∧
    loadDWord blocked.1.machine.memory 65536 = .ok 0 ∧
    blocked.2 = .machine (.blocked 1) ∧
    (blocked.1.machine.workers[1]?).map TSO.Worker.buffer = some [⟨262144, 0x11223344⟩] ∧
    (blocked.1.machine.workers[2]?).map TSO.Worker.returned = some true ∧
    (blocked.1.machine.workers[2]?).map TSO.Worker.buffer = some [⟨131072, 0x55667788⟩] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- The managed trace is an enabledness conclusion from the independent raw
-- prefix. It preserves the returned peer's distinct, still-buffered payload.
theorem entire_raw_prefix_lifts :
    ∃ final, Runtime.Trace profile initial actions observations final ∧
      Admitted cohort final ∧ final.suspended = exchanged.1 ∧
      loadDWord final.suspended.machine.memory 262144 = .ok 0x11223344 ∧
      loadDWord final.suspended.machine.memory 65536 = .ok 1 ∧
      loadDWord final.suspended.machine.memory 131072 = .ok 0 ∧
      (final.suspended.machine.workers[2]?).map TSO.Worker.buffer = some [⟨131072, 0x55667788⟩] := by
  obtain ⟨final, trace, physical, valid⟩ := physical_prefix.lift initial_admitted rfl
  refine ⟨final, trace, valid, physical, ?_, ?_, ?_, ?_⟩
  all_goals rw [physical]; rfl

-- An arbitrary supported continuation cannot reset W after this exact XCHG,
-- including a late drain from the returned producer. Publication is derived
-- from the real atomic event and present admission, not assumed at a PC.
theorem actual_exchange_and_all_suffixes :
    ∃ before, Admitted cohort before ∧ before.suspended = ownDrain.1 ∧
      loadDWord before.suspended.machine.memory 262144 = .ok 0x11223344 ∧
      (∀ (after : Suspend.State),
        Suspend.issue before.suspended 1 = .ok (after, .machine (.retired 1 (some ⟨65536, 0, 1⟩))) →
        loadDWord after.machine.memory 262144 = .ok 0x11223344 ∧
        loadDWord after.machine.memory 65536 = .ok 1) ∧
      (∀ (current : Futex.State) (next : Futex.State) (suffix : List Runtime.Action)
          (seen : List Runtime.Observation),
        Admitted cohort current → current.suspended = exchanged.1 →
        Runtime.Trace profile current suffix seen next →
        loadDWord next.suspended.machine.memory 65536 = .ok 1) := by
  have raw : MachineTrace initial.suspended (actions.take 8) (observations.take 8) ownDrain.1 :=
    .issue (checked_ok _ (by rfl)) (.issue (checked_ok _ (by rfl)) (.issue (checked_ok _ (by rfl))
      (.issue (checked_ok _ (by rfl)) (.issue (checked_ok _ (by rfl)) (.issue (checked_ok _ (by rfl))
        (.issue (checked_ok _ (by rfl)) (.drain (checked_ok _ (by rfl)) .nil)))))))
  obtain ⟨before, _, physical, valid⟩ := raw.lift initial_admitted rfl
  refine ⟨before, valid, physical, ?_, ?_, ?_⟩
  · rw [physical]; rfl
  · intro after actual
    obtain ⟨client, member, _, _, _, _, payload, word⟩ :=
      publisher_exchange_publishes_payload valid actual
    have same : client = publisher := Option.some.inj member.symm
    subst client
    exact ⟨payload, word⟩
  · intro current next suffix seen admitted currentPhysical continuation
    exact published_word_trace admitted (by rw [currentPhysical]; rfl) continuation

-- This extension has no supplied managed-drain success. The actual FIFO head
-- and its retained current grant suffice after the physical-only prefix.
theorem returned_peer_demand_extends :
    ∃ final next, Runtime.Trace profile initial actions observations final ∧
      Runtime.step profile final (.drain 2) =
        .ok (next, .physical (.machine (.drained 2 ⟨131072, 0x55667788⟩))) ∧
      Admitted cohort next ∧
      loadDWord next.suspended.machine.memory 65536 = .ok 1 ∧
      loadDWord next.suspended.machine.memory 262144 = .ok 0x11223344 ∧
      loadDWord next.suspended.machine.memory 131072 = .ok 0x55667788 ∧
      (next.suspended.machine.workers[2]?).map TSO.Worker.returned = some true := by
  obtain ⟨final, trace, physical, valid⟩ := physical_prefix.lift initial_admitted rfl
  let drained := checked (Suspend.drain exchanged.1 2) (by rfl)
  have actual : Suspend.drain final.suspended 2 =
      .ok (drained.1, .machine (.drained 2 ⟨131072, 0x55667788⟩)) := by rw [physical]; rfl
  obtain ⟨next, enabled, nextPhysical, nextValid⟩ := drain_lift valid actual
  have step : Runtime.step profile final (.drain 2) =
      .ok (next, .physical (.machine (.drained 2 ⟨131072, 0x55667788⟩))) := by
    change Runtime.step cohort.profile final (.drain 2) = _
    simp [Runtime.step, enabled]
  refine ⟨final, next, trace, step, nextValid,
    published_word_step valid (by rw [physical]; rfl) step, ?_, ?_, ?_⟩
  all_goals rw [nextPhysical]; rfl

end EDSL.Tests.FutexClientCoverage

#audit_edsl
