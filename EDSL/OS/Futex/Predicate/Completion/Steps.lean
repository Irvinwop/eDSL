/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Completion.Instructions
import EDSL.OS.Futex.Predicate.Physical
import EDSL.OS.Futex.ClientNotification.Base

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate.Completion
open X86

/-- The reused physical notification lemma is profile-generic: it requires
neither the old client admission nor its old straight-line WAIT policy. -/
theorem selected_issue_lift {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {suspended : Suspend.State} {observation : Suspend.Observation}
    (admitted : Admitted cohort state) (clear : Futex.Notification.NoQueuedWait state worker)
    (issued : Suspend.issue state.suspended worker = .ok (suspended, observation)) :
    ∃ after, Runtime.step cohort.profile state (.issue worker) = .ok (after, .physical observation) ∧
      after.suspended = suspended ∧ Admitted cohort after ∧
      Futex.Notification.NoQueuedWait after worker := by
  obtain ⟨after, lifted, exactState, valid⟩ := issue_lift admitted issued
  exact ⟨after, by simp [Runtime.step, lifted], exactState, valid,
    Clients.Notification.issue_preserves clear lifted⟩

theorem service_clear {cohort : Cohort} {state after : Futex.State} {worker : Nat}
    {client : Client} {action : Futex.Action} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker)
    (serviced : Futex.step cohort.profile.service state action = .ok after) :
    Futex.Notification.NoQueuedWait after worker := by
  have designated : worker = cohort.waiter :=
    (admitted.static.descriptors worker (.waitLoop client) member).2.2.2.2
  have expected : Futex.Notification.ExpectedFor state worker 0 := by
    rw [designated]
    exact admitted.expectedFor
  exact Futex.Notification.service_preserves admitted.runtime.service (admitted.currentWord published)
    (by decide) expected clear serviced

theorem ordinary_step {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} {point : Point} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker)
    (running : RunningAt client worker state.suspended point)
    (notCall : point ≠ .syscall) (notReturn : ∀ observed, point ≠ .done observed) :
    ∃ after next,
      Runtime.step cohort.profile state (.issue worker) =
        .ok (after, .physical (.machine (.retired worker none))) ∧
      Admitted cohort after ∧ Cut client worker after (remaining next) ∧
      remaining next + 1 ≤ remaining point ∧
      PrivateFrame worker state.suspended after.suspended ∧
      Futex.Notification.NoQueuedWait after worker := by
  obtain ⟨next, context, issued, current, bound, frame⟩ :=
    ordinary_issue admitted member published running notCall notReturn
  obtain ⟨after, lifted, same, valid, afterClear⟩ := selected_issue_lift admitted clear issued
  exact ⟨after, next, lifted, valid, .running (same ▸ current), bound, same ▸ frame, afterClear⟩

theorem capture_step {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (clear : Futex.Notification.NoQueuedWait state worker)
    (running : RunningAt client worker state.suspended .syscall) :
    ∃ after count,
      Runtime.step cohort.profile state (.issue worker) =
        .ok (after, .physical (.entered worker state.suspended.nextCall)) ∧
      Admitted cohort after ∧ Cut client worker after count ∧ count ≤ 9 ∧
      PrivateFrame worker state.suspended after.suspended ∧
      Futex.Notification.NoQueuedWait after worker := by
  obtain ⟨actual, found, current, live, free, empty⟩ := running
  obtain ⟨issued, pending, _, _, _⟩ := syscall_enabled found current live free empty
    (admitted.protected worker (.waitLoop client) member).2.2.1
  obtain ⟨after, lifted, same, valid, afterClear⟩ := selected_issue_lift admitted clear issued
  have afterPending := same ▸ pending
  obtain ⟨count, bound, cut⟩ := pending_cut valid member afterClear afterPending
  refine ⟨after, count, lifted, valid, cut, bound, ?_, afterClear⟩
  rw [same]
  exact ⟨rfl, fun _ different => ⟨rfl, by simp [Suspend.capture, different]⟩⟩

theorem return_step {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} {observed : BitVec 32} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (clear : Futex.Notification.NoQueuedWait state worker)
    (running : RunningAt client worker state.suspended (.done observed)) :
    ∃ after,
      Runtime.step cohort.profile state (.issue worker) =
        .ok (after, .physical (.machine (.retired worker none))) ∧
      Admitted cohort after ∧ Cut client worker after 0 ∧
      PrivateFrame worker state.suspended after.suspended ∧
      Futex.Notification.NoQueuedWait after worker := by
  obtain ⟨actual, found, current, live, free, empty⟩ := running
  have ready := admitted.loop_ready member (.done observed)
  obtain ⟨issued, selected, _, _⟩ := ret_enabled found current live free empty
    (admitted.protected worker (.waitLoop client) member).2.2.1 ready.1 ready.2
  obtain ⟨after, lifted, same, valid, afterClear⟩ := selected_issue_lift admitted clear issued
  refine ⟨after, lifted, valid, .returned (same ▸ selected) rfl, ?_, afterClear⟩
  rw [same]
  exact ⟨rfl, fun _ different => ⟨retire_peer different, rfl⟩⟩

/-- Actual pinned current-RAM comparison creates typed EAGAIN readiness. The
next cut still has eight actions: service readiness is not program completion. -/
theorem compare_step {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} {saved : Suspend.Saved} {pin : Nat} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker)
    (pending : state.suspended.pending worker = some saved)
    (found : state.calls saved.identifier = some ⟨worker, .wait 0, pin, .entered⟩) :
    ∃ after,
      Runtime.step cohort.profile state (.service (.compare saved.identifier)) =
        .ok (after, .serviced (.compare saved.identifier)) ∧
      Admitted cohort after ∧ Cut client worker after 8 ∧
      PrivateFrame worker state.suspended after.suspended ∧
      Futex.Notification.NoQueuedWait after worker := by
  have compared := Futex.Notification.compare_mismatch_enabled admitted.runtime.service
    (admitted.currentWord published) (by decide) found
  let after := setPhase state saved.identifier ⟨worker, .wait 0, pin, .entered⟩
    (.ready .waitAgain .mismatch)
  have actual : Futex.step cohort.profile.service state (.compare saved.identifier) = .ok after := compared
  have runtime : Runtime.step cohort.profile state (.service (.compare saved.identifier)) =
      .ok (after, .serviced (.compare saved.identifier)) := by
    simp [Runtime.step, actual, Except.mapError]
  exact ⟨_, runtime, admitted_step admitted runtime,
    .ready (pin := pin) (outcome := .waitAgain) (origin := .mismatch)
      pending (by simp [after, setPhase, putCall]), PrivateFrame.refl _ _,
    service_clear admitted member published clear actual⟩

/-- Only a resume actually executed by this suffix chooses new full-word
clobbers. Its current typed result and saved request determine the real context
at19. Already-resumed cuts never pass through this operation. -/
theorem resume_step {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} {saved : Suspend.Saved} {pin : Nat}
    {outcome : Outcome (.wait 0)} {origin : Origin} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker)
    (pending : state.suspended.pending worker = some saved)
    (found : state.calls saved.identifier = some ⟨worker, .wait 0, pin, .ready outcome origin⟩)
    (flags rcx r11 : Word) :
    ∃ after raw,
      Runtime.step cohort.profile state (.service (.resume saved.identifier flags rcx r11)) =
        .ok (after, .serviced (.resume saved.identifier flags rcx r11)) ∧
      Admitted cohort after ∧ Cut client worker after (remaining (.resumed raw)) ∧
      PrivateFrame worker state.suspended after.suspended ∧
      Futex.Notification.NoQueuedWait after worker := by
  obtain ⟨after, serviced, valid⟩ := service_lift admitted
    (action := .resume saved.identifier flags rcx r11) ⟨_, outcome, origin, found, rfl⟩
  obtain ⟨call, result, _, _, suspended, _, atCall, _, _, resumed, _, exactAfter⟩ :=
    resumeReady_effect serviced
  have owner : call.worker = worker := congrArg Call.worker (Option.some.inj (atCall.symm.trans found))
  rw [owner] at resumed
  have savedValid := admitted.runtime.service.suspended.pending worker saved pending
  obtain ⟨actual, selected, live, empty, _⟩ := savedValid.live
  obtain ⟨kind, atKind, family⟩ := admitted.pending_family pending
  cases Option.some.inj (atKind.symm.trans member)
  change client.Family saved.request at family
  obtain ⟨enabled, selectedAfter, current, _, consumed, _, _, _⟩ :=
    resume_enabled selected live pending savedValid.owner family empty result.raw flags rcx r11
  have exactSuspended : after.suspended = resumedState state.suspended worker saved.request
      result.raw flags rcx r11 := by
    rw [exactAfter]
    exact Except.ok.inj (resumed.symm.trans enabled)
  refine ⟨after, result.raw, by simp [Runtime.step, serviced, Except.mapError], valid,
    .running ?_, ?_, service_clear admitted member published clear serviced⟩
  · rw [exactSuspended]
    exact ⟨_, selectedAfter, current, rfl, consumed, rfl⟩
  · rw [exactSuspended]
    exact ⟨rfl, fun _ different => resumedState_peer different⟩

end EDSL.OS.Futex.Predicate.Completion

#audit_edsl
