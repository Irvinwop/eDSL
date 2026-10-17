/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.FutexNotification
import EDSL.OS.Futex.ClientNotification
import EDSL.Audit

namespace EDSL.Tests.FutexNotification
open X86 OS OS.Futex OS.Futex.Clients Examples.FutexNotification
open Examples.Futex (checked checked_ok)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! These fixtures execute the decoder, FIFO, syscall capture, current-pin
comparison, WAKE1, private resume and RET. Expected observations below are
specified separately from the scheduled operations. This is portable Lean
model evidence, not native Linux or hardware execution evidence. -/

def readyRaw (state : Futex.State) (invocation : Nat) : Option Word := do
  let call ← state.calls invocation
  match call.phase with
  | .ready outcome _ => some outcome.raw
  | _ => none

def capturedWord (state : Futex.State) (worker : Nat) : Option (Except X86.Error (BitVec 32)) :=
  (state.suspended.pending worker).map fun saved => loadDWord saved.request.user.memory 65536

/-- RAM and observations distinguish an ordinary store, a returned buffered
peer, a blocked atomic instruction, and the publisher's actual FIFO drain. -/
theorem preparation_observed :
    prepared.2 =
      [.physical (.machine (.retired 2 none)), .physical (.machine (.retired 2 none)),
       .physical (.machine (.retired 2 none)), .physical (.machine (.retired 1 none)),
       .physical (.machine (.retired 1 none)), .physical (.machine (.retired 1 none)),
       .physical (.machine (.blocked 1)), .physical (.machine (.drained 1 ⟨262144, 0x11223344⟩))] ∧
    loadDWord prepared.1.suspended.machine.memory 65536 = .ok 0 ∧
    loadDWord prepared.1.suspended.machine.memory 262144 = .ok 0x11223344 ∧
    loadDWord prepared.1.suspended.machine.memory 131072 = .ok 0 ∧
    (prepared.1.suspended.machine.workers[2]?).map TSO.Worker.returned = some true ∧
    (prepared.1.suspended.machine.workers[2]?).map TSO.Worker.buffer = some [⟨131072, 0x55667788⟩] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Entry before publication records historical zero; comparison after the
actual XCHG must nevertheless return EAGAIN. A late capture records one.
The early equal comparison instead really queues and is selected by WAKE1. -/
theorem comparison_cuts_observed :
    queued.1.queue = [0] ∧ readyRaw queued.1 0 = none ∧
    readyRaw queuedWoken 0 = some 0 ∧ readyRaw queuedWoken 1 = some 1 ∧
    capturedWord betweenWoken 0 = some (.ok 0) ∧
    readyRaw betweenWoken 0 = some 0xfffffffffffffff5 ∧ readyRaw betweenWoken 1 = some 0 ∧
    capturedWord lateCompared.1 0 = some (.ok 1) ∧
    readyRaw lateCompared.1 1 = some 0xfffffffffffffff5 ∧ readyRaw lateCompared.1 0 = some 0 ∧
    loadDWord betweenWoken.suspended.machine.memory 65536 = .ok 1 ∧
    lateCompared.1.queue = [] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Publication alone does not discharge an already queued WAIT. -/
theorem publication_does_not_clear_queued :
    loadDWord queuedExchange.1.suspended.machine.memory 65536 = .ok 1 ∧
    ¬ Futex.Notification.NoQueuedWait queuedExchange.1 0 := by
  refine ⟨rfl, ?_⟩
  intro clear
  exact clear 0 ⟨0, .wait 0, 2, .queued⟩ rfl rfl (queued_queued _ _ _)

def AllSuffixes (state : Futex.State) : Prop :=
  ∀ {actions observations after}, Runtime.Trace profile state actions observations after →
    Futex.Notification.NoQueuedWait after 0 ∧
    loadDWord after.suspended.machine.memory 65536 = .ok 1 ∧ Admitted cohort after

/-- Concrete associated publisher XCHG/WAKE1, followed by every accepted
mixed suffix, including service retries, arbitrary clobbers and peer drains. -/
theorem queued_all_suffixes : AllSuffixes queuedWoken := by
  intro actions observations after later
  have exchange : Physical.issue profile queued.1 1 =
      .ok (queuedExchange.1, .machine (.retired 1 (some ⟨65536, 0, 1⟩))) := rfl
  have between := Runtime.schedule_trace profile queuedExchange.1 publisherEntry queuedWaking (checked_ok _ _)
  have associated : queuedWaking.1.calls 1 = some ⟨1, .wakeOne, 3, .entered⟩ := rfl
  exact (Clients.Notification.exchange_wake_trace policy queued_admitted exchange between associated
    (checked_ok (wakeOne queuedWaking.1 1 (some 0)) (by rfl)) later).2

theorem between_all_suffixes : AllSuffixes betweenWoken := by
  intro actions observations after later
  have exchange : Physical.issue profile entered.1 1 =
      .ok (enteredExchange.1, .machine (.retired 1 (some ⟨65536, 0, 1⟩))) := rfl
  have between := Runtime.schedule_trace profile enteredExchange.1 betweenActions betweenWaking (checked_ok _ _)
  have associated : betweenWaking.1.calls 1 = some ⟨1, .wakeOne, 3, .entered⟩ := rfl
  exact (Clients.Notification.exchange_wake_trace policy entered_admitted exchange between associated
    (checked_ok (wakeOne betweenWaking.1 1 none) (by rfl)) later).2

theorem late_all_suffixes : AllSuffixes lateWoken := by
  intro actions observations after later
  have exchange : Physical.issue profile prepared.1 1 =
      .ok (lateExchange.1, .machine (.retired 1 (some ⟨65536, 0, 1⟩))) := rfl
  have between := Runtime.schedule_trace profile lateExchange.1 publisherEntry lateWaking (checked_ok _ _)
  have associated : lateWaking.1.calls 0 = some ⟨1, .wakeOne, 2, .entered⟩ := rfl
  exact (Clients.Notification.exchange_wake_trace policy prepared_admitted exchange between associated
    (checked_ok (wakeOne lateWaking.1 0 none) (by rfl)) later).2

/-- Retry really re-reads present RAM rather than retaining the equal result
which originally queued this same invocation. The later wake selects nobody. -/
theorem retry_observed_and_all_suffixes :
    readyRaw retryWoken 0 = some 0xfffffffffffffff5 ∧
    readyRaw retryWoken 1 = some 0 ∧ capturedWord retryWoken 0 = some (.ok 0) ∧
    AllSuffixes retryWoken := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro actions observations after later
  have exchange : Physical.issue profile queued.1 1 =
      .ok (queuedExchange.1, .machine (.retired 1 (some ⟨65536, 0, 1⟩))) := rfl
  have between := Runtime.schedule_trace profile queuedExchange.1 retryActions retryWaking (checked_ok _ _)
  have associated : retryWaking.1.calls 1 = some ⟨1, .wakeOne, 3, .entered⟩ := rfl
  exact (Clients.Notification.exchange_wake_trace policy queued_admitted exchange between associated
    (checked_ok (wakeOne retryWaking.1 1 none) (by rfl)) later).2

/-- Late entry leaves only an entered request. Current admission and the
notification theorem construct compare/resume/RET in at most three steps for
every full-width private clobber; no future successful compare is assumed. -/
theorem late_pending_finishes (flags rcx r11 : Word) :
    ∃ after, Clients.Notification.FinishesWithin 3 cohort 0 0 flags rcx r11 lateEntered.1 after ∧
      Admitted cohort after := by
  have enteredTrace := Runtime.schedule_trace profile lateWoken waiterEntry lateEntered (checked_ok _ _)
  obtain ⟨clear, word, admitted⟩ := late_all_suffixes enteredTrace
  let saved := (lateEntered.1.suspended.pending 0).get (by rfl)
  exact Clients.Notification.pending_worker_finishes policy admitted word clear
    (show lateEntered.1.suspended.pending 0 = some saved from rfl) flags rcx r11

/-- A typed selected readiness also constructs its real two-step suffix,
without assuming a future scheduler selection or successful RET. -/
theorem selected_pending_finishes (flags rcx r11 : Word) :
    ∃ after, Clients.Notification.FinishesWithin 2 cohort 0 0 flags rcx r11 queuedWoken after ∧
      Admitted cohort after := by
  exact Clients.Notification.ready_finishes (queued_all_suffixes Runtime.Trace.nil).2.2
    (show queuedWoken.calls 0 = some ⟨0, .wait 0, 2, .ready .waitZero (.wake 1)⟩ from rfl)
    flags rcx r11

def finish (invocation : Nat) : List Runtime.Action :=
  [.service (.resume invocation 0x1122334455667788 0x8877665544332211 0xfedcba9876543210), .issue 0]

def selectedReturned := checked (Runtime.schedule profile queuedWoken (finish 0)) (by rfl)
def betweenReturned := checked (Runtime.schedule profile betweenWoken (finish 0)) (by rfl)
def lateReturned := checked (Runtime.schedule profile lateCompared.1 (finish 1)) (by rfl)
def spuriousReturned := checked (Runtime.schedule profile spurious.1 (finish 0)) (by rfl)

def returnView (state : Futex.State) : Option (Bool × Word × Word × Word × Word × Word × Word) :=
  (state.suspended.machine.workers[0]?).map fun worker =>
    (worker.returned, worker.context.registers .rax, worker.context.rip, worker.context.registers .rsp,
      worker.context.flags, worker.context.registers .rcx, worker.context.registers .r11)

/-- Independent ABI observations catch truncation/sign-extension, wrong
continuation/stack, private-register restoration and accidental peer flushes. -/
theorem returns_observed :
    returnView selectedReturned.1 = some
      (true, 0, 0x6000, 32776, 0x1122334455667788, 0x8877665544332211, 0xfedcba9876543210) ∧
    returnView betweenReturned.1 = some
      (true, 0xfffffffffffffff5, 0x6000, 32776, 0x1122334455667788, 0x8877665544332211, 0xfedcba9876543210) ∧
    returnView lateReturned.1 = some
      (true, 0xfffffffffffffff5, 0x6000, 32776, 0x1122334455667788, 0x8877665544332211, 0xfedcba9876543210) ∧
    (selectedReturned.1.suspended.machine.workers[2]?).map TSO.Worker.buffer =
      some [⟨131072, 0x55667788⟩] ∧
    loadDWord selectedReturned.1.suspended.machine.memory 131072 = .ok 0 ∧
    selectedReturned.1.calls 0 = none ∧ selectedReturned.1.suspended.pending 0 = none ∧
    Atomics.authorize selectedReturned.1.authority 90 2 = .error .missingHandle := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Zero WAIT can finish while publication is still false, even in the
well-formed admitted sole-WAIT cohort. No wake or acquisition follows. -/
theorem spurious_zero_without_publication :
    Admitted cohort spuriousReturned.1 ∧
    returnView spuriousReturned.1 = some
      (true, 0, 0x6000, 32776, 0x1122334455667788, 0x8877665544332211, 0xfedcba9876543210) ∧
    readyRaw spurious.1 0 = some 0 ∧
    loadDWord spuriousReturned.1.suspended.machine.memory 65536 = .ok 0 := by
  exact ⟨(queued_admitted.schedule (checked_ok _ _)).schedule (checked_ok _ _), rfl, rfl, rfl⟩

def rawPeerDrain := checked (Suspend.drain selectedReturned.1.suspended 2) (by rfl)

/-- An actual returned peer's nonempty FIFO has a managed lift with the same
observation and notification safety. Managed replay is a conclusion. -/
theorem returned_peer_drain_lifts :
    ∃ after, Runtime.Trace profile selectedReturned.1 [.drain 2]
      [.physical (.machine (.drained 2 ⟨131072, 0x55667788⟩))] after ∧
      Futex.Notification.NoQueuedWait after 0 ∧ Admitted cohort after ∧
      loadDWord after.suspended.machine.memory 65536 = .ok 1 ∧
      loadDWord after.suspended.machine.memory 131072 = .ok 0x55667788 ∧
      (after.suspended.machine.workers[2]?).map TSO.Worker.returned = some true ∧
      (after.suspended.machine.workers[2]?).map TSO.Worker.buffer = some [] := by
  have completed := Runtime.schedule_trace profile queuedWoken (finish 0) selectedReturned (checked_ok _ _)
  obtain ⟨clear, word, admitted⟩ := queued_all_suffixes completed
  have actual : Suspend.drain selectedReturned.1.suspended 2 =
      .ok (rawPeerDrain.1, .machine (.drained 2 ⟨131072, 0x55667788⟩)) := rfl
  obtain ⟨after, trace, same, safe, published, valid⟩ :=
    Clients.Notification.machineTrace_lift policy admitted word clear (MachineTrace.drain actual .nil)
  refine ⟨after, trace, safe, valid, published, ?_, ?_, ?_⟩
  all_goals rw [same]; rfl

/-- Safety does not imply all-scheduler return: a ready pending worker can
remain unreturned along an admitted, safe infinite idle execution. -/
theorem safe_ready_can_idle_forever :
    Runtime.Infinite profile (fun _ => queuedWoken) (fun _ => .service .idle)
      (fun _ => .serviced .idle) ∧
    (queuedWoken.suspended.machine.workers[0]?).map TSO.Worker.returned = some false ∧
    ∀ index : Nat, Futex.Notification.NoQueuedWait ((fun _ : Nat => queuedWoken) index) 0 := by
  have execution : Runtime.Infinite profile (fun _ => queuedWoken) (fun _ => .service .idle)
      (fun _ => .serviced .idle) := fun _ => rfl
  obtain ⟨clear, word, admitted⟩ := queued_all_suffixes Runtime.Trace.nil
  have safety := Clients.Notification.infinite_preserves policy admitted word clear execution
  exact ⟨execution, rfl, fun index => (safety index).1⟩

/-- Without the sole-WAIT restriction, selecting an eligible other invocation
preserves a queued survivor. This service-level limit needs no client policy
or future scheduling assumption. -/
theorem wake_other_preserves_queued (state : Futex.State)
    (waker target survivor owner pin waitingWorker waitingPin : Nat) (expected : BitVec 32)
    (call : Call)
    (waking : state.calls waker = some ⟨owner, .wakeOne, pin, .entered⟩)
    (waiting : state.calls target = some ⟨waitingWorker, .wait expected, waitingPin, .queued⟩)
    (survives : state.calls survivor = some call) (queued : Queued call)
    (different : target ≠ waker) (eligible : target ∈ state.queue)
    (otherTarget : survivor ≠ target) (otherWaker : survivor ≠ waker) :
    ∃ after, wakeOne state waker (some target) = .ok after ∧
      after.calls survivor = some call ∧ ¬ Futex.Notification.NoQueuedWait after call.worker := by
  refine ⟨_, wakeOne_selected _ _ _ _ _ _ _ _ waking waiting different eligible, ?_, ?_⟩
  · simpa [setPhase, putCall, otherTarget, otherWaker] using survives
  · intro clear
    apply clear survivor call _ rfl queued
    simpa [setPhase, putCall, otherTarget, otherWaker] using survives

def twoWaitersBeforeWake := checked (Runtime.schedule Examples.FutexClient.profile Examples.FutexClient.initial
  (prepare ++ waiterEntry ++ [.service (.compare 0), .issue 3, .issue 3, .issue 3,
    .service (.compare 1), .issue 1] ++ publisherEntry)) (by rfl)

def otherSelected := checked (wakeOne twoWaitersBeforeWake.1 2 (some 1)) (by rfl)

/-- Real four-client execution supplies the abstract limit's witness: W=1,
the actual publisher's WAKE1 returns one, worker3 is ready, worker0 is queued.
It remains admitted under the original cohort, which fails the new policy. -/
theorem multiple_waiters_outside_policy :
    Admitted Examples.FutexClient.cohort twoWaitersBeforeWake.1 ∧
    Admitted Examples.FutexClient.cohort otherSelected ∧
    ¬ Clients.Notification.Policy Examples.FutexClient.cohort 0 0 ∧
    loadDWord otherSelected.suspended.machine.memory 65536 = .ok 1 ∧
    readyRaw otherSelected 1 = some 0 ∧ readyRaw otherSelected 2 = some 1 ∧
    ¬ Futex.Notification.NoQueuedWait otherSelected 0 := by
  have before : Admitted Examples.FutexClient.cohort twoWaitersBeforeWake.1 :=
    Examples.FutexClient.initial_admitted.schedule (checked_ok _ _)
  have step : Runtime.step Examples.FutexClient.profile twoWaitersBeforeWake.1
      (.service (.wake 2 (some 1))) = .ok (otherSelected, .serviced (.wake 2 (some 1))) := rfl
  refine ⟨before, admitted_step before step, ?_, rfl, rfl, rfl, ?_⟩
  · intro policy
    have impossible := policy.sole 3 Examples.FutexClient.otherWaiter 0 rfl rfl
    omega
  · obtain ⟨after, actual, _, remains⟩ := wake_other_preserves_queued twoWaitersBeforeWake.1
      2 1 0 1 4 3 3 0 ⟨0, .wait 0, 2, .queued⟩ rfl rfl rfl
      (queued_queued _ _ _) (by decide) (by decide) (by decide) (by decide)
    have same : after = otherSelected := Except.ok.inj
      (actual.symm.trans (checked_ok (wakeOne twoWaitersBeforeWake.1 2 (some 1)) (by rfl)))
    exact same ▸ remains

end EDSL.Tests.FutexNotification

#audit_edsl
