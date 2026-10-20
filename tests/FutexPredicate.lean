/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.FutexPredicate
import EDSL.OS.Futex.Predicate.Physical
import EDSL.OS.Futex.Predicate.Completion
import EDSL.OS.Futex.Predicate.Notification
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.FutexPredicate
open X86 OS OS.Futex OS.Futex.Predicate Examples.FutexPredicate
open Examples.Futex (checked checked_ok)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! These tests execute actual decoder, physical, suspension and managed
service transitions. Expected machine observations are independent of the
schedule definitions. No later cut is assumed admitted, and no desired final
machine state is installed by a fixture. This is portable model evidence. -/

def registerAt (state : Futex.State) (register : Register) : Option Word :=
  (state.suspended.machine.workers[0]?).map fun worker => worker.context.registers register

def returnView (state : Futex.State) : Option (Bool × Word × Word × Word × Word × Word × Word) :=
  (state.suspended.machine.workers[0]?).map fun worker =>
    (worker.returned, worker.context.registers .rax, worker.context.rip,
      worker.context.registers .rsp, worker.context.flags,
      worker.context.registers .rcx, worker.context.registers .r11)

def decoded (state : Futex.State) : Option (Except X86.Error Instruction) :=
  (state.suspended.machine.workers[0]?).map fun worker =>
    decodeAt (TSO.sharedState state.suspended.machine worker)

def zeroFlag (state : Futex.State) : Option Bool :=
  (state.suspended.machine.workers[0]?).map fun worker => worker.context.flags.getLsbD 6

def readyRaw (state : Futex.State) (invocation : Nat) : Option Word := do
  let call ← state.calls invocation
  match call.phase with
  | .ready outcome _ => some outcome.raw
  | _ => none

def capturedWord (state : Futex.State) (worker : Nat) : Option (Except X86.Error (BitVec 32)) :=
  (state.suspended.pending worker).map fun saved => loadDWord saved.request.user.memory 65536

def capturedIdentity (state : Futex.State) : Option (Nat × Nat × Word × Word × Word × Word) :=
  (state.suspended.pending 0).map fun saved =>
    (saved.identifier, saved.worker, saved.request.continuation, saved.request.user.flags,
      saved.request.user.registers .rcx, saved.request.user.registers .r11)

/-- Real FIFO behavior distinguishes publication, ordinary payload stores,
blocking, and a returned peer whose write has not yet reached shared RAM. -/
theorem preparation_observed :
    prepared.2 =
      [.physical (.machine (.retired 2 none)), .physical (.machine (.retired 2 none)),
       .physical (.machine (.retired 2 none)), .physical (.machine (.retired 1 none)),
       .physical (.machine (.retired 1 none)), .physical (.machine (.retired 1 none)),
       .physical (.machine (.blocked 1)),
       .physical (.machine (.drained 1 ⟨262144, 0x11223344⟩))] ∧
    loadDWord prepared.1.suspended.machine.memory 65536 = .ok 0 ∧
    loadDWord prepared.1.suspended.machine.memory 262144 = .ok 0x11223344 ∧
    loadDWord prepared.1.suspended.machine.memory 131072 = .ok 0 ∧
    (prepared.1.suspended.machine.workers[2]?).map TSO.Worker.returned = some true ∧
    (prepared.1.suspended.machine.workers[2]?).map TSO.Worker.buffer =
      some [⟨131072, 0x55667788⟩] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Admission is exercised against actual memory/resource enforcement:
the last loop bytes and all eight return bytes remain frozen, while W is
pinned by a keeper instead of being frozen by an ordinary read loan. -/
theorem genuine_resource_enforcement :
    Atomics.mutate initial.authority (.store 7 ⟨3, 0⟩ 4122 0) =
      .error (.authority .borrowed) ∧
    Atomics.mutate initial.authority (.store64 7 ⟨6, 0⟩ 32768 0) =
      .error (.authority .borrowed) ∧
    Atomics.mutate initial.authority (.release 7 ⟨0, 0⟩) = .error .reserved ∧
    Atomics.readBorrow initial.authority 7 ⟨0, 0⟩ 9 ⟨65536, 4⟩ = .error .reserved := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact Resources.keeper_blocks_mutation _ registration _
      initial_admitted.runtime.service.authority initial_admitted.keeper rfl
  · exact Resources.keeper_blocks_readLoan _ registration _ _ _
      initial_admitted.runtime.service.authority initial_admitted.keeper

/-- Six actual decoded instructions capture the real continuation at19,
an initial invocation0 and fresh pin2. Parked selection cannot run RET. -/
theorem first_entry_observed :
    entered.2 =
      [.physical (.machine (.retired 0 none)), .physical (.machine (.retired 0 none)),
       .physical (.machine (.retired 0 none)), .physical (.machine (.retired 0 none)),
       .physical (.machine (.retired 0 none)), .physical (.entered 0 0)] ∧
    entered.1.calls 0 = some ⟨0, .wait 0, 2, .entered⟩ ∧
    capturedWord entered.1 0 = some (.ok 0) ∧
    (entered.1.suspended.pending 0).map (fun saved => saved.request.continuation) = some 4115 ∧
    Suspend.issue queued.1.suspended 0 = .ok (queued.1.suspended, .parked 0 0) ∧
    queued.1.queue = [0] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A service-derived zero leaves the program at MOV1, unreturned and W0.
The fresh CMP clears an adversarial ZF1, and JNZ returns to the actual LOAD.
This rejects the former behavior where zero could directly reach RET. -/
theorem spurious_zero_must_recheck :
    readyRaw spurious.1 0 = some 0 ∧
    returnView spuriousResumed.1 = some
      (false, 0, 4115, 32768, 0x11223344556677c0,
        0x8877665544332211, 0xfedcba9876543210) ∧
    decoded spuriousResumed.1 = some (.ok (.mov32 .rax 1)) ∧
    zeroFlag spuriousResumed.1 = some true ∧
    registerAt spuriousMoved.1 .rax = some 1 ∧
    decoded spuriousMoved.1 = some (.ok .cmpEaxZero) ∧
    zeroFlag spuriousCompared.1 = some false ∧
    decoded spuriousCompared.1 = some (.ok (.jnz 0xe3)) ∧
    decoded spuriousBackedge.1 = some (.ok .loadEaxRdi) ∧
    (spuriousBackedge.1.suspended.machine.workers[0]?).map (fun worker => worker.context.rip) =
      some 4096 ∧
    (spuriousBackedge.1.suspended.machine.workers[0]?).map TSO.Worker.returned = some false ∧
    loadDWord spuriousBackedge.1.suspended.machine.memory 65536 = .ok 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The raw suspension path and the checked physical path execute the same
MOV, not an independently fabricated fixture transition. -/
theorem raw_retry_instruction_agrees :
    Suspend.issue spuriousResumed.1.suspended 0 =
      .ok (spuriousMoved.1.suspended, .machine (.retired 0 none)) ∧
    spuriousMoved.2 = .machine (.retired 0 none) ∧
    Physical.issue profile spuriousResumed.1 0 = .ok spuriousMoved := by
  exact ⟨rfl, rfl, checked_ok _ _⟩

/-- Re-entry executes the new LOAD and an entire fresh syscall. Captured
identities and pins advance monotonically; consumed records never revive.
The second call preserves the actual clobbered private context, not entry's. -/
theorem repeated_call_is_fresh :
    spuriousReentered.1.calls 0 = none ∧
    spuriousReentered.1.calls 1 = some ⟨0, .wait 0, 3, .entered⟩ ∧
    spuriousReentered.1.suspended.nextCall = 2 ∧
    spuriousReentered.1.authority.nextHandle = 4 ∧
    capturedIdentity spuriousReentered.1 = some
      (1, 0, 4115, 0x1122334455667744, 0x8877665544332211, 0xfedcba9876543210) ∧
    capturedWord spuriousReentered.1 0 = some (.ok 0) ∧
    Atomics.authorize spuriousReentered.1.authority 90 2 = .error .missingHandle ∧
    Atomics.authorize spuriousReentered.1.authority 90 3 =
      .ok (registration.callHandle 90) ∧
    resumeReady profile.service spuriousReentered.1 0 0 0 0 = .error .missingCall ∧
    Suspend.resume spuriousReentered.1.suspended 0 0 0 0 0 0 = .error .staleCall ∧
    spuriousRequeued.1.queue = [1] ∧
    spuriousRequeued.1.calls 1 = some ⟨0, .wait 0, 3, .queued⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Historical request RAM can remain W0 after actual publicationW1. Both
initial and retried service comparisons use current pinned RAM, including
the complete 64-bit negative EAGAIN result. -/
theorem current_ram_comparison_observed :
    betweenExchange.2 = .machine (.retired 1 (some ⟨65536, 0, 1⟩)) ∧
    capturedWord betweenCompared.1 0 = some (.ok 0) ∧
    loadDWord betweenCompared.1.suspended.machine.memory 65536 = .ok 1 ∧
    readyRaw betweenCompared.1 0 = some 0xfffffffffffffff5 ∧
    betweenCompared.1.queue = [] ∧
    registerAt betweenResumed.1 .rax = some 0xfffffffffffffff5 ∧
    capturedWord currentRecheck.1 0 = some (.ok 0) ∧
    currentRecheck.1.calls 0 = some ⟨0, .wait 0, 2, .ready .waitAgain .mismatch⟩ ∧
    currentRecheck.1.suspended.nextCall = 1 ∧ currentRecheck.1.authority.nextHandle = 3 ∧
    currentRecheck.1.queue = [] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An actual publisher wake selects the queued invocation, yields zero to
WAIT and one to WAKE. Even with W1, zero resumes at19 then reaches a fresh
LOAD at0; the following loaded/tested value, not raw zero, enables RET29. -/
theorem selected_zero_must_load :
    selected.1.calls 0 = some ⟨0, .wait 0, 2, .ready .waitZero (.wake 1)⟩ ∧
    readyRaw selected.1 1 = some 1 ∧ selected.1.queue = [] ∧
    registerAt selectedResumed.1 .rax = some 0 ∧
    zeroFlag selectedResumed.1 = some true ∧
    (selectedResumed.1.suspended.machine.workers[0]?).map TSO.Worker.returned = some false ∧
    decoded selectedBackedge.1 = some (.ok .loadEaxRdi) ∧
    zeroFlag selectedBackedge.1 = some false ∧
    loadDWord selectedBackedge.1.suspended.machine.memory 65536 = .ok 1 ∧
    selectedReturned.2 = List.replicate 4 (.physical (.machine (.retired 0 none))) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- All stale snapshot stages are retained. Publication plus an empty actual
WAKE leaves the later captured call to compare against W1 and get EAGAIN;
the saved request's RAM is already W1 even though the earlier LOAD saw0. -/
theorem stale_cuts_observed :
    capturedWord staleLoaded.1 0 = some (.ok 1) ∧
    staleLoaded.1.calls 0 = some ⟨1, .wakeOne, 2, .ready .wakeZero .emptyWake⟩ ∧
    staleLoaded.1.calls 1 = some ⟨0, .wait 0, 3, .ready .waitAgain .mismatch⟩ ∧
    readyRaw staleCompared.1 1 = some 0xfffffffffffffff5 ∧
    readyRaw staleBranched.1 1 = some 0xfffffffffffffff5 ∧
    readyRaw staleNumbered.1 1 = some 0xfffffffffffffff5 ∧
    loadDWord staleNumbered.1.suspended.machine.memory 65536 = .ok 1 ∧
    staleNumbered.1.queue = [] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The stale machine cuts themselves exist after the real notification:
RAM is W1 while the earlier loaded/tested value remains0. Current control
must retain these compare0/branch0/number cuts instead of erasing them. -/
theorem notified_stale_load_observed :
    registerAt notifiedAfterLoad.1 .rax = some 0 ∧
    decoded notifiedAfterLoad.1 = some (.ok .cmpEaxZero) ∧
    loadDWord notifiedAfterLoad.1.suspended.machine.memory 65536 = .ok 1 ∧
    notifiedAfterLoad.1.suspended.pending 0 = none ∧
    readyRaw notifiedAfterLoad.1 0 = some 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem notified_stale_compare_branch_observed :
    registerAt notifiedAfterCompare.1 .rax = some 0 ∧
    zeroFlag notifiedAfterCompare.1 = some true ∧
    decoded notifiedAfterCompare.1 = some (.ok (.jnz 0x16)) ∧
    decoded notifiedAfterBranch.1 = some (.ok (.mov32 .rax 202)) ∧
    registerAt notifiedAfterBranch.1 .rax = some 0 ∧
    loadDWord notifiedAfterBranch.1.suspended.machine.memory 65536 = .ok 1 ∧
    decoded notifiedAfterNumber.1 = some (.ok (.mov32 .rsi 128)) ∧
    registerAt notifiedAfterNumber.1 .rax = some 202 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A first LOAD after actual publication takes the nonzero branch without
capturing a WAIT or consuming a WAIT pin. The only live call is the real
publisher's empty WAKE. Its raw result is not the loop's return value. -/
theorem late_nonzero_load_observed :
    lateReturned.1.calls 0 = some ⟨1, .wakeOne, 2, .ready .wakeZero .emptyWake⟩ ∧
    lateReturned.1.calls 1 = none ∧ lateReturned.1.suspended.pending 0 = none ∧
    lateReturned.1.suspended.nextCall = 1 ∧ lateReturned.1.authority.nextHandle = 3 ∧
    registerAt lateReturned.1 .rax = some 1 ∧
    registerAt lateReturned.1 .rsi = some 0xdeadbeefabcdef01 ∧
    (lateReturned.1.suspended.machine.workers[0]?).map TSO.Worker.returned = some true ∧
    loadDWord lateReturned.1.suspended.machine.memory 65536 = .ok 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- After a genuine second capture, the associated publisher wake selects
call1/pin3; it cannot select consumed call0 or reuse revoked pin2. -/
theorem repeated_wake_observed :
    repeatedWoken.1.calls 0 = none ∧
    repeatedWoken.1.calls 1 = some ⟨0, .wait 0, 3, .ready .waitZero (.wake 2)⟩ ∧
    repeatedWoken.1.calls 2 = some ⟨1, .wakeOne, 4, .ready .wakeOne (.wake 2)⟩ ∧
    repeatedReturned.1.suspended.pending 0 = none ∧
    repeatedReturned.1.calls 1 = none ∧
    Atomics.authorize repeatedReturned.1.authority 90 2 = .error .missingHandle ∧
    Atomics.authorize repeatedReturned.1.authority 90 3 = .error .missingHandle ∧
    repeatedReturned.1.authority.nextHandle = 5 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The independent final contract observes RAX1/currentW1, actual RET and
stack pop, pending consumption and stable GPRs in four distinct executions.
It does not assume any intermediate or final Admitted proposition. -/
theorem final_returns (state : Futex.State)
    (member : state ∈ [selectedReturned.1, betweenReturned.1, staleReturned.1, repeatedReturned.1]) :
    ∃ actual, Predicate.Returns waiter 65536 state.suspended 0 actual := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    refine ⟨_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, Or.inr rfl⟩⟩
    intro register rax rsi rcx r11 rsp
    cases register <;> first
      | exact (rax rfl).elim
      | exact (rsi rfl).elim
      | exact (rcx rfl).elim
      | exact (r11 rfl).elim
      | exact (rsp rfl).elim
      | rfl

theorem late_return_contract :
    ∃ actual, Predicate.Returns waiter 65536 lateReturned.1.suspended 0 actual := by
  refine ⟨_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, Or.inl rfl⟩⟩
  intro register rax rsi rcx r11 rsp
  cases register <;> first
    | exact (rax rfl).elim
    | exact (rsi rfl).elim
    | exact (rcx rfl).elim
    | exact (r11 rfl).elim
    | exact (rsp rfl).elim
    | rfl

/-- Private high bits survive resumption; the actual CMPs determine final
flags. Peer context, its nonempty FIFO, both payloads and all original return
words remain intact until the peer's explicit drain. -/
theorem selected_return_observed :
    returnView selectedReturned.1 = some
      (true, 1, 0x6000, 32776, 0x1122334455667700,
        0x8877665544332211, 0xfedcba9876543210) := by
  rfl

theorem returned_peer_frame_observed :
    (selectedReturned.1.suspended.machine.workers[2]?).map TSO.Worker.buffer =
      some [⟨131072, 0x55667788⟩] ∧
    (selectedReturned.1.suspended.machine.workers[2]?).map (fun worker => worker.context.rip) = some 0x6200 ∧
    (selectedReturned.1.suspended.machine.workers[2]?).map (fun worker => worker.context.registers .rsp) = some 32840 := by
  exact ⟨rfl, rfl, rfl⟩

theorem payload_and_return_words_observed :
    loadDWord selectedReturned.1.suspended.machine.memory 262144 = .ok 0x11223344 ∧
    loadDWord selectedReturned.1.suspended.machine.memory 131072 = .ok 0 ∧
    readWord selectedReturned.1.suspended.machine.memory 32768 = .ok 0x6000 ∧
    readWord selectedReturned.1.suspended.machine.memory 32800 = .ok 0x6100 ∧
    readWord selectedReturned.1.suspended.machine.memory 32832 = .ok 0x6200 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem returned_peer_drain_observed :
    peerDrained.2 = [.physical (.machine (.drained 2 ⟨131072, 0x55667788⟩))] ∧
    loadDWord peerDrained.1.suspended.machine.memory 131072 = .ok 0x55667788 := by
  exact ⟨rfl, rfl⟩

theorem peer_drain_data_frame :
    loadDWord peerDrained.1.suspended.machine.memory 262144 = .ok 0x11223344 ∧
    loadDWord peerDrained.1.suspended.machine.memory 65536 = .ok 1 := by
  exact ⟨rfl, rfl⟩

theorem peer_drain_worker_frame :
    peerDrained.1.suspended.machine.workers[0]? = publisherReturned.1.suspended.machine.workers[0]? := by
  exact Suspend.drain_peer (identifier := 2) (result :=
    (peerDrained.1.suspended, .machine (.drained 2 ⟨131072, 0x55667788⟩))) (by decide) (by rfl)

theorem peer_drain_owner_remains_returned :
    (peerDrained.1.suspended.machine.workers[2]?).map TSO.Worker.returned = some true ∧
    (peerDrained.1.suspended.machine.workers[2]?).map TSO.Worker.buffer = some [] := by
  exact ⟨rfl, rfl⟩

def repeatedActions : List Runtime.Action :=
  prepare ++ waiterEntry ++ [.service (.compare 0), .service (.spurious 0), resume 0] ++
    retry ++ waiterEntry ++ [.service (.compare 1), .issue 1] ++ publisherEntry ++
    [.service (.wake 2 (some 1))] ++ finish 1

private theorem repeated_schedule :
    ∃ observations, Runtime.schedule profile initial repeatedActions =
      .ok (repeatedReturned.1, observations) := by
  let result := checked (Runtime.schedule profile initial repeatedActions) (by rfl)
  exact ⟨result.2, checked_ok (Runtime.schedule profile initial repeatedActions) (by rfl)⟩

/-- Instantiation of generic resource/history preservation for an actual
two-call execution. This proves the full current resource RAM coupling,
every exact code/stack frame, original floor and fixed handles; no later
cyclic-control admission is a premise. -/
theorem repeated_resources :
    Runtime.Invariant profile repeatedReturned.1 ∧
    Predicate.Protected cohort repeatedReturned.1 ∧
    Clients.PinDiscipline cohort.pinFloor repeatedReturned.1 ∧
    (∀ identifier handle, (identifier, handle) ∈ cohort.fixedHandles →
      repeatedReturned.1.authority.handles identifier = some handle) := by
  obtain ⟨observations, scheduled⟩ := repeated_schedule
  exact schedule_resources (result := (repeatedReturned.1, observations)) scheduled

theorem returned_loop_has_no_service_record (identifier : Nat) (call : Call)
    (found : repeatedReturned.1.calls identifier = some call) : call.worker ≠ 0 := by
  obtain ⟨actual, returned⟩ := final_returns repeatedReturned.1 (by simp)
  exact returned.no_call repeated_resources.1 found

/-- Consuming invocation pins does not unpin the fixed keeper or producer.
The mutable word is still protected against release after both real returns. -/
theorem fixed_handles_survive_returns :
    Atomics.authorize peerDrained.1.authority 90 0 = .ok registration.handle ∧
    Atomics.authorize peerDrained.1.authority 11 1 = .ok (registration.callHandle 11) ∧
    Atomics.authorize peerDrained.1.authority 90 2 = .error .missingHandle ∧
    Atomics.authorize peerDrained.1.authority 90 3 = .error .missingHandle ∧
    Atomics.mutate peerDrained.1.authority (.release 7 ⟨0, 0⟩) = .error .reserved := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! These are applications of root's universal preservation theorem to
actual schedules. Admission at every later cut is a conclusion. -/

theorem prepared_admitted : Predicate.Admitted cohort prepared.1 :=
  initial_admitted.schedule (result := prepared) (checked_ok _ _)

theorem entered_admitted : Predicate.Admitted cohort entered.1 :=
  prepared_admitted.schedule (result := entered) (checked_ok _ _)

theorem queued_admitted : Predicate.Admitted cohort queued.1 :=
  entered_admitted.schedule (result := queued) (checked_ok _ _)

theorem queued_exchange_admitted : Predicate.Admitted cohort queuedExchange.1 :=
  Predicate.admitted_step queued_admitted
    (show Runtime.step profile queued.1 (.issue 1) =
      .ok (queuedExchange.1, .physical queuedExchange.2) from rfl)

theorem selected_admitted : Predicate.Admitted cohort selected.1 :=
  (queued_exchange_admitted.schedule (result := queuedWaking) (checked_ok _ _)).schedule
    (result := selected) (checked_ok _ _)

theorem publisher_returned_admitted : Predicate.Admitted cohort publisherReturned.1 := by
  have resumed := selected_admitted.schedule (result := selectedResumed) (checked_ok _ _)
  have back := resumed.schedule (result := selectedBackedge) (checked_ok _ _)
  have returned := back.schedule (result := selectedReturned) (checked_ok _ _)
  exact returned.schedule (result := publisherReturned) (checked_ok _ _)

theorem spurious_resumed_admitted : Predicate.Admitted cohort spuriousResumed.1 :=
  (queued_admitted.schedule (result := spurious) (checked_ok _ _)).schedule
    (result := spuriousResumed) (checked_ok _ _)

theorem repeated_admitted : Predicate.Admitted cohort repeatedReturned.1 := by
  obtain ⟨observations, scheduled⟩ := repeated_schedule
  exact initial_admitted.schedule (result := (repeatedReturned.1, observations)) scheduled

theorem stale_cuts_admitted :
    Predicate.Admitted cohort staleLoaded.1 ∧ Predicate.Admitted cohort staleCompared.1 ∧
    Predicate.Admitted cohort staleBranched.1 ∧ Predicate.Admitted cohort staleNumbered.1 := by
  exact ⟨prepared_admitted.schedule (result := staleLoaded) (checked_ok _ _),
    prepared_admitted.schedule (result := staleCompared) (checked_ok _ _),
    prepared_admitted.schedule (result := staleBranched) (checked_ok _ _),
    prepared_admitted.schedule (result := staleNumbered) (checked_ok _ _)⟩

theorem notified_stale_cuts_admitted :
    Predicate.Admitted cohort notifiedAfterLoad.1 ∧
    Predicate.Admitted cohort notifiedAfterCompare.1 ∧
    Predicate.Admitted cohort notifiedAfterBranch.1 ∧
    Predicate.Admitted cohort notifiedAfterNumber.1 := by
  exact ⟨prepared_admitted.schedule (result := notifiedAfterLoad) (checked_ok _ _),
    prepared_admitted.schedule (result := notifiedAfterCompare) (checked_ok _ _),
    prepared_admitted.schedule (result := notifiedAfterBranch) (checked_ok _ _),
    prepared_admitted.schedule (result := notifiedAfterNumber) (checked_ok _ _)⟩

/-- Genuine admission supplies a positive managed lift for the actual raw
MOV after spurious zero. A future successful managed issue is not a premise. -/
theorem raw_retry_has_managed_lift :
    ∃ after, Physical.issue profile spuriousResumed.1 0 =
      .ok (after, .machine (.retired 0 none)) ∧
      after.suspended = spuriousMoved.1.suspended ∧ Predicate.Admitted cohort after :=
  Predicate.issue_lift spurious_resumed_admitted raw_retry_instruction_agrees.1

/-- The actual XCHG is bound to the same legacy publisher and its drained
payload by the generic decoded-effect theorem. No wake or payload promise
is inserted as an admission field. -/
theorem publisher_exchange_has_published_payload :
    loadDWord queuedExchange.1.suspended.machine.memory 262144 = .ok 0x11223344 ∧
    loadDWord queuedExchange.1.suspended.machine.memory 65536 = .ok 1 := by
  have exchanged : Physical.issue profile queued.1 1 =
      .ok (queuedExchange.1, .machine (.retired 1 (some ⟨65536, 0, 1⟩))) := rfl
  obtain ⟨client, member, _, _, _, _, payload, word⟩ :=
    Predicate.physical_publisher_exchange_publishes_payload queued_admitted exchanged
  have same : client = publisher := by simpa [cohort, clients] using member.symm
  subst client
  exact ⟨payload, word⟩

/-- A returned peer's raw nonempty-FIFO drain has a positive managed lift
with the exact suspended output and observation, preserving real admission. -/
theorem returned_peer_has_managed_drain_lift :
    ∃ after, Physical.drain profile publisherReturned.1 2 =
      .ok (after, .machine (.drained 2 ⟨131072, 0x55667788⟩)) ∧
      after.suspended = peerDrained.1.suspended ∧ Predicate.Admitted cohort after :=
  Predicate.drain_lift publisher_returned_admitted
    (show Suspend.drain publisherReturned.1.suspended 2 =
      .ok (peerDrained.1.suspended, .machine (.drained 2 ⟨131072, 0x55667788⟩)) from rfl)

/-- The independently observed final contract also follows generically
from the derived cyclic control, not a separately assumed final control. -/
theorem repeated_contract_from_admission :
    ∃ actual, Predicate.Returns waiter 65536 repeatedReturned.1.suspended 0 actual := by
  let actual := (repeatedReturned.1.suspended.machine.workers[0]?).get (by rfl)
  exact ⟨actual, repeated_admitted.returned_sound rfl (by rfl) (by rfl)⟩

private theorem empty_queue_no_wait {state : Futex.State}
    (admitted : Predicate.Admitted cohort state) (empty : state.queue = []) :
    Futex.Notification.NoQueuedWait state 0 := by
  intro identifier call found _ queued
  have eligible := (admitted.runtime.service.eligible identifier).mpr ⟨call, found, queued⟩
  simp [empty] at eligible

/-- Generic constructive completion is instantiated at the worst stale
LOAD0 cut after actual publication and WAKE. Its witness includes the real
finite trace, independent Returns, admission, full RAM and peer frame. -/
theorem notified_load_completion (flags rcx r11 : Word) :
    ∃ after, CompletesWithin 14 cohort 0 waiter notifiedAfterLoad.1 after := by
  have admitted := notified_stale_cuts_admitted.1
  exact Predicate.constructive_completion_with admitted rfl rfl
    (empty_queue_no_wait admitted rfl) flags rcx r11

theorem notified_compare_completion (flags rcx r11 : Word) :
    ∃ after, CompletesWithin 14 cohort 0 waiter notifiedAfterCompare.1 after := by
  have admitted := notified_stale_cuts_admitted.2.1
  exact Predicate.constructive_completion_with admitted rfl rfl
    (empty_queue_no_wait admitted rfl) flags rcx r11

theorem notified_branch_completion (flags rcx r11 : Word) :
    ∃ after, CompletesWithin 14 cohort 0 waiter notifiedAfterBranch.1 after := by
  have admitted := notified_stale_cuts_admitted.2.2.1
  exact Predicate.constructive_completion_with admitted rfl rfl
    (empty_queue_no_wait admitted rfl) flags rcx r11

theorem notified_number_completion (flags rcx r11 : Word) :
    ∃ after, CompletesWithin 14 cohort 0 waiter notifiedAfterNumber.1 after := by
  have admitted := notified_stale_cuts_admitted.2.2.2
  exact Predicate.constructive_completion_with admitted rfl rfl
    (empty_queue_no_wait admitted rfl) flags rcx r11

theorem selected_completion (flags rcx r11 : Word) :
    ∃ after, CompletesWithin 14 cohort 0 waiter selected.1 after :=
  Predicate.constructive_completion_with selected_admitted rfl rfl
    (empty_queue_no_wait selected_admitted rfl) flags rcx r11

theorem mismatch_completion (flags rcx r11 : Word) :
    ∃ after, CompletesWithin 14 cohort 0 waiter staleLoaded.1 after := by
  have admitted := stale_cuts_admitted.1
  exact Predicate.constructive_completion_with admitted rfl rfl
    (empty_queue_no_wait admitted rfl) flags rcx r11

/-- This cut retains its historical flags/RCX/R11, regardless of the tuple
given to the generic suffix constructor. It is already past service resume. -/
theorem already_resumed_completion (flags rcx r11 : Word) :
    ∃ after, CompletesWithin 14 cohort 0 waiter selectedResumed.1 after := by
  have admitted := selected_admitted.schedule (result := selectedResumed) (checked_ok _ _)
  exact Predicate.constructive_completion_with admitted rfl rfl
    (empty_queue_no_wait admitted rfl) flags rcx r11

theorem already_returned_empty_completion :
    CompletesWithin 0 cohort 0 waiter repeatedReturned.1 repeatedReturned.1 := by
  let actual := (repeatedReturned.1.suspended.machine.workers[0]?).get (by rfl)
  exact Predicate.returned_completion (actual := actual) repeated_admitted rfl (by rfl) (by rfl)

def NotifiedSuffixes (state : Futex.State) : Prop :=
  ∀ {actions observations after}, Runtime.Trace profile state actions observations after →
    Futex.Notification.NoQueuedWait after 0 ∧
    loadDWord after.suspended.machine.memory 65536 = .ok 1 ∧
    loadDWord after.suspended.machine.memory 262144 = .ok 0x11223344 ∧
    Predicate.Admitted cohort after

/-- The same actual publisher retires XCHG, captures the actual WAKE and
selects the actual queued WAIT. Every later accepted mixed trace retains
notification, payload publication and admission, without fairness. -/
theorem selected_all_suffixes : NotifiedSuffixes selected.1 := by
  intro actions observations after later
  have exchange : Physical.issue profile queued.1 1 =
      .ok (queuedExchange.1, .machine (.retired 1 (some ⟨65536, 0, 1⟩))) := rfl
  have between := Runtime.schedule_trace profile queuedExchange.1 publisherEntry queuedWaking (checked_ok _ _)
  have associated : queuedWaking.1.calls 1 = some ⟨1, .wakeOne, 3, .entered⟩ := rfl
  have wake : wakeOne queuedWaking.1 1 (some 0) = .ok selected.1 := rfl
  obtain ⟨⟨client, _, member, _, _, _, _, payload⟩, clear, word, admitted⟩ :=
    Predicate.Notification.exchange_wake_trace queued_admitted exchange between associated wake later
  have same : client = publisher := by simpa [cohort, clients] using member.symm
  subst client
  exact ⟨clear, word, payload, admitted⟩

/-- Actual notification can occur after LOAD0 but before its CMP. The
publisher's empty wake is associated with that same actual XCHG; the stale
snapshot remains admitted, and every accepted later mixed trace is safe. -/
theorem stale_load_all_suffixes : NotifiedSuffixes notifiedAfterLoad.1 := by
  intro actions observations after later
  have admitted := prepared_admitted.schedule (result := loadedBeforeNotification) (checked_ok _ _)
  have exchange : Physical.issue profile loadedBeforeNotification.1 1 =
      .ok (staleExchange.1, .machine (.retired 1 (some ⟨65536, 0, 1⟩))) := rfl
  have between := Runtime.schedule_trace profile staleExchange.1 publisherEntry staleWaking (checked_ok _ _)
  have associated : staleWaking.1.calls 0 = some ⟨1, .wakeOne, 2, .entered⟩ := rfl
  have wake : wakeOne staleWaking.1 0 none = .ok notifiedAfterLoad.1 := rfl
  obtain ⟨⟨client, _, member, _, _, _, _, payload⟩, clear, word, valid⟩ :=
    Predicate.Notification.exchange_wake_trace admitted exchange between associated wake later
  have same : client = publisher := by simpa [cohort, clients] using member.symm
  subst client
  exact ⟨clear, word, payload, valid⟩

/-- The strengthened root constructor also proves that its worst-case
suffix selects only this loop's issues and its current typed WAIT service. -/
theorem notified_load_selected_completion (flags rcx r11 : Word) :
    ∃ after, SelectedCompletesWithin 14 cohort 0 waiter notifiedAfterLoad.1 after := by
  have admitted := notified_stale_cuts_admitted.1
  exact Predicate.constructive_completion_selected_with admitted rfl rfl
    (empty_queue_no_wait admitted rfl) flags rcx r11

end EDSL.Tests.FutexPredicate

#audit_edsl
