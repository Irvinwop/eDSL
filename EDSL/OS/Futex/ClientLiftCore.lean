/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.LoanFrames
import EDSL.OS.Futex.Stubs

namespace EDSL.OS.Futex.Clients.LiftCore
open X86 AddressSpace

/-- The canonical request at a current physical instruction. Its entire RAM
is the current shared RAM; no historical memory is substituted. -/
def entryRequest (state : Suspend.State) (worker : TSO.Worker) : SyscallRequest :=
  let user := TSO.sharedState state.machine worker
  ⟨user, user.rip + 2⟩

theorem issue_slots {before after : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (actual : Suspend.issue before worker = .ok (after, observation)) :
    after.machine.workers.length = before.machine.workers.length := by
  cases Suspend.issue_effect _ _ _ actual with
  | entered live running free decoded empty executed stepped user continuation => rfl
  | parked live running pending => rfl
  | machine free issued =>
    obtain ⟨selected, instruction, live, running, decoded, executed, effect⟩ := TSO.issue_effect _ _ _ issued
    cases effect <;> simp [TSO.install]

theorem drain_slots {before after : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (actual : Suspend.drain before worker = .ok (after, observation)) :
    after.machine.workers.length = before.machine.workers.length := by
  obtain ⟨machine, observed, drained, same⟩ := Suspend.drain_ok _ _ _ actual
  obtain ⟨selected, head, tail, memory, live, buffer, committed, installed⟩ := TSO.drain_ok _ _ _ drained
  have afterEq := congrArg Prod.fst same
  have machineEq := congrArg Prod.fst installed
  dsimp only at afterEq machineEq
  rw [afterEq, machineEq]
  simp [TSO.install]

theorem resume_slots {before after : Suspend.State} {worker invocation : Nat} {raw flags rcx r11 : Word}
    (actual : Suspend.resume before worker invocation raw flags rcx r11 = .ok after) :
    after.machine.workers.length = before.machine.workers.length := by
  obtain ⟨selected, saved, live, running, pending, current, owner, empty, same⟩ :=
    Suspend.resume_ok _ _ _ _ _ _ _ _ actual
  rw [same]
  simp [TSO.install]

/-- The actual scheduler never inserts or removes a physical worker slot. -/
theorem suspend_step_slots {before after : Suspend.State} {action : Suspend.Action}
    {observation : Suspend.Observation}
    (actual : Suspend.step before action = .ok (after, observation)) :
    after.machine.workers.length = before.machine.workers.length := by
  cases action with
  | issue worker => exact issue_slots actual
  | drain worker => exact drain_slots actual
  | resume worker invocation raw flags rcx r11 =>
    cases resumed : Suspend.resume before worker invocation raw flags rcx r11 with
    | error fault => simp [Suspend.step, resumed] at actual
    | ok suspended =>
      simp [Suspend.step, resumed] at actual
      obtain ⟨rfl, rfl⟩ := actual
      exact resume_slots resumed
  | idle => cases Except.ok.inj actual; rfl

/-- Current keeper, target and full ABI support at every running, unparked
SYSCALL. This predicate contains no future service/replay computation and no
preservation callback. Instruction selection remains the actual decoder's. -/
def EntrySupport (profile : Physical.Profile) (state : Futex.State) : Prop :=
  ∃ registration, state.registration = some registration ∧
    Resources.Valid state.authority registration ∧
    targetSupported profile.service state.authority registration.address = true ∧
    ∀ worker selected,
    state.suspended.machine.workers[worker]? = some selected →
    selected.returned = false → state.suspended.pending worker = none →
    decodeAt (TSO.sharedState state.suspended.machine selected) = .ok .syscall →
    ∃ operation, classify (entryRequest state.suspended selected) = .ok operation ∧
      (entryRequest state.suspended selected).user.registers .rdi = registration.address

/-- The actual allocator and current service invariant exclude an old call
at the new invocation. This also covers other workers with pending calls. -/
theorem fresh_call_absent {profile : Physical.Profile} {state : Futex.State}
    (valid : Runtime.Invariant profile state) :
    state.calls state.suspended.nextCall = none := by
  cases found : state.calls state.suspended.nextCall with
  | none => rfl
  | some call => exact (Nat.lt_irrefl _ (valid.service.allocated found)).elim

/-- Capture is enabled by the real fresh Saved record. Retaining its fresh
pin is derived from the current keeper and resource well-formedness. -/
theorem capture_enabled {profile : Physical.Profile} {state : Futex.State}
    {suspended : Suspend.State} {worker invocation : Nat}
    (valid : Runtime.Invariant profile state) (support : EntrySupport profile state)
    (actual : Suspend.issue state.suspended worker = .ok (suspended, .entered worker invocation)) :
    ∃ after, captureEntered profile.service { state with suspended := suspended }
      worker invocation = .ok after ∧ after.suspended = suspended := by
  obtain ⟨fresh, selected, request, live, running, free, empty, decoded, stepped,
    user, requestMemory, context, continuation, suspendedEq, machine, frontier, pending⟩ :=
    Suspend.issue_entered_effect actual
  obtain ⟨registration, registered, keeper, target, abi⟩ := support
  obtain ⟨operation, classified, address⟩ := abi worker selected live running free decoded
  have requestEq : request = entryRequest state.suspended selected :=
    Suspend.request_eq_entry user continuation
  have absent : state.calls invocation = none := by
    rw [fresh]
    exact fresh_call_absent valid
  have captured := captureEntered_enabled profile.service { state with suspended := suspended }
    worker invocation ⟨invocation, worker, request⟩ operation registration pending rfl rfl
    absent (requestEq ▸ classified) registered (requestEq ▸ address)
    target valid.service.authority keeper
  exact ⟨_, captured, rfl⟩

/-- Every actual issue with present resource rights and current entry support
has an enabled physical lift, preserving its exact suspended output and
observation. Resource replay and capture success are conclusions. -/
theorem issue_enabled {profile : Physical.Profile} {state : Futex.State}
    {suspended : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (valid : Runtime.Invariant profile state) (support : EntrySupport profile state)
    (ready : Physical.Ready profile state.authority observation)
    (actual : Suspend.issue state.suspended worker = .ok (suspended, observation)) :
    ∃ after, Physical.issue profile state worker = .ok (after, observation) ∧
      after.suspended = suspended ∧ Runtime.Invariant profile after ∧
      Atomics.History state.authority after.authority := by
  obtain ⟨authority, synced, memory, history, wellFormed⟩ :=
    Physical.synchronize_enabled profile state.authority _ _ observation valid.service.authority
      valid.memory ready (Physical.issue_effect actual)
  have enabled : ∃ after, Physical.issue profile state worker = .ok (after, observation) ∧
      after.suspended = suspended := by
    cases observation with
    | entered selected invocation =>
      have sameWorker : selected = worker := by
        cases Suspend.issue_effect _ _ _ actual
        rfl
      subst selected
      obtain ⟨after, captured, exactSuspended⟩ := capture_enabled valid support actual
      exact ⟨after, by simp [Physical.issue, actual, Physical.synchronize, captured, Except.mapError],
        exactSuspended⟩
    | machine observed =>
      exact ⟨{ state with suspended := suspended, authority := authority },
        by simp [Physical.issue, actual, synced, Except.mapError], rfl⟩
    | parked selected invocation | resumed selected invocation raw | idle =>
      exact ⟨{ state with suspended := suspended, authority := authority },
        by simp [Physical.issue, actual, synced, Except.mapError], rfl⟩
  obtain ⟨after, issued, exactSuspended⟩ := enabled
  have runtime : Runtime.step profile state (.issue worker) =
      .ok (after, .physical observation) := by simp [Runtime.step, issued]
  obtain ⟨invariant, resources⟩ := Runtime.step_invariant valid runtime
  exact ⟨after, issued, exactSuspended, invariant, resources⟩

/-- Draining needs the grant for the actual FIFO head, including a returned
producer's head. It does not require the other FIFOs or pending calls empty. -/
theorem drain_enabled {profile : Physical.Profile} {state : Futex.State}
    {suspended : Suspend.State} {worker : Nat} {observation : Suspend.Observation}
    (valid : Runtime.Invariant profile state)
    (ready : Physical.Ready profile state.authority observation)
    (actual : Suspend.drain state.suspended worker = .ok (suspended, observation)) :
    ∃ after, Physical.drain profile state worker = .ok (after, observation) ∧
      after.suspended = suspended ∧ Runtime.Invariant profile after ∧
      Atomics.History state.authority after.authority := by
  obtain ⟨authority, synced, memory, history, wellFormed⟩ :=
    Physical.synchronize_enabled profile state.authority _ _ observation valid.service.authority
      valid.memory ready (Physical.drain_effect actual)
  let after : Futex.State := { state with suspended := suspended, authority := authority }
  have drained : Physical.drain profile state worker = .ok (after, observation) := by
    simp [Physical.drain, actual, synced, Except.mapError, after]
  have runtime : Runtime.step profile state (.drain worker) =
      .ok (after, .physical observation) := by simp [Runtime.step, drained]
  obtain ⟨invariant, resources⟩ := Runtime.step_invariant valid runtime
  exact ⟨after, drained, rfl, invariant, resources⟩

/-- Service demand is a current phase and queue choice. Typed outcomes are
already in the actual call; callers cannot choose a raw return value. -/
def Guard (state : Futex.State) : Futex.Action → Prop
  | .compare invocation => ∃ worker expected pin,
      state.calls invocation = some ⟨worker, .wait expected, pin, .entered⟩
  | .wake invocation target => (∃ worker pin,
      state.calls invocation = some ⟨worker, .wakeOne, pin, .entered⟩) ∧
      match target with
      | none => state.queue = []
      | some selected => selected ∈ state.queue
  | .retry invocation | .spurious invocation => ∃ worker expected pin,
      state.calls invocation = some ⟨worker, .wait expected, pin, .queued⟩
  | .resume invocation _ _ _ => ∃ call outcome origin,
      state.calls invocation = some call ∧ call.phase = .ready outcome origin
  | .idle => True

/-- Every supported current service guard positively enables actual service
and retains the runtime invariant. No service success is assumed. -/
theorem service_enabled {profile : Physical.Profile} {state : Futex.State} {action : Futex.Action}
    (valid : Runtime.Invariant profile state) (guard : Guard state action) :
    ∃ after, Futex.step profile.service state action = .ok after ∧
      Runtime.Invariant profile after ∧ Atomics.History state.authority after.authority := by
  have enabled : ∃ after, Futex.step profile.service state action = .ok after := by
    cases action with
    | compare invocation =>
      obtain ⟨worker, expected, pin, found⟩ := guard
      exact valid.service.compare_enabled found
    | wake invocation target =>
      obtain ⟨⟨worker, pin, found⟩, choice⟩ := guard
      cases target with
      | none => exact ⟨_, wakeOne_empty _ _ _ _ found choice⟩
      | some selected => exact valid.service.wake_selected_enabled found choice
    | retry invocation =>
      obtain ⟨worker, expected, pin, found⟩ := guard
      exact ⟨_, retryQueued_enabled _ _ _ _ _ found⟩
    | spurious invocation =>
      obtain ⟨worker, expected, pin, found⟩ := guard
      exact ⟨_, spuriousReady_enabled _ _ _ _ _ found⟩
    | resume invocation flags rcx r11 =>
      obtain ⟨call, outcome, origin, found, ready⟩ := guard
      exact valid.service.resume_enabled found ready flags rcx r11
    | idle => exact ⟨state, rfl⟩
  obtain ⟨after, serviced⟩ := enabled
  have runtime : Runtime.step profile state (.service action) =
      .ok (after, .serviced action) := by simp [Runtime.step, serviced, Except.mapError]
  obtain ⟨invariant, resources⟩ := Runtime.step_invariant valid runtime
  exact ⟨after, serviced, invariant, resources⟩

/-- A ready actual invocation and its current executable RET/stack enable
both checked resumption and the actual decoded physical RET. The raw result
comes from the operation-indexed outcome, and all private clobbers are full
words. Current RAM is retained throughout, even when other FIFOs are nonempty.
The stack read is the complete checked eight-byte read. -/
theorem resume_ret_enabled {profile : Physical.Profile} {state : Futex.State}
    {invocation : Nat} {call : Call} {outcome : Outcome call.op} {origin : Origin}
    {saved : Suspend.Saved} {target : Word}
    (valid : Runtime.Invariant profile state)
    (found : state.calls invocation = some call) (ready : call.phase = .ready outcome origin)
    (pending : state.suspended.pending call.worker = some saved)
    (code : CodeAt state.suspended.machine.memory saved.request.continuation [0xc3])
    (stack : readWord state.suspended.machine.memory (saved.request.user.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) (flags rcx r11 : Word) :
    ∃ resumed after returned,
      resumeReady profile.service state invocation flags rcx r11 = .ok resumed ∧
      Physical.issue profile resumed call.worker = .ok (after, .machine (.retired call.worker none)) ∧
      after.suspended.machine.workers[call.worker]? = some returned ∧
      returned.returned = true ∧ returned.buffer = [] ∧
      returned.context.registers .rax = outcome.raw ∧ returned.context.rip = target ∧
      returned.context.registers .rsp = saved.request.user.registers .rsp + 8 ∧
      returned.context.flags = flags ∧ returned.context.registers .rcx = rcx ∧
      returned.context.registers .r11 = r11 ∧
      after.suspended.machine.memory = state.suspended.machine.memory ∧
      (∀ query, query ≠ call.worker →
        after.suspended.machine.workers[query]? = state.suspended.machine.workers[query]? ∧
        after.suspended.pending query = state.suspended.pending query) ∧
      Runtime.Invariant profile resumed ∧ Runtime.Invariant profile after := by
  obtain ⟨resumed, resume⟩ := valid.service.resume_enabled found ready flags rcx r11
  have runtimeResume : Runtime.step profile state (.service (.resume invocation flags rcx r11)) =
      .ok (resumed, .serviced (.resume invocation flags rcx r11)) := by
    simp [Runtime.step, Futex.step, resume, Except.mapError]
  have resumedValid := (Runtime.step_invariant valid runtimeResume).1
  obtain ⟨actualCall, actualOutcome, actualOrigin, registration, suspended, closed,
    actualFound, actualReady, registered, actualResume, close, exactResumed⟩ := resumeReady_effect resume
  have sameCall := Option.some.inj (actualFound.symm.trans found)
  subst actualCall
  have samePhase := actualReady.symm.trans ready
  have sameOutcome : actualOutcome = outcome := by cases samePhase; rfl
  subst actualOutcome
  obtain ⟨actualSaved, selected, actualPending, live, running, empty, projected, returnedAt⟩ :=
    Suspend.resume_returnsAt actualResume
  have sameSaved := Option.some.inj (actualPending.symm.trans pending)
  subst actualSaved
  have suspendedEq : resumed.suspended = suspended := by rw [exactResumed]
  have currentMemory : suspended.machine.memory = state.suspended.machine.memory :=
    Suspend.resume_memory actualResume
  have inputCode : CodeAt (TSO.sharedState suspended.machine selected).memory
      (TSO.sharedState suspended.machine selected).rip [0xc3] := by
    rw [returnedAt.memory, returnedAt.continuation]
    exact code
  have byte := inputCode.2 0 0xc3 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at byte
  have decoded : decodeAt (TSO.sharedState suspended.machine selected) = .ok .ret := by
    simp [decodeAt, byte]
  have stackPointer : (TSO.sharedState suspended.machine selected).registers .rsp =
      saved.request.user.registers .rsp := returnedAt.register .rsp (by decide) (by decide) (by decide)
  have read : readWord (TSO.sharedState suspended.machine selected).memory
      ((TSO.sharedState suspended.machine selected).registers .rsp) = .ok target := by
    rw [returnedAt.memory, stackPointer]
    exact stack
  let output := Examples.FutexStubs.returnFinal (TSO.sharedState suspended.machine selected) target
  have executed : executeInstruction (TSO.sharedState suspended.machine selected) .ret =
      .ok (.returned output) := by
    simp [executeInstruction, executeRet, read, canonicalTarget, output,
      Examples.FutexStubs.returnFinal, X86.State.writeRegister]
  have localEqual : TSO.localState suspended.machine selected = TSO.sharedState suspended.machine selected := by
    simp [TSO.localState, TSO.sharedState, empty, StoreBuffer.view]
  let machine := TSO.install suspended.machine call.worker suspended.machine.memory
    (.ofState output) true []
  have tso : TSO.issue suspended.machine call.worker = .ok (machine, .retired call.worker none) := by
    simp [TSO.issue, live, running, decoded, TSO.execute, TSO.pendingStore, TSO.locked,
      TSO.loadAddress, localEqual, executed, empty, machine, Except.mapError]
  have free : suspended.pending call.worker = none := Suspend.resume_consumed actualResume
  have actual : Suspend.issue suspended call.worker =
      .ok ({ suspended with machine := machine }, .machine (.retired call.worker none)) :=
    (Suspend.IssueEffect.machine free tso).success
  let after : Futex.State := { resumed with suspended := { suspended with machine := machine } }
  have issue : Physical.issue profile resumed call.worker =
      .ok (after, .machine (.retired call.worker none)) := by
    simp [Physical.issue, suspendedEq, actual, Physical.synchronize, Except.mapError, after]
  have runtimeRet : Runtime.step profile resumed (.issue call.worker) =
      .ok (after, .physical (.machine (.retired call.worker none))) := by
    simp [Runtime.step, issue]
  have afterValid := (Runtime.step_invariant resumedValid runtimeRet).1
  let returned : TSO.Worker := ⟨.ofState output, true, []⟩
  have installed : after.suspended.machine.workers[call.worker]? = some returned :=
    List.getElem?_set_self (List.getElem_of_getElem? live).1
  have peers : ∀ query, query ≠ call.worker →
      after.suspended.machine.workers[query]? = state.suspended.machine.workers[query]? ∧
      after.suspended.pending query = state.suspended.pending query := by
    intro query different
    constructor
    · exact (List.getElem?_set_ne different.symm).trans
        (Suspend.resume_peer different.symm actualResume)
    · change suspended.pending query = state.suspended.pending query
      simp only [Suspend.resume_pending actualResume, ite_eq_right different]
  refine ⟨resumed, after, returned, resume, issue, installed, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_,
    currentMemory, peers, resumedValid, afterValid⟩
  · change output.registers .rax = outcome.raw
    simpa [output, Examples.FutexStubs.returnFinal] using returnedAt.result
  · change output.registers .rsp = saved.request.user.registers .rsp + 8
    simp [output, Examples.FutexStubs.returnFinal, stackPointer]
  · change output.flags = flags
    simp only [output, Examples.FutexStubs.returnFinal]
    rw [projected]
    rfl
  · change output.registers .rcx = rcx
    simp only [output, Examples.FutexStubs.returnFinal]
    rw [projected]
    simp [X86.resumeAt]
  · change output.registers .r11 = r11
    simp only [output, Examples.FutexStubs.returnFinal]
    rw [projected]
    simp [X86.resumeAt]

end EDSL.OS.Futex.Clients.LiftCore
