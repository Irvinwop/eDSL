/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Suspend.Model
import EDSL.Audit

namespace EDSL.OS.Suspend
open X86

theorem request_eq_entry {request : SyscallRequest} {input : X86.State}
    (user : request.user = input)
    (continuation : request.continuation = request.user.rip + 2) :
    request = ⟨input, input.rip + 2⟩ := by
  cases request with
  | mk actual next =>
    simp only [SyscallRequest.mk.injEq]
    exact ⟨user, continuation.trans (congrArg (fun state : X86.State => state.rip + 2) user)⟩

/-- Effects of the primitive wrapper. Ordinary execution is exactly the TSO
operation; entry captures the entire architectural input without changing it. -/
inductive ExecuteEffect (state : State) (identifier : Nat) (worker : TSO.Worker)
    (instruction : Instruction) : State × Observation → Prop where
  | entered {request}
      (syscall : instruction = .syscall)
      (empty : worker.buffer = [])
      (executed : executeInstruction (TSO.sharedState state.machine worker) instruction =
        .ok (.syscall request))
      (user : request.user = TSO.sharedState state.machine worker)
      (continuation : request.continuation = request.user.rip + 2) :
      ExecuteEffect state identifier worker instruction
        (capture state identifier request, .entered identifier state.nextCall)
  | machine {after observation}
      (ordinary : instruction ≠ .syscall)
      (executed : TSO.execute state.machine identifier worker instruction = .ok (after, observation)) :
      ExecuteEffect state identifier worker instruction
        ({ state with machine := after }, .machine observation)

theorem execute_effect (state : State) (identifier : Nat) (worker : TSO.Worker)
    (instruction : Instruction) (result : State × Observation)
    (success : execute state identifier worker instruction = .ok result) :
    ExecuteEffect state identifier worker instruction result := by
  by_cases syscall : instruction = .syscall
  · subst instruction
    cases empty : worker.buffer.isEmpty with
    | false => simp [execute, empty] at success
    | true =>
      have same : result =
          (capture state identifier ⟨TSO.sharedState state.machine worker,
            (TSO.sharedState state.machine worker).rip + 2⟩,
            .entered identifier state.nextCall) := by
        simpa [execute, empty, executeInstruction, Except.mapError] using success.symm
      rw [same]
      exact .entered rfl (List.isEmpty_iff.mp empty) rfl rfl rfl
  · cases executed : TSO.execute state.machine identifier worker instruction with
    | error fault => simp [execute, syscall, executed, Except.mapError] at success
    | ok outcome =>
      have same : result = ({ state with machine := outcome.1 }, .machine outcome.2) := by
        simpa [execute, syscall, executed, Except.mapError] using success.symm
      rw [same]
      exact .machine syscall executed

theorem ExecuteEffect.success {state : State} {identifier : Nat} {worker : TSO.Worker}
    {instruction : Instruction} {result : State × Observation}
    (effect : ExecuteEffect state identifier worker instruction result) :
    execute state identifier worker instruction = .ok result := by
  cases effect with
  | entered syscall empty executed user continuation =>
    simp [execute, syscall, empty, request_eq_entry user continuation,
      executeInstruction, Except.mapError]
  | machine ordinary executed => simp [execute, ordinary, executed, Except.mapError]

theorem execute_effect_iff (state : State) (identifier : Nat) (worker : TSO.Worker)
    (instruction : Instruction) (result : State × Observation) :
    execute state identifier worker instruction = .ok result ↔
      ExecuteEffect state identifier worker instruction result :=
  ⟨execute_effect _ _ _ _ _, ExecuteEffect.success⟩

theorem execute_syscall_pendingStores (state : State) (identifier : Nat) (worker : TSO.Worker)
    (nonempty : worker.buffer ≠ []) :
    execute state identifier worker .syscall = .error .pendingStores := by
  have busy : worker.buffer.isEmpty = false := by
    cases buffer : worker.buffer with
    | nil => exact (nonempty buffer).elim
    | cons head tail => rfl
  simp [execute, busy]

theorem tso_execute_syscall (state : TSO.State) (identifier : Nat) (worker : TSO.Worker) :
    TSO.execute state identifier worker .syscall = .error .syscallBoundary := by
  simp [TSO.execute, TSO.pendingStore, TSO.locked, TSO.loadAddress, executeInstruction,
    Except.mapError]

/-- Exhaustive inversion of actual issue success. No expected request, replay,
service completion, or endpoint checker is a premise. -/
inductive IssueEffect (state : State) (identifier : Nat) : State × Observation → Prop where
  | parked {worker saved}
      (live : state.machine.workers[identifier]? = some worker)
      (returned : worker.returned = false)
      (pending : state.pending identifier = some saved) :
      IssueEffect state identifier (state, .parked identifier saved.identifier)
  | entered {worker request}
      (live : state.machine.workers[identifier]? = some worker)
      (returned : worker.returned = false)
      (pending : state.pending identifier = none)
      (decoded : decodeAt (TSO.sharedState state.machine worker) = .ok .syscall)
      (empty : worker.buffer = [])
      (executed : executeInstruction (TSO.sharedState state.machine worker) .syscall =
        .ok (.syscall request))
      (stepped : X86.step (TSO.sharedState state.machine worker) = .ok (.syscall request))
      (user : request.user = TSO.sharedState state.machine worker)
      (continuation : request.continuation = request.user.rip + 2) :
      IssueEffect state identifier
        (capture state identifier request, .entered identifier state.nextCall)
  | machine {after observation}
      (pending : state.pending identifier = none)
      (issued : TSO.issue state.machine identifier = .ok (after, observation)) :
      IssueEffect state identifier ({ state with machine := after }, .machine observation)

theorem issue_effect (state : State) (identifier : Nat) (result : State × Observation)
    (success : issue state identifier = .ok result) : IssueEffect state identifier result := by
  cases live : state.machine.workers[identifier]? with
  | none => simp [issue, live] at success
  | some worker =>
    cases returned : worker.returned with
    | true => simp [issue, live, returned] at success
    | false =>
      cases pending : state.pending identifier with
      | some saved =>
        simp [issue, live, returned, pending] at success
        subst result
        exact .parked live returned pending
      | none =>
        cases decoded : decodeAt (TSO.sharedState state.machine worker) with
        | error fault => simp [issue, live, returned, pending, decoded, Except.mapError] at success
        | ok instruction =>
          have executed : execute state identifier worker instruction = .ok result := by
            simpa [issue, live, returned, pending, decoded, Except.mapError] using success
          cases execute_effect _ _ _ _ _ executed with
          | entered syscall empty actual user continuation =>
            subst instruction
            exact .entered live returned pending decoded empty actual
              (by unfold X86.step; rw [decoded]; exact actual) user continuation
          | machine ordinary actual =>
            exact .machine pending
              (by simp [TSO.issue, live, returned, decoded, actual, Except.mapError])

theorem IssueEffect.success {state : State} {identifier : Nat} {result : State × Observation}
    (effect : IssueEffect state identifier result) : issue state identifier = .ok result := by
  cases effect with
  | parked live returned pending => simp [issue, live, returned, pending]
  | entered live returned pending decoded empty executed stepped user continuation =>
    have actual := ExecuteEffect.success
      (ExecuteEffect.entered (state := state) (identifier := identifier)
        rfl empty executed user continuation)
    simpa [issue, live, returned, pending, decoded, Except.mapError] using actual
  | machine pending issued =>
    obtain ⟨worker, instruction, live, returned, decoded, executed, _⟩ :=
      TSO.issue_effect _ _ _ issued
    have ordinary : instruction ≠ .syscall := by
      intro same
      subst instruction
      rw [tso_execute_syscall] at executed
      cases executed
    simp [issue, live, returned, pending, decoded, execute, ordinary, executed, Except.mapError]

theorem issue_effect_iff (state : State) (identifier : Nat) (result : State × Observation) :
    issue state identifier = .ok result ↔ IssueEffect state identifier result :=
  ⟨issue_effect _ _ _, IssueEffect.success⟩

theorem issue_missingThread {state : State} {identifier : Nat}
    (missing : state.machine.workers[identifier]? = none) :
    issue state identifier = .error (.underlying .missingThread) := by
  simp [issue, missing]

theorem issue_alreadyReturned {state : State} {identifier : Nat} {worker : TSO.Worker}
    (live : state.machine.workers[identifier]? = some worker) (returned : worker.returned = true) :
    issue state identifier = .error (.underlying .alreadyReturned) := by
  simp [issue, live, returned]

theorem issue_pendingStores {state : State} {identifier : Nat} {worker : TSO.Worker}
    (live : state.machine.workers[identifier]? = some worker) (returned : worker.returned = false)
    (pending : state.pending identifier = none)
    (decoded : decodeAt (TSO.sharedState state.machine worker) = .ok .syscall)
    (nonempty : worker.buffer ≠ []) : issue state identifier = .error .pendingStores := by
  simp [issue, live, returned, pending, decoded,
    execute_syscall_pendingStores state identifier worker nonempty, Except.mapError]

theorem issue_live {state : State} {identifier : Nat} {result : State × Observation}
    (success : issue state identifier = .ok result) :
    ∃ worker, state.machine.workers[identifier]? = some worker ∧ worker.returned = false := by
  cases issue_effect _ _ _ success with
  | parked live returned _ | entered live returned _ _ _ _ _ _ _ =>
    exact ⟨_, live, returned⟩
  | machine _ issued =>
    obtain ⟨worker, _, live, returned, _⟩ := TSO.issue_effect _ _ _ issued
    exact ⟨worker, live, returned⟩

/-- An entry event retains exact user state and memory and advances only the
invocation frontier and pending map. The continuation may fault on a later fetch. -/
theorem issue_entered_effect {state after : State} {identifier invocation : Nat}
    (success : issue state identifier = .ok (after, .entered identifier invocation)) :
    invocation = state.nextCall ∧
    ∃ worker request, state.machine.workers[identifier]? = some worker ∧
      worker.returned = false ∧ state.pending identifier = none ∧ worker.buffer = [] ∧
      decodeAt (TSO.sharedState state.machine worker) = .ok .syscall ∧
      X86.step (TSO.sharedState state.machine worker) = .ok (.syscall request) ∧
      request.user = TSO.sharedState state.machine worker ∧
      request.user.memory = state.machine.memory ∧
      Threads.Context.ofState request.user = worker.context ∧
      request.continuation = request.user.rip + 2 ∧
      after = capture state identifier request ∧
      after.machine = state.machine ∧ after.nextCall = state.nextCall + 1 ∧
      after.pending identifier = some ⟨invocation, identifier, request⟩ := by
  cases issue_effect _ _ _ success with
  | entered live returned pending decoded empty executed stepped user continuation =>
    refine ⟨rfl, _, _, live, returned, pending, empty, decoded, stepped, user, ?_, ?_,
      continuation, rfl, rfl, rfl, ?_⟩
    · rw [user]; rfl
    · rw [user]; rfl
    · simp [capture]

theorem issue_parked_effect {state after : State} {identifier invocation : Nat}
    (success : issue state identifier = .ok (after, .parked identifier invocation)) :
    after = state ∧ ∃ worker saved, state.machine.workers[identifier]? = some worker ∧
      worker.returned = false ∧ state.pending identifier = some saved ∧
      saved.identifier = invocation := by
  cases issue_effect _ _ _ success with
  | parked live returned pending => exact ⟨rfl, _, _, live, returned, pending, rfl⟩

theorem issue_machine_effect {state after : State} {identifier : Nat} {observation : TSO.Observation}
    (success : issue state identifier = .ok (after, .machine observation)) :
    state.pending identifier = none ∧
      TSO.issue state.machine identifier = .ok (after.machine, observation) ∧
      after.pending = state.pending ∧ after.nextCall = state.nextCall := by
  cases issue_effect _ _ _ success with
  | machine pending issued => exact ⟨pending, issued, rfl, rfl⟩

/-- Full worker framing includes every register, flags, RIP, return status and
the complete FIFO, with no condition on other workers' queues. -/
theorem tso_execute_peer {state : TSO.State} {identifier query : Nat} {worker : TSO.Worker}
    {instruction : Instruction} {result : TSO.State × TSO.Observation}
    (different : identifier ≠ query)
    (success : TSO.execute state identifier worker instruction = .ok result) :
    result.1.workers[query]? = state.workers[query]? := by
  cases TSO.execute_effect _ _ _ _ _ success <;>
    simp only [TSO.install, List.getElem?_set_ne different]

theorem tso_issue_peer {state : TSO.State} {identifier query : Nat}
    {result : TSO.State × TSO.Observation} (different : identifier ≠ query)
    (success : TSO.issue state identifier = .ok result) :
    result.1.workers[query]? = state.workers[query]? := by
  obtain ⟨_, _, _, _, _, executed, _⟩ := TSO.issue_effect _ _ _ success
  exact tso_execute_peer different executed

theorem tso_drain_peer {state : TSO.State} {identifier query : Nat}
    {result : TSO.State × TSO.Observation} (different : identifier ≠ query)
    (success : TSO.drain state identifier = .ok result) :
    result.1.workers[query]? = state.workers[query]? := by
  obtain ⟨_, _, _, _, _, _, _, same⟩ := TSO.drain_ok _ _ _ success
  rw [same]
  exact List.getElem?_set_ne different

theorem issue_peer {state : State} {identifier query : Nat} {result : State × Observation}
    (different : identifier ≠ query) (success : issue state identifier = .ok result) :
    result.1.machine.workers[query]? = state.machine.workers[query]? := by
  cases issue_effect _ _ _ success with
  | parked | entered => rfl
  | machine _ issued => exact tso_issue_peer different issued

theorem drain_ok (state : State) (identifier : Nat) (result : State × Observation)
    (success : drain state identifier = .ok result) :
    ∃ machine observation, TSO.drain state.machine identifier = .ok (machine, observation) ∧
      result = ({ state with machine := machine }, .machine observation) := by
  cases drained : TSO.drain state.machine identifier with
  | error fault => simp [drain, drained, Except.mapError] at success
  | ok outcome =>
    simp [drain, drained, Except.mapError] at success
    exact ⟨outcome.1, outcome.2, rfl, success.symm⟩

theorem drain_success {state : State} {identifier : Nat} {machine : TSO.State}
    {observation : TSO.Observation}
    (success : TSO.drain state.machine identifier = .ok (machine, observation)) :
    drain state identifier = .ok ({ state with machine := machine }, .machine observation) := by
  simp [drain, success, Except.mapError]

theorem drain_peer {state : State} {identifier query : Nat} {result : State × Observation}
    (different : identifier ≠ query) (success : drain state identifier = .ok result) :
    result.1.machine.workers[query]? = state.machine.workers[query]? := by
  obtain ⟨_, _, drained, same⟩ := drain_ok _ _ _ success
  rw [same]
  exact tso_drain_peer different drained

/-- Exact checked completion and installed state. In particular, memory is the
full current shared memory, rather than the historical request snapshot. -/
theorem resume_ok (state : State) (identifier invocation : Nat) (raw flags rcx r11 : Word)
    (after : State) (success : resume state identifier invocation raw flags rcx r11 = .ok after) :
    ∃ worker saved, state.machine.workers[identifier]? = some worker ∧ worker.returned = false ∧
      state.pending identifier = some saved ∧ saved.identifier = invocation ∧
      saved.worker = identifier ∧ worker.buffer = [] ∧
      after = { state with
        machine := TSO.install state.machine identifier state.machine.memory
          (.ofState (X86.resumeAt saved.request state.machine.memory raw flags rcx r11)) false []
        pending := fun query => if query = identifier then none else state.pending query } := by
  cases live : state.machine.workers[identifier]? with
  | none => simp [resume, live] at success
  | some worker =>
    cases returned : worker.returned with
    | true => simp [resume, live, returned] at success
    | false =>
      cases pending : state.pending identifier with
      | none => simp [resume, live, returned, pending] at success
      | some saved =>
        by_cases current : saved.identifier = invocation
        · by_cases owner : saved.worker = identifier
          · cases empty : worker.buffer.isEmpty with
            | false => simp [resume, live, returned, pending, current, owner, empty] at success
            | true =>
              simp [resume, live, returned, pending, current, owner, empty] at success
              exact ⟨worker, saved, rfl, returned, rfl, current, owner,
                List.isEmpty_iff.mp empty, success.symm⟩
          · simp [resume, live, returned, pending, current, owner] at success
        · simp [resume, live, returned, pending, current] at success

theorem resume_success {state : State} {identifier invocation : Nat} {worker : TSO.Worker}
    {saved : Saved} (raw flags rcx r11 : Word)
    (live : state.machine.workers[identifier]? = some worker) (returned : worker.returned = false)
    (pending : state.pending identifier = some saved) (current : saved.identifier = invocation)
    (owner : saved.worker = identifier) (empty : worker.buffer = []) :
    resume state identifier invocation raw flags rcx r11 = .ok
      { state with
        machine := TSO.install state.machine identifier state.machine.memory
          (.ofState (X86.resumeAt saved.request state.machine.memory raw flags rcx r11)) false []
        pending := fun query => if query = identifier then none else state.pending query } := by
  simp [resume, live, returned, pending, current, owner, empty]

theorem resume_memory {state after : State} {identifier invocation : Nat} {raw flags rcx r11 : Word}
    (success : resume state identifier invocation raw flags rcx r11 = .ok after) :
    after.machine.memory = state.machine.memory := by
  obtain ⟨_, _, _, _, _, _, _, _, same⟩ := resume_ok _ _ _ _ _ _ _ _ success
  rw [same]
  rfl

theorem resume_peer {state after : State} {identifier invocation query : Nat}
    {raw flags rcx r11 : Word} (different : identifier ≠ query)
    (success : resume state identifier invocation raw flags rcx r11 = .ok after) :
    after.machine.workers[query]? = state.machine.workers[query]? := by
  obtain ⟨_, _, _, _, _, _, _, _, same⟩ := resume_ok _ _ _ _ _ _ _ _ success
  rw [same]
  exact List.getElem?_set_ne different

theorem resume_pending {state after : State} {identifier invocation : Nat} {raw flags rcx r11 : Word}
    (success : resume state identifier invocation raw flags rcx r11 = .ok after) :
    after.pending = fun query => if query = identifier then none else state.pending query := by
  obtain ⟨_, _, _, _, _, _, _, _, same⟩ := resume_ok _ _ _ _ _ _ _ _ success
  rw [same]

theorem resume_consumed {state after : State} {identifier invocation : Nat} {raw flags rcx r11 : Word}
    (success : resume state identifier invocation raw flags rcx r11 = .ok after) :
    after.pending identifier = none := by
  simp [resume_pending success]

theorem resume_nextCall {state after : State} {identifier invocation : Nat} {raw flags rcx r11 : Word}
    (success : resume state identifier invocation raw flags rcx r11 = .ok after) :
    after.nextCall = state.nextCall := by
  obtain ⟨_, _, _, _, _, _, _, _, same⟩ := resume_ok _ _ _ _ _ _ _ _ success
  rw [same]

/-- The contract applies to the actual installed worker projected against
actual output RAM, not just to a separately constructed witness. -/
theorem resume_returnsAt {state after : State} {identifier invocation : Nat}
    {raw flags rcx r11 : Word}
    (success : resume state identifier invocation raw flags rcx r11 = .ok after) :
    ∃ saved worker, state.pending identifier = some saved ∧
      after.machine.workers[identifier]? = some worker ∧
      worker.returned = false ∧ worker.buffer = [] ∧
      TSO.sharedState after.machine worker =
        X86.resumeAt saved.request state.machine.memory raw flags rcx r11 ∧
      ReturnsAt saved.request state.machine.memory raw (TSO.sharedState after.machine worker) := by
  obtain ⟨before, saved, live, _, pending, _, _, _, same⟩ := resume_ok _ _ _ _ _ _ _ _ success
  let output := X86.resumeAt saved.request state.machine.memory raw flags rcx r11
  let worker : TSO.Worker := ⟨.ofState output, false, []⟩
  have installed : after.machine.workers[identifier]? = some worker := by
    rw [same]
    exact List.getElem?_set_self (List.getElem_of_getElem? live).1
  have projected : TSO.sharedState after.machine worker = output := by
    rw [same]
    rfl
  exact ⟨saved, worker, pending, installed, rfl, rfl, projected,
    projected ▸ X86.resumeAt_returnsAt saved.request state.machine.memory raw flags rcx r11⟩

/-- All private completion choices survive installation at full word width.
Every other register is the saved entry register, even if peers changed RAM. -/
theorem resume_registers {state after : State} {identifier invocation : Nat}
    {raw flags rcx r11 : Word}
    (success : resume state identifier invocation raw flags rcx r11 = .ok after) :
    ∃ saved worker, state.pending identifier = some saved ∧
      after.machine.workers[identifier]? = some worker ∧
      worker.context.rip = saved.request.continuation ∧
      worker.context.registers .rax = raw ∧ worker.context.flags = flags ∧
      worker.context.registers .rcx = rcx ∧ worker.context.registers .r11 = r11 ∧
      ∀ register, register ≠ .rax → register ≠ .rcx → register ≠ .r11 →
        worker.context.registers register = saved.request.user.registers register := by
  obtain ⟨saved, worker, pending, live, _, _, projected, returned⟩ := resume_returnsAt success
  refine ⟨saved, worker, pending, live, returned.continuation, returned.result, ?_, ?_, ?_,
    returned.register⟩
  · change (TSO.sharedState after.machine worker).flags = flags
    rw [projected]
    rfl
  · change (TSO.sharedState after.machine worker).registers .rcx = rcx
    rw [projected]
    simp [X86.resumeAt]
  · change (TSO.sharedState after.machine worker).registers .r11 = r11
    rw [projected]
    simp [X86.resumeAt]

/-- Failure cases are ordered exactly as the runtime checks. They apply to
arbitrary raw wrapper states, including malformed pending entries. -/
inductive ResumeFailure (state : State) (identifier invocation : Nat) : Fault → Prop where
  | missing (live : state.machine.workers[identifier]? = none) :
      ResumeFailure state identifier invocation (.underlying .missingThread)
  | returned {worker} (live : state.machine.workers[identifier]? = some worker)
      (returned : worker.returned = true) :
      ResumeFailure state identifier invocation (.underlying .alreadyReturned)
  | absent {worker} (live : state.machine.workers[identifier]? = some worker)
      (returned : worker.returned = false) (pending : state.pending identifier = none) :
      ResumeFailure state identifier invocation .noPending
  | stale {worker saved} (live : state.machine.workers[identifier]? = some worker)
      (returned : worker.returned = false) (pending : state.pending identifier = some saved)
      (current : saved.identifier ≠ invocation) :
      ResumeFailure state identifier invocation .staleCall
  | owner {worker saved} (live : state.machine.workers[identifier]? = some worker)
      (returned : worker.returned = false) (pending : state.pending identifier = some saved)
      (current : saved.identifier = invocation) (owner : saved.worker ≠ identifier) :
      ResumeFailure state identifier invocation .wrongWorker
  | queued {worker saved} (live : state.machine.workers[identifier]? = some worker)
      (returned : worker.returned = false) (pending : state.pending identifier = some saved)
      (current : saved.identifier = invocation) (owner : saved.worker = identifier)
      (nonempty : worker.buffer ≠ []) :
      ResumeFailure state identifier invocation .pendingStores

theorem ResumeFailure.error {state : State} {identifier invocation : Nat} {fault : Fault}
    (failure : ResumeFailure state identifier invocation fault) (raw flags rcx r11 : Word) :
    resume state identifier invocation raw flags rcx r11 = .error fault := by
  cases failure with
  | missing live => simp [resume, live]
  | returned live returned => simp [resume, live, returned]
  | absent live returned pending => simp [resume, live, returned, pending]
  | stale live returned pending current => simp [resume, live, returned, pending, current]
  | owner live returned pending current owner =>
    simp [resume, live, returned, pending, current, owner]
  | @queued worker saved live returned pending current owner nonempty =>
    have busy : worker.buffer.isEmpty = false := by
      cases buffer : worker.buffer with
      | nil => exact (nonempty buffer).elim
      | cons head tail => rfl
    simp [resume, live, returned, pending, current, owner, busy]

theorem resume_failure (state : State) (identifier invocation : Nat) (raw flags rcx r11 : Word)
    (fault : Fault) (failed : resume state identifier invocation raw flags rcx r11 = .error fault) :
    ResumeFailure state identifier invocation fault := by
  cases live : state.machine.workers[identifier]? with
  | none =>
    simp [resume, live] at failed
    subst fault
    exact .missing live
  | some worker =>
    cases returned : worker.returned with
    | true =>
      simp [resume, live, returned] at failed
      subst fault
      exact .returned live returned
    | false =>
      cases pending : state.pending identifier with
      | none =>
        simp [resume, live, returned, pending] at failed
        subst fault
        exact .absent live returned pending
      | some saved =>
        by_cases current : saved.identifier = invocation
        · by_cases owner : saved.worker = identifier
          · by_cases empty : worker.buffer = []
            · rw [resume_success raw flags rcx r11 live returned pending current owner empty] at failed
              cases failed
            · have busy : worker.buffer.isEmpty = false := by
                cases buffer : worker.buffer with
                | nil => exact (empty buffer).elim
                | cons head tail => rfl
              simp [resume, live, returned, pending, current, owner, busy] at failed
              subst fault
              exact .queued live returned pending current owner empty
          · simp [resume, live, returned, pending, current, owner] at failed
            subst fault
            exact .owner live returned pending current owner
        · simp [resume, live, returned, pending, current] at failed
          subst fault
          exact .stale live returned pending current

theorem resume_error_iff (state : State) (identifier invocation : Nat) (raw flags rcx r11 : Word)
    (fault : Fault) :
    resume state identifier invocation raw flags rcx r11 = .error fault ↔
      ResumeFailure state identifier invocation fault :=
  ⟨resume_failure _ _ _ _ _ _ _ _, fun failure => failure.error raw flags rcx r11⟩

theorem resume_missingThread {state : State} {identifier invocation : Nat}
    (missing : state.machine.workers[identifier]? = none) (raw flags rcx r11 : Word) :
    resume state identifier invocation raw flags rcx r11 = .error (.underlying .missingThread) :=
  (ResumeFailure.missing missing).error raw flags rcx r11

theorem resume_alreadyReturned {state : State} {identifier invocation : Nat} {worker : TSO.Worker}
    (live : state.machine.workers[identifier]? = some worker) (returned : worker.returned = true)
    (raw flags rcx r11 : Word) :
    resume state identifier invocation raw flags rcx r11 = .error (.underlying .alreadyReturned) :=
  (ResumeFailure.returned live returned).error raw flags rcx r11

theorem resume_noPending {state : State} {identifier invocation : Nat} {worker : TSO.Worker}
    (live : state.machine.workers[identifier]? = some worker) (returned : worker.returned = false)
    (pending : state.pending identifier = none) (raw flags rcx r11 : Word) :
    resume state identifier invocation raw flags rcx r11 = .error .noPending :=
  (ResumeFailure.absent live returned pending).error raw flags rcx r11

theorem resume_staleCall {state : State} {identifier invocation : Nat} {worker : TSO.Worker}
    {saved : Saved} (live : state.machine.workers[identifier]? = some worker)
    (returned : worker.returned = false) (pending : state.pending identifier = some saved)
    (current : saved.identifier ≠ invocation) (raw flags rcx r11 : Word) :
    resume state identifier invocation raw flags rcx r11 = .error .staleCall :=
  (ResumeFailure.stale live returned pending current).error raw flags rcx r11

theorem resume_wrongWorker {state : State} {identifier invocation : Nat} {worker : TSO.Worker}
    {saved : Saved} (live : state.machine.workers[identifier]? = some worker)
    (returned : worker.returned = false) (pending : state.pending identifier = some saved)
    (current : saved.identifier = invocation) (owner : saved.worker ≠ identifier)
    (raw flags rcx r11 : Word) :
    resume state identifier invocation raw flags rcx r11 = .error .wrongWorker :=
  (ResumeFailure.owner live returned pending current owner).error raw flags rcx r11

theorem resume_pendingStores {state : State} {identifier invocation : Nat} {worker : TSO.Worker}
    {saved : Saved} (live : state.machine.workers[identifier]? = some worker)
    (returned : worker.returned = false) (pending : state.pending identifier = some saved)
    (current : saved.identifier = invocation) (owner : saved.worker = identifier)
    (nonempty : worker.buffer ≠ []) (raw flags rcx r11 : Word) :
    resume state identifier invocation raw flags rcx r11 = .error .pendingStores :=
  (ResumeFailure.queued live returned pending current owner nonempty).error raw flags rcx r11

theorem resume_twice {state after : State} {identifier invocation : Nat} {raw flags rcx r11 : Word}
    (success : resume state identifier invocation raw flags rcx r11 = .ok after)
    (raw' flags' rcx' r11' : Word) :
    resume after identifier invocation raw' flags' rcx' r11' = .error .noPending := by
  obtain ⟨_, _, _, live, returned, _, _, _⟩ := resume_returnsAt success
  exact resume_noPending live returned (resume_consumed success) raw' flags' rcx' r11'

theorem issue_nextCall {state : State} {identifier : Nat} {result : State × Observation}
    (success : issue state identifier = .ok result) : state.nextCall ≤ result.1.nextCall := by
  cases issue_effect _ _ _ success with
  | parked | machine => exact Nat.le_refl _
  | entered => exact Nat.le_succ _

theorem drain_nextCall {state : State} {identifier : Nat} {result : State × Observation}
    (success : drain state identifier = .ok result) : result.1.nextCall = state.nextCall := by
  obtain ⟨_, _, _, same⟩ := drain_ok _ _ _ success
  rw [same]

theorem drain_pending {state : State} {identifier : Nat} {result : State × Observation}
    (success : drain state identifier = .ok result) : result.1.pending = state.pending := by
  obtain ⟨_, _, _, same⟩ := drain_ok _ _ _ success
  rw [same]

theorem step_nextCall {state : State} {action : Action} {result : State × Observation}
    (success : step state action = .ok result) : state.nextCall ≤ result.1.nextCall := by
  cases action with
  | issue identifier => exact issue_nextCall success
  | drain identifier => rw [drain_nextCall success]; exact Nat.le_refl _
  | resume identifier invocation raw flags rcx r11 =>
    cases completed : resume state identifier invocation raw flags rcx r11 with
    | error fault => simp [step, completed] at success
    | ok after =>
      simp [step, completed] at success
      subst result
      rw [resume_nextCall completed]
      exact Nat.le_refl _
  | idle => simp [step] at success; subst result; exact Nat.le_refl _

/-- New pending invocations arise only at the current frontier; all other
pending records are exact old records, including their historical memory. -/
theorem step_pending_origin {state : State} {action : Action} {result : State × Observation}
    {query : Nat} {saved : Saved} (success : step state action = .ok result)
    (pending : result.1.pending query = some saved) :
    state.pending query = some saved ∨
      (saved.identifier = state.nextCall ∧ result.1.nextCall = state.nextCall + 1 ∧
        state.pending query = none) := by
  cases action with
  | issue identifier =>
    cases issue_effect _ _ _ success with
    | parked => exact .inl pending
    | machine => exact .inl pending
    | @entered worker request live returned absent decoded empty executed stepped user continuation =>
      by_cases own : query = identifier
      · subst query
        have same : saved = ⟨state.nextCall, identifier, request⟩ := by
          simpa only [capture, ↓reduceIte, Option.some.injEq] using pending.symm
        exact .inr ⟨by rw [same], rfl, absent⟩
      · exact .inl (by simpa only [capture, ite_eq_right own] using pending)
  | drain identifier => exact .inl (by simpa only [drain_pending success] using pending)
  | resume identifier invocation raw flags rcx r11 =>
    cases completed : resume state identifier invocation raw flags rcx r11 with
    | error fault => simp [step, completed] at success
    | ok after =>
      simp [step, completed] at success
      subst result
      by_cases own : query = identifier
      · subst query
        rw [resume_consumed completed] at pending
        cases pending
      · exact .inl (by simpa only [resume_pending completed, ite_eq_right own] using pending)
  | idle => simp [step] at success; subst result; exact .inl pending

end EDSL.OS.Suspend

#audit_edsl
