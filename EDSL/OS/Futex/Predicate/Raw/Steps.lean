import EDSL.OS.Futex.Predicate.Raw.Instructions

namespace EDSL.OS.Futex.Predicate
open X86

theorem ordinary_next {client : Client} {point : Point} {context : Threads.Context} {memory : Memory}
    (current : Running client point context) (ready : Ready client point memory)
    (notCall : point ≠ .syscall) (notReturn : ∀ observed, point ≠ .done observed) :
    ∃ next after, executeInstruction (MachineThreads.contextState context memory) point.instruction =
      .ok (.next (MachineThreads.contextState after memory)) ∧ Running client next after := by
  cases point with
  | load =>
    obtain ⟨_, observed, readable⟩ := ready
    exact ⟨.compare observed, context.loaded observed,
      execute_load context memory observed (by rw [current.rdi]; exact readable), current.load_next observed⟩
  | compare observed =>
    exact ⟨.branch observed, cmpContext context, execute_cmp context memory, current.compare_next⟩
  | branch observed =>
    by_cases zero : observed = 0
    · subst observed
      have zf : context.flags.getLsbD 6 = true := by simpa using current.fields.2
      exact ⟨.number, branchContext context (context.rip + 2),
        execute_jnz_fallthrough context memory 0x16 zf, current.branch_zero⟩
    · have zf : context.flags.getLsbD 6 = false := by
        have bits : context.flags.getLsbD 6 = (observed == 0) := current.fields.2
        rw [beq_eq_false_iff_ne.mpr zero] at bits
        exact bits
      have executed := execute_jnz_taken context memory 0x16 zf
        (by rw [branch_done_target current]; exact ready zero)
      rw [branch_done_target current] at executed
      exact ⟨.done observed, branchContext context (client.entry.rip + 29),
        executed, current.branch_nonzero zero⟩
  | number => exact ⟨.operation, movContext context .rax 202, execute_mov .., current.number_next⟩
  | operation => exact ⟨.syscall, movContext context .rsi 128, execute_mov .., current.operation_next⟩
  | syscall => exact (notCall rfl).elim
  | resumed raw => exact ⟨.retryCompare, movContext context .rax 1, execute_mov .., current.resumed_next⟩
  | retryCompare => exact ⟨.retryBranch, cmpContext context, execute_cmp .., current.retryCompare_next⟩
  | retryBranch =>
    have executed := execute_jnz_taken context memory 0xe3 current.fields.2.2
      (by rw [branch_retry_target current]; exact ready)
    rw [branch_retry_target current] at executed
    exact ⟨.load, branchContext context client.entry.rip, executed, current.retryBranch_next⟩
  | done observed => exact (notReturn observed rfl).elim

theorem current_load_aligned {client : Client} {point : Point} {context : Threads.Context}
    {memory : Memory} (current : Running client point context) (ready : Ready client point memory)
    {address : Word} (load : TSO.loadAddress context point.instruction = some address) :
    atomicAddressable address = true := by
  cases point <;> simp [Point.instruction, TSO.loadAddress] at load
  rw [← load, current.rdi]
  exact ready.1

theorem issue_next {client : Client} {point : Point} {state : Suspend.State}
    {worker : Nat} {before : TSO.Worker} {context : Threads.Context}
    (atWorker : state.machine.workers[worker]? = some before)
    (current : Running client point before.context) (live : before.returned = false)
    (free : state.pending worker = none) (empty : before.buffer = [])
    (code : CodeAt state.machine.memory client.entry.rip bytes)
    (ready : Ready client point state.machine.memory) (notCall : point ≠ .syscall)
    (executed : executeInstruction (MachineThreads.contextState before.context state.machine.memory)
      point.instruction = .ok (.next (MachineThreads.contextState context state.machine.memory))) :
    Suspend.issue state worker =
      .ok (retire state worker context, .machine (.retired worker none)) := by
  have decoded : decodeAt (TSO.sharedState state.machine before) = .ok point.instruction :=
    decode_point current code
  have notSyscall : point.instruction ≠ .syscall := fun equation => notCall (Point.syscall_only equation)
  have executedLocal : executeInstruction (TSO.localState state.machine before) point.instruction =
      .ok (.next (MachineThreads.contextState context state.machine.memory)) := by
    simpa [TSO.localState, empty] using executed
  cases loading : TSO.loadAddress before.context point.instruction with
  | none =>
    simp [Suspend.issue, atWorker, live, free, decoded, Suspend.execute, notSyscall,
      TSO.execute, Point.no_store, Point.unlocked, loading, executedLocal, Except.mapError,
      Threads.Context.ofState, MachineThreads.contextState, empty, retire]
  | some address =>
    have aligned := current_load_aligned current ready loading
    simp [Suspend.issue, atWorker, live, free, decoded, Suspend.execute, notSyscall,
      TSO.execute, Point.no_store, Point.unlocked, loading, aligned, executedLocal, Except.mapError,
      Threads.Context.ofState, MachineThreads.contextState, empty, retire]

theorem ordinary_enabled {client : Client} {point : Point} {state : Suspend.State}
    {worker : Nat} {before : TSO.Worker}
    (atWorker : state.machine.workers[worker]? = some before)
    (current : Running client point before.context) (live : before.returned = false)
    (free : state.pending worker = none) (empty : before.buffer = [])
    (code : CodeAt state.machine.memory client.entry.rip bytes)
    (ready : Ready client point state.machine.memory)
    (notCall : point ≠ .syscall) (notReturn : ∀ observed, point ≠ .done observed) :
    ∃ next context,
      Suspend.issue state worker = .ok (retire state worker context, .machine (.retired worker none)) ∧
      Running client next context ∧
      (retire state worker context).machine.workers[worker]? = some ⟨context, false, []⟩ ∧
      WorkerControl client worker (retire state worker context) ⟨context, false, []⟩ := by
  obtain ⟨next, context, executed, controlled⟩ := ordinary_next current ready notCall notReturn
  exact ⟨next, context, issue_next atWorker current live free empty code ready notCall executed,
    controlled, List.getElem?_set_self (List.getElem_of_getElem? atWorker).1,
    .running next controlled rfl free rfl⟩

theorem syscall_enabled {client : Client} {state : Suspend.State} {worker : Nat} {before : TSO.Worker}
    (atWorker : state.machine.workers[worker]? = some before)
    (current : Running client .syscall before.context) (live : before.returned = false)
    (free : state.pending worker = none) (empty : before.buffer = [])
    (code : CodeAt state.machine.memory client.entry.rip bytes) :
    let request : SyscallRequest := ⟨TSO.sharedState state.machine before, before.context.rip + 2⟩
    let after := Suspend.capture state worker request
    Suspend.issue state worker = .ok (after, .entered worker state.nextCall) ∧
      after.pending worker = some ⟨state.nextCall, worker, request⟩ ∧
      after.nextCall = state.nextCall + 1 ∧ client.Family request ∧
      WorkerControl client worker after before := by
  dsimp only
  have decoded : decodeAt (TSO.sharedState state.machine before) = .ok .syscall :=
    decode_point current code
  have family : client.Family ⟨TSO.sharedState state.machine before, before.context.rip + 2⟩ :=
    ⟨current, rfl⟩
  refine ⟨?_, ?_, rfl, family, ?_⟩
  · simp only [Suspend.issue, atWorker, live, Bool.false_eq_true, ↓reduceIte,
      free, decoded, Except.mapError, ok_bind]
    simp [Suspend.execute, empty,
      executeInstruction, TSO.sharedState, MachineThreads.contextState, Except.mapError]
  · simp [Suspend.capture]
  · exact .entered ⟨state.nextCall, worker,
      ⟨TSO.sharedState state.machine before, before.context.rip + 2⟩⟩
      (by simp [Suspend.capture]) rfl family rfl live empty

theorem ret_enabled {client : Client} {state : Suspend.State} {worker : Nat} {before : TSO.Worker}
    {observed : BitVec 32}
    (atWorker : state.machine.workers[worker]? = some before)
    (current : Running client (.done observed) before.context) (live : before.returned = false)
    (free : state.pending worker = none) (empty : before.buffer = [])
    (code : CodeAt state.machine.memory client.entry.rip bytes)
    (stack : readWord state.machine.memory (client.entry.registers .rsp) = .ok client.returnTarget)
    (canonical : X86.canonical client.returnTarget = true) :
    let context := client.returned before.context
    let after := retire state worker context true
    Suspend.issue state worker = .ok (after, .machine (.retired worker none)) ∧
      after.machine.workers[worker]? = some ⟨context, true, []⟩ ∧
      WorkerControl client worker after ⟨context, true, []⟩ ∧
      context.registers .rax = observed.setWidth 64 ∧ observed ≠ 0 ∧
      context.rip = client.returnTarget ∧ context.registers .rsp = client.entry.registers .rsp + 8 ∧
      context.flags = before.context.flags ∧ context.registers .rcx = before.context.registers .rcx ∧
      context.registers .r11 = before.context.registers .r11 := by
  dsimp only
  have decoded : decodeAt (TSO.sharedState state.machine before) = .ok .ret :=
    decode_point current code
  have executed : executeInstruction (TSO.localState state.machine before) .ret = .ok
      (.returned (MachineThreads.contextState (client.returned before.context) state.machine.memory)) := by
    simpa [TSO.localState, empty] using execute_ret client before.context state.machine.memory
      (by rw [current.rsp]; exact stack) canonical
  refine ⟨?_, List.getElem?_set_self (List.getElem_of_getElem? atWorker).1,
    .returned before.context observed current rfl rfl free rfl, ?_, current.fields.2.1,
    rfl, ?_, rfl, ?_, ?_⟩
  · simp [Suspend.issue, atWorker, live, free, decoded, Suspend.execute, TSO.execute,
      TSO.pendingStore, TSO.locked, TSO.loadAddress, executed, Except.mapError, empty,
      Threads.Context.ofState, MachineThreads.contextState, retire]
  · simpa [Client.returned] using current.fields.1
  · simp [Client.returned, current.rsp]
  · simp [Client.returned]
  · simp [Client.returned]

theorem parked_enabled {client : Client} {state : Suspend.State} {worker : Nat} {before : TSO.Worker}
    {saved : Suspend.Saved}
    (atWorker : state.machine.workers[worker]? = some before) (live : before.returned = false)
    (pending : state.pending worker = some saved) (owner : saved.worker = worker)
    (family : client.Family saved.request) (context : before.context = .ofState saved.request.user)
    (empty : before.buffer = []) :
    Suspend.issue state worker = .ok (state, .parked worker saved.identifier) ∧
      WorkerControl client worker state before := by
  exact ⟨by simp [Suspend.issue, atWorker, live, pending],
    .entered saved pending owner family context live empty⟩

def resumedState (state : Suspend.State) (worker : Nat) (request : SyscallRequest)
    (raw flags rcx r11 : Word) : Suspend.State :=
  { retire state worker (resumeContext request raw flags rcx r11) with
    pending := fun query => if query = worker then none else state.pending query }

theorem resume_enabled {client : Client} {state : Suspend.State} {worker : Nat} {before : TSO.Worker}
    {saved : Suspend.Saved}
    (atWorker : state.machine.workers[worker]? = some before) (live : before.returned = false)
    (pending : state.pending worker = some saved) (owner : saved.worker = worker)
    (family : client.Family saved.request) (empty : before.buffer = []) (raw flags rcx r11 : Word) :
    let context := resumeContext saved.request raw flags rcx r11
    let after := resumedState state worker saved.request raw flags rcx r11
    Suspend.resume state worker saved.identifier raw flags rcx r11 = .ok after ∧
      after.machine.workers[worker]? = some ⟨context, false, []⟩ ∧
      Running client (.resumed raw) context ∧ WorkerControl client worker after ⟨context, false, []⟩ ∧
      after.pending worker = none ∧ after.nextCall = state.nextCall ∧
      after.machine.memory = state.machine.memory ∧ context.rip = client.entry.rip + 19 := by
  dsimp only
  have current := family_resume family raw flags rcx r11
  refine ⟨?_, List.getElem?_set_self (List.getElem_of_getElem? atWorker).1,
    current, .running (.resumed raw) current rfl ?_ rfl, ?_, rfl, rfl, Family.continuation family⟩
  · simpa only [resume_context_exact, Threads.Context.ofState, MachineThreads.contextState,
      resumedState, retire] using
      Suspend.resume_success raw flags rcx r11 atWorker live pending rfl owner empty
  · simp [resumedState]
  · simp [resumedState]

theorem resumedState_peer {state : Suspend.State} {worker peer : Nat} {request : SyscallRequest}
    {raw flags rcx r11 : Word} (different : peer ≠ worker) :
    (resumedState state worker request raw flags rcx r11).machine.workers[peer]? =
      state.machine.workers[peer]? ∧
    (resumedState state worker request raw flags rcx r11).pending peer = state.pending peer := by
  exact ⟨retire_peer different, by simp [resumedState, different]⟩

end EDSL.OS.Futex.Predicate
