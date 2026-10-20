/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexTSO.Facts
import EDSL.OS.MutexTSO.Machine

namespace EDSL.OS.MutexTSO
open X86

/-- A stall keeps the entire logical state. A retirement is exactly one
checked replay dispatch, including the actual optional atomic event. -/
inductive IssueResult (config : Mutex.Config) (before : Physical) (logical : Logical)
    (identifier : Nat) : Physical × TSO.Observation → Prop where
  | blocked (related : Rel config before logical) :
      IssueResult config before logical identifier (before, .blocked identifier)
  | retired {after : Physical} {logicalAfter : Logical} {event : Option AtomicEvent}
      (checked : MutexReplay.dispatch logical identifier = .ok (logicalAfter, event))
      (related : Rel config after logicalAfter) :
      IssueResult config before logical identifier (after, .retired identifier event)

private theorem issue_of_execute {physical : Physical} {identifier : Nat}
    {worker : TSO.Worker} {instruction : Instruction} {result : Physical × TSO.Observation}
    (live : physical.workers[identifier]? = some worker)
    (running : worker.returned = false)
    (decoded : decodeAt (TSO.sharedState physical worker) = .ok instruction)
    (executed : TSO.execute physical identifier worker instruction = .ok result) :
    TSO.issue physical identifier = .ok result := by
  simp [TSO.issue, live, running, decoded, Except.mapError, executed]

/-- Installation retains peers' complete contexts and queues. The selected
queue is checked against its actual new guard, independently of retirement
credit or any final payload value. -/
private theorem Rel.install_issue {config : Mutex.Config} {physical : Physical}
    {logical logicalAfter : Logical} {identifier : Nat} {before : TSO.Worker}
    {after : MutexReplay.Worker} {memory : Memory} {context : Threads.Context}
    {returned : Bool} {buffer : StoreBuffer.Buffer} {event : Option AtomicEvent}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    (live : physical.workers[identifier]? = some before)
    (checked : MutexReplay.dispatch logical identifier = .ok (logicalAfter, event))
    (workers : logicalAfter.workers = logical.workers.set identifier after)
    (architectureEq : architecture ⟨context, returned, buffer⟩ = MutexReplay.eraseWorker after)
    (payloads : ∀ store ∈ buffer, store.address = config.dataAddress)
    (unguarded : after.guard = none → buffer = [])
    (memoryEq : logicalMemory logicalAfter =
      overlay (TSO.install physical identifier memory context returned buffer))
    (issued : TSO.issue physical identifier = .ok
      (TSO.install physical identifier memory context returned buffer, .retired identifier event)) :
    Rel config (TSO.install physical identifier memory context returned buffer) logicalAfter := by
  have bound := (List.getElem_of_getElem? live).1
  have permissions := TSO.issue_permissions issued
  change memory.executable = physical.memory.executable ∧
    memory.writable = physical.memory.writable at permissions
  refine ⟨MutexReplay.dispatch_invariant _ _ _ _ related.invariant closed checked,
    MutexReplay.dispatch_executionReady _ _ _ related.invariant.shared related.ready checked,
    ?_, related.buffers.issue issued, ?_, ?_, memoryEq, ?_⟩
  · simp only [TSO.install, workers, List.map_set, related.contexts, architectureEq]
  · intro worker member store queued
    rcases List.mem_or_eq_of_mem_set member with old | rfl
    · exact related.payloads worker old store queued
    · exact payloads store queued
  · intro query worker selected found present free
    change (physical.workers.set identifier ⟨context, returned, buffer⟩)[query]? = some worker at found
    rw [workers] at present
    by_cases own : identifier = query
    · subst query
      rw [List.getElem?_set_self bound] at found
      cases found
      have logicalBound : identifier < logical.workers.length := by
        have lengths := congrArg List.length related.contexts
        simp only [List.length_map] at lengths
        omega
      rw [List.getElem?_set_self logicalBound] at present
      cases present
      exact unguarded free
    · rw [List.getElem?_set_ne own] at found present
      exact related.unguarded query worker selected found present free
  · exact ⟨related.profile.payload,
      by simpa only [TSO.dataOnly, TSO.install, permissions.1] using related.profile.lockData,
      by simpa only [TSO.dataOnly, TSO.install, permissions.1] using related.profile.payloadData⟩

private theorem Rel.advance_issue_result {config : Mutex.Config} {physical : Physical}
    {logical : Logical} {identifier : Nat} {before : TSO.Worker}
    {worker : MutexReplay.Worker} {output : MutexReplay.Result}
    {memory : Memory} {buffer : StoreBuffer.Buffer}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    (live : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some worker)
    (advanced : MutexReplay.advance logical identifier worker = .ok output)
    (payloads : ∀ store ∈ buffer, store.address = config.dataAddress)
    (unguarded : output.guard = none → buffer = [])
    (memoryEq : logicalMemory ⟨output.shared,
        logical.workers.set identifier (MutexReplay.evolved worker output)⟩ =
      overlay (TSO.install physical identifier memory output.context output.returned buffer))
    (issued : TSO.issue physical identifier = .ok
      (TSO.install physical identifier memory output.context output.returned buffer,
        .retired identifier output.event)) :
    IssueResult config physical logical identifier
      (TSO.install physical identifier memory output.context output.returned buffer,
        .retired identifier output.event) := by
  have checked : MutexReplay.dispatch logical identifier = .ok
      (⟨output.shared, logical.workers.set identifier (MutexReplay.evolved worker output)⟩,
        output.event) := by
    simp only [MutexReplay.dispatch, logicalLive, MutexReplay.evolved, advanced,
      ok_bind, pure_ok]
  obtain ⟨_, _, _, _, returned⟩ := MutexReplay.advance_ok _ _ _ _ advanced
  apply IssueResult.retired checked
  apply related.install_issue closed live checked rfl ?_ payloads unguarded memoryEq issued
  change output.returned = decide (MutexReplay.nextPhase worker output = .completed) at returned
  change (⟨output.context, output.returned⟩ : MachineThreads.Worker) =
    ⟨output.context, decide (MutexReplay.nextPhase worker output = .completed)⟩
  rw [returned]

private theorem action_load_guard {worker : MutexReplay.Worker} {guard : Mutex.Lease}
    (selected : MutexReplay.action worker = .ok (.load guard)) : worker.guard = some guard := by
  cases phase : worker.phase <;> cases held : worker.guard <;>
    simp_all [MutexReplay.action]

private theorem action_store_guard {worker : MutexReplay.Worker} {guard : Mutex.Lease}
    (selected : MutexReplay.action worker = .ok (.store guard)) : worker.guard = some guard := by
  cases phase : worker.phase <;> cases held : worker.guard <;>
    simp_all [MutexReplay.action]

private theorem action_release_guard {worker : MutexReplay.Worker} {guard : Mutex.Lease}
    (selected : MutexReplay.action worker = .ok (.release guard)) : worker.guard = some guard := by
  cases phase : worker.phase <;> cases held : worker.guard <;>
    simp_all [MutexReplay.action]

private theorem plain_no_store (context : Threads.Context) (instruction : MutexReplay.Plain) :
    TSO.pendingStore context instruction.instruction = none := by cases instruction <;> rfl

private theorem plain_unlocked (instruction : MutexReplay.Plain) :
    TSO.locked instruction.instruction = false := by cases instruction <;> rfl

private theorem plain_no_load (context : Threads.Context) (instruction : MutexReplay.Plain) :
    TSO.loadAddress context instruction.instruction = none := by cases instruction <;> rfl

private theorem Rel.decode {config : Mutex.Config} {physical : Physical} {logical : Logical}
    {identifier : Nat} {before : TSO.Worker} {worker : MutexReplay.Worker}
    {instruction : Instruction} (related : Rel config physical logical)
    (physicalLive : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some worker)
    (decoded : decodeAt (worker.context.snapshot logical.shared.shared.resources.space) =
      .ok instruction) :
    decodeAt (TSO.sharedState physical before) = .ok instruction := by
  have contexts := (related.match_workers physicalLive logicalLive).1
  apply (decodeAt_fetch_congr (TSO.sharedState physical before)
    (worker.context.snapshot logical.shared.shared.resources.space) ?_ ?_).trans decoded
  · exact congrArg Threads.Context.rip contexts
  · intro address
    exact (related.fetch address).symm

private theorem Rel.operands {config : Mutex.Config} {physical : Physical} {logical : Logical}
    {identifier : Nat} {before : TSO.Worker} {worker : MutexReplay.Worker}
    (related : Rel config physical logical)
    (physicalLive : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some worker)
    (unfinished : worker.phase ≠ .completed) :
    before.context.registers .rdi = config.lockAddress ∧
      before.context.registers .rsi = config.dataAddress ∧
      before.context.registers .rsp = worker.entry.registers .rsp := by
  have contexts := (related.match_workers physicalLive logicalLive).1
  have privateInv := related.invariant.workers identifier worker logicalLive
  have fields := MutexReplay.contextValid_fields worker privateInv.context unfinished
  rw [contexts]
  exact ⟨fields.1.trans privateInv.operands.1,
    fields.2.1.trans privateInv.operands.2, fields.2.2.1⟩

/-- Reverse exchange transport constructs physical success from the current
logical execution. Pending peer payload writes commute with the lock exchange;
neither their absence nor equality of the entire input memories is assumed. -/
private theorem Rel.exchange_issue {config : Mutex.Config} {physical : Physical}
    {logical : Logical} {identifier : Nat} {before : TSO.Worker}
    {worker : MutexReplay.Worker} {context : Threads.Context} {memory : Memory}
    {event : AtomicEvent} (related : Rel config physical logical)
    (physicalLive : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some worker)
    (running : before.returned = false)
    (unfinished : worker.phase ≠ .completed)
    (empty : before.buffer = [])
    (decoded : decodeAt (worker.context.snapshot logical.shared.shared.resources.space) =
      .ok .exchangeEaxRdi)
    (executed : executeInstruction (MachineThreads.contextState worker.context (logicalMemory logical))
      .exchangeEaxRdi = .ok (.atomic event (MachineThreads.contextState context memory))) :
    ∃ physicalMemory,
      TSO.issue physical identifier = .ok
        (TSO.install physical identifier physicalMemory context false [],
          .retired identifier (some event)) ∧
      memory = overlay (TSO.install physical identifier physicalMemory context false []) := by
  have contexts := (related.match_workers physicalLive logicalLive).1
  have operands := related.operands physicalLive logicalLive unfinished
  have checked : ∀ store ∈ pending physical,
      canStoreDWord (TSO.sharedState physical before).memory store.address = true := by
    intro store member
    exact (related.pending_valid store member).2.1
  have separate : ∀ store ∈ pending physical,
      StoreBuffer.Separate store.address ((TSO.sharedState physical before).registers .rdi) := by
    intro store member
    change StoreBuffer.Separate store.address (before.context.registers .rdi)
    rw [related.pending_payloads store member, operands.1]
    exact related.invariant.data_lock_separate
  have forwarded : executeInstruction
      { TSO.sharedState physical before with memory := StoreBuffer.view physical.memory (pending physical) }
      .exchangeEaxRdi = .ok (.atomic event (MachineThreads.contextState context memory)) := by
    simpa only [TSO.sharedState, MachineThreads.contextState, contexts,
      related.memory, overlay] using executed
  obtain ⟨output, actual, outputEq⟩ :=
    (execute_exchange_view_iff (TSO.sharedState physical before) (pending physical)
      checked separate event (MachineThreads.contextState context memory)).mp forwarded
  have contextEq : Threads.Context.ofState output = context := by
    have same := congrArg Threads.Context.ofState outputEq
    exact same.symm
  have transition := executeInstruction_atomic_transition actual
  have data : TSO.dataOnly physical.memory (before.context.registers .rdi) = true := by
    rw [operands.1]
    exact related.profile.lockData
  have performed := (TSO.ExecuteEffect.atomic (state := physical) (identifier := identifier)
    (worker := before) (instruction := .exchangeEaxRdi) rfl rfl empty data actual
    transition.1 transition.2.1 transition.2.2).success
  rw [contextEq] at performed
  have issued := issue_of_execute physicalLive running
    (related.decode physicalLive logicalLive decoded) performed
  refine ⟨output.memory, issued, ?_⟩
  have queues : pending (TSO.install physical identifier output.memory context false []) =
      pending physical := by
    simpa only [empty] using pending_install_same physicalLive output.memory context false
  change memory = StoreBuffer.view output.memory _
  rw [queues]
  exact congrArg X86.State.memory outputEq

private theorem Rel.advance_correspondence {config : Mutex.Config} {physical : Physical}
    {logical : Logical} {identifier : Nat} {before : TSO.Worker}
    {worker : MutexReplay.Worker} {output : MutexReplay.Result}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    (physicalLive : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some worker)
    (running : before.returned = false)
    (advanced : MutexReplay.advance logical identifier worker = .ok output) :
    ∃ result, TSO.issue physical identifier = .ok result ∧
      IssueResult config physical logical identifier result := by
  have unfinished := MutexReplay.advance_unfinished _ _ _ _ advanced
  have contexts := (related.match_workers physicalLive logicalLive).1
  have operands := related.operands physicalLive logicalLive unfinished
  obtain ⟨_, operation, selected, performed, _⟩ := MutexReplay.advance_ok _ _ _ _ advanced
  have full := MutexReplay.perform_refines _ _ _ _ _ performed
  cases MutexReplay.perform_effect _ _ _ _ _ performed with
  | plain instruction context ran =>
    obtain ⟨_, decoded, _, _⟩ := MutexReplay.runNext_ok _ _ _ _ ran
    rw [step_eq_executeInstruction _ _ decoded] at full
    change executeInstruction (MachineThreads.contextState worker.context (logicalMemory logical))
      instruction.instruction = .ok (.next
        (MachineThreads.contextState context (logicalMemory logical))) at full
    have executed : executeInstruction (TSO.localState physical before) instruction.instruction =
        .ok (.next (MachineThreads.contextState context
          (StoreBuffer.view physical.memory before.buffer))) := by
      have transported := X86.execute_contextOnly_memory _ _
        (StoreBuffer.view physical.memory before.buffer) instruction.instruction
        (plain_contextOnly instruction) full
      simpa only [TSO.localState, MachineThreads.contextState, contexts] using transported
    have effect := (TSO.ExecuteEffect.ordinary (state := physical) (identifier := identifier)
      (worker := before) (instruction := instruction.instruction)
      (plain_no_store before.context instruction) (plain_unlocked instruction)
      (by intro address found; simp [plain_no_load] at found)
      executed rfl).success
    have issued := issue_of_execute physicalLive running
      (related.decode physicalLive logicalLive decoded) effect
    refine ⟨_, issued, related.advance_issue_result closed physicalLive logicalLive advanced
      (related.payloads before (List.mem_of_getElem? physicalLive))
      (related.unguarded identifier before worker physicalLive logicalLive) ?_ issued⟩
    change logicalMemory logical = overlay
      (TSO.install physical identifier physical.memory context false before.buffer)
    rw [overlay_install_same physicalLive]
    exact related.memory
  | load guard record value context authorized operand loaded ran =>
    have held := action_load_guard selected
    have viewEq := related.guarded_view physicalLive logicalLive held
    obtain ⟨_, decoded, _, _⟩ := MutexReplay.runNext_ok _ _ _ _ ran
    rw [step_eq_executeInstruction _ _ decoded] at full
    change executeInstruction (MachineThreads.contextState worker.context (logicalMemory logical))
      .loadEaxRsi = .ok (.next
        (MachineThreads.contextState context (logicalMemory logical))) at full
    have executed : executeInstruction (TSO.localState physical before) .loadEaxRsi =
        .ok (.next (MachineThreads.contextState context
          (StoreBuffer.view physical.memory before.buffer))) := by
      simpa only [TSO.localState, contexts, ← viewEq] using full
    have effect := (TSO.ExecuteEffect.ordinary (state := physical) (identifier := identifier)
      (worker := before) (instruction := .loadEaxRsi) rfl rfl
      (by
        intro address found
        simp only [TSO.loadAddress, Option.some.injEq] at found
        rw [← found, operands.2.1]
        exact related.profile.payload)
      executed rfl).success
    have issued := issue_of_execute physicalLive running
      (related.decode physicalLive logicalLive decoded) effect
    refine ⟨_, issued, related.advance_issue_result closed physicalLive logicalLive advanced
      (related.payloads before (List.mem_of_getElem? physicalLive))
      (related.unguarded identifier before worker physicalLive logicalLive) ?_ issued⟩
    change logicalMemory logical = overlay
      (TSO.install physical identifier physical.memory context false before.buffer)
    rw [overlay_install_same physicalLive]
    exact related.memory
  | store guard record after context authorized operand stored ran =>
    have held := action_store_guard selected
    have peers := related.peers_empty logicalLive held
    obtain ⟨_, decoded, _, _⟩ := MutexReplay.runNext_ok _ _ _ _ ran
    rw [step_eq_executeInstruction _ _ decoded] at full
    change executeInstruction (MachineThreads.contextState worker.context (logicalMemory logical))
      .storeEaxRsi = .ok (.next (MachineThreads.contextState context
        (AddressSpace.toMemory after.shared.resources.space))) at full
    have exactStore := (executeInstruction_storeIntent_next_iff
      (initial := MachineThreads.contextState worker.context (logicalMemory logical))
      (instruction := .storeEaxRsi) (address := worker.context.registers .rsi)
      (value := (worker.context.registers .rax).setWidth 32) rfl).mp full
    have writable : canStoreDWord physical.memory (before.context.registers .rsi) = true := by
      rw [contexts, ← related.canStore]
      exact exactStore.1
    have contextEq : context = MutexReplay.storedContext before.context := by
      have same := congrArg Threads.Context.ofState exactStore.2
      simpa only [Threads.Context.ofState, MachineThreads.contextState,
        MutexReplay.storedContext, contexts] using same
    have executed := execute_store_exact before.context physical.memory writable
    rw [← contextEq] at executed
    have aligned : atomicAddressable (before.context.registers .rsi) = true := by
      rw [operands.2.1]
      exact related.profile.payload
    have data : TSO.dataOnly physical.memory (before.context.registers .rsi) = true := by
      rw [operands.2.1]
      exact related.profile.payloadData
    have effect : TSO.execute physical identifier before .storeEaxRsi = .ok
        (TSO.install physical identifier physical.memory context false
          (StoreBuffer.enqueue before.buffer
            ⟨before.context.registers .rsi, (before.context.registers .rax).setWidth 32⟩),
          .retired identifier none) := by
      simp only [TSO.execute, TSO.pendingStore, aligned, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, data, executed, TSO.sharedState, Except.mapError, ok_bind, pure_ok]
      rfl
    have issued := issue_of_execute physicalLive running
      (related.decode physicalLive logicalLive decoded) effect
    refine ⟨_, issued, related.advance_issue_result closed physicalLive logicalLive advanced
      ?_ ?_ ?_ issued⟩
    · intro store member
      rcases List.mem_append.mp member with previous | newest
      · exact related.payloads before (List.mem_of_getElem? physicalLive) store previous
      · have same := List.mem_singleton.mp newest
        subst store
        exact operands.2.1
    · intro free
      rw [held] at free
      cases free
    · rw [overlay_install_enqueue physicalLive peers, ← related.memory]
      have memoryEq := congrArg X86.State.memory exactStore.2
      simpa only [MachineThreads.contextState, logicalMemory, contexts] using memoryEq
  | acquire record attempt context found operand replacement acquired ran =>
    have free := MutexReplay.action_acquire_none worker selected
    have empty := related.unguarded identifier before worker physicalLive logicalLive free
    obtain ⟨_, decoded, _, _⟩ := MutexReplay.runAtomic_ok _ _ _ _ ran
    rw [step_eq_executeInstruction _ _ decoded] at full
    change executeInstruction (MachineThreads.contextState worker.context (logicalMemory logical))
      .exchangeEaxRdi = .ok (.atomic attempt.event (MachineThreads.contextState context
        (AddressSpace.toMemory attempt.state.shared.resources.space))) at full
    obtain ⟨memory, issued, memoryEq⟩ := related.exchange_issue physicalLive logicalLive
      running unfinished empty decoded full
    refine ⟨_, issued, related.advance_issue_result closed physicalLive logicalLive advanced
      (by intro store member; simp at member) (by intro _; rfl) memoryEq issued⟩
  | release guard record released context authorized operand replacement finished ran =>
    obtain ⟨_, decoded, _, _⟩ := MutexReplay.runAtomic_ok _ _ _ _ ran
    by_cases empty : before.buffer = []
    · rw [step_eq_executeInstruction _ _ decoded] at full
      change executeInstruction (MachineThreads.contextState worker.context (logicalMemory logical))
        .exchangeEaxRdi = .ok (.atomic released.2 (MachineThreads.contextState context
          (AddressSpace.toMemory released.1.shared.resources.space))) at full
      obtain ⟨memory, issued, memoryEq⟩ := related.exchange_issue physicalLive logicalLive
        running unfinished empty decoded full
      refine ⟨_, issued, related.advance_issue_result closed physicalLive logicalLive advanced
        (by intro store member; simp at member) (by intro _; rfl) memoryEq issued⟩
    · have effect := (TSO.ExecuteEffect.blocked (state := physical) (identifier := identifier)
        (worker := before) (instruction := .exchangeEaxRdi) rfl rfl empty).success
      have issued := issue_of_execute physicalLive running
        (related.decode physicalLive logicalLive decoded) effect
      exact ⟨_, issued, .blocked related⟩
  | ret context ran =>
    have returning : worker.phase = .returning := by
      cases phase : worker.phase <;> cases guard : worker.guard <;>
        simp_all [MutexReplay.action]
    have free : worker.guard = none := by
      have control : worker.guard = none ∧ worker.context.registers .rax = 0 := by
        simpa only [MutexReplay.Control, returning] using
          (related.invariant.workers identifier worker logicalLive).control
      exact control.1
    have empty := related.unguarded identifier before worker physicalLive logicalLive free
    have executable := related.ready identifier worker logicalLive
    have logicalRead : readWord (logicalMemory logical) (worker.context.registers .rsp) =
        .ok worker.returnAddress := by
      have fields := MutexReplay.contextValid_fields worker
        (related.invariant.workers identifier worker logicalLive).context unfinished
      rw [fields.2.2.1]
      exact executable.stack
    have physicalRead : readWord (StoreBuffer.view physical.memory before.buffer)
        (before.context.registers .rsp) = .ok worker.returnAddress := by
      rw [operands.2.2]
      exact related.stack_local logicalLive physicalLive
    obtain ⟨_, decoded, _, _⟩ := MutexReplay.runReturn_ok _ _ _ ran
    rw [step_eq_executeInstruction _ _ decoded] at full
    change executeInstruction (MachineThreads.contextState worker.context (logicalMemory logical))
      .ret = .ok (.returned (MachineThreads.contextState context (logicalMemory logical))) at full
    have exactLogical := execute_ret_exact worker.context (logicalMemory logical)
      worker.returnAddress logicalRead executable.canonical
    have contextEq : context = MutexReplay.returnedContext before.context worker.returnAddress := by
      have same := congrArg Threads.Context.ofState
        (StepResult.returned.inj (Except.ok.inj (full.symm.trans exactLogical)))
      simpa only [MachineThreads.contextState, Threads.Context.ofState, contexts] using same
    have executed := execute_ret_exact before.context
      (StoreBuffer.view physical.memory before.buffer) worker.returnAddress
      physicalRead executable.canonical
    rw [← contextEq] at executed
    have effect := (TSO.ExecuteEffect.returned (state := physical) (identifier := identifier)
      (worker := before) (instruction := .ret) rfl rfl rfl executed rfl).success
    have issued := issue_of_execute physicalLive running
      (related.decode physicalLive logicalLive decoded) effect
    refine ⟨_, issued, related.advance_issue_result closed physicalLive logicalLive advanced
      (related.payloads before (List.mem_of_getElem? physicalLive))
      (related.unguarded identifier before worker physicalLive logicalLive) ?_ issued⟩
    change logicalMemory logical = overlay
      (TSO.install physical identifier physical.memory context true before.buffer)
    rw [overlay_install_same physicalLive]
    exact related.memory

/-- Forward enabledness and simulation for every actual live, unreturned
selection. Replay success is constructed from the current invariant and
readiness before any physical execution or lifting premise is used. -/
theorem issue_correspondence {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    {identifier : Nat} {before : TSO.Worker}
    (live : physical.workers[identifier]? = some before) (running : before.returned = false) :
    ∃ result, TSO.issue physical identifier = .ok result ∧
      IssueResult config physical logical identifier result := by
  obtain ⟨worker, logicalLive, _, _⟩ := related.physical_live live
  have unfinished := related.unfinished live logicalLive running
  obtain ⟨logicalResult, checked⟩ := MutexReplay.dispatch_enabled logical config identifier worker
    related.invariant related.ready logicalLive unfinished
  obtain ⟨selected, output, selectedLive, advanced, _⟩ :=
    MutexReplay.dispatch_ok _ _ _ checked
  have same := Option.some.inj (selectedLive.symm.trans logicalLive)
  subst selected
  exact related.advance_correspondence closed live logicalLive running advanced

/-- Every live unreturned worker can issue. A release whose own FIFO is still
nonempty succeeds with the runtime's actual blocked observation. -/
theorem issue_enabled {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    {identifier : Nat} {before : TSO.Worker}
    (live : physical.workers[identifier]? = some before) (running : before.returned = false) :
    ∃ result, TSO.issue physical identifier = .ok result := by
  obtain ⟨result, issued, _⟩ := issue_correspondence related closed live running
  exact ⟨result, issued⟩

/-- An arbitrary successful actual issue has the forward-constructed result,
by determinism. No replay success, payload endpoint, or expected-code gate is
an input to this inversion theorem. -/
theorem issue_lifts {config : Mutex.Config} {physical : Physical} {logical : Logical}
    (related : Rel config physical logical) (closed : MutexReplay.ClosedUnderTwo config)
    {identifier : Nat} {result : Physical × TSO.Observation}
    (success : TSO.issue physical identifier = .ok result) :
    IssueResult config physical logical identifier result := by
  obtain ⟨worker, _, live, running, _, _, _⟩ := TSO.issue_effect _ _ _ success
  obtain ⟨actual, issued, lifted⟩ := issue_correspondence related closed live running
  have same := Except.ok.inj (issued.symm.trans success)
  exact same ▸ lifted

/-- An empty own queue permits a retirement even while another holder has
pending payload writes. RET emptiness follows from the fixed control invariant;
the generic runtime's RET instruction itself performs no flushing. -/
theorem issue_retiring_if_own_empty {config : Mutex.Config} {physical : Physical}
    {logical : Logical} (related : Rel config physical logical)
    (closed : MutexReplay.ClosedUnderTwo config) {identifier : Nat} {before : TSO.Worker}
    (live : physical.workers[identifier]? = some before) (running : before.returned = false)
    (empty : before.buffer = []) :
    ∃ after logicalAfter event,
      TSO.issue physical identifier = .ok (after, .retired identifier event) ∧
      MutexReplay.dispatch logical identifier = .ok (logicalAfter, event) ∧
      Rel config after logicalAfter := by
  obtain ⟨result, issued, lifted⟩ := issue_correspondence related closed live running
  cases lifted with
  | blocked _ =>
    obtain ⟨worker, _, found, _, _, _, nonempty, _, _⟩ := TSO.issue_blocked_effect issued
    have same := Option.some.inj (found.symm.trans live)
    subst worker
    exact False.elim (nonempty empty)
  | retired checked afterRelated => exact ⟨_, _, _, issued, checked, afterRelated⟩

end EDSL.OS.MutexTSO

#audit_edsl
