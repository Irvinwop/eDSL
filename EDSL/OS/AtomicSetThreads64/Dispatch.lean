/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicSetThreads64.Resources
import EDSL.OS.Atomics64.LogicalMachine

namespace EDSL.OS.AtomicSetThreads64
open X86 AddressSpace

theorem logical_context (context : Context) (before after : Space) (value : Word) (af : Bool) :
    Threads.Context.ofState (LockedSet64.afterLogical (context.snapshot before)
      (toMemory after) value af) = applied context value af := rfl

/-- The retained caller slot is read in the current space, independently of
any earlier own or peer atomic event. -/
theorem WorkerValid.running_ret_step {shared identifier worker}
    (valid : WorkerValid shared identifier worker) (running : worker.phase = .running)
    (terminal : worker.cursor = worker.operations.length) (af : Bool) :
    LockedSet64.step af (worker.context.snapshot shared.legacy.shared.resources.space) =
      .ok ⟨.returned ((returned worker.context worker.returnAddress).snapshot
        shared.legacy.shared.resources.space), [.stack8 (worker.context.registers .rsp)]⟩ := by
  have read : readWord (toMemory shared.legacy.shared.resources.space)
      (worker.context.registers .rsp) = .ok worker.returnAddress := by
    rw [valid.running_registers running]
    exact valid.target
  rw [LockedSet64.step_eq_execute af (valid.running_ret_decode running terminal)]
  simpa only [Threads.Context.snapshot, returned, X86.State.writeRegister] using
    LockedSet64.execute_ret_context (worker.context.snapshot shared.legacy.shared.resources.space)
      worker.returnAddress af read valid.canonical

theorem dispatch_logical (state : State) (identifier : Nat) (worker : Worker) (af : Bool)
    (op : Sequential.LogicalOp) (updated : Atomics64.State × Atomics64.Event)
    (live : state.workers identifier = some worker) (valid : WellFormed state)
    (running : worker.phase = .running) (selected : worker.operations[worker.cursor]? = some op)
    (changed : Atomics64.logicalUpdate op state.shared (principal identifier) worker.handle
      (worker.context.registers .rsi) = .ok updated) :
    dispatch state identifier af = .ok
      ({ replace state identifier (some { worker with
        context := applied worker.context updated.2.logical.event.after af,
        cursor := worker.cursor + 1, events := worker.events ++ [updated.2] }) with
        shared := updated.1 }, some updated.2) := by
  have workerValid := (valid.2 _ _ live).2
  obtain ⟨handle, cell, authorized, address, _⟩ := workerValid.authorized valid.1
  have operand : worker.context.registers .rdi = cell.address := by
    rw [workerValid.running_registers running]
    exact address.symm
  have decoded := workerValid.running_logical_decode running selected
  have instruction := Atomics64.logicalUpdate_step op state.shared (principal identifier)
    worker.handle (worker.context.registers .rsi) updated handle cell
    (worker.context.snapshot state.shared.legacy.shared.resources.space) af changed authorized
    rfl operand rfl decoded
  simp [dispatch, live, running, decoded, authorized, operand, changed, instruction,
    logical_context, Except.mapError]

theorem dispatch_returning (state : State) (identifier : Nat) (worker : Worker) (af : Bool)
    (live : state.workers identifier = some worker) (valid : WorkerValid state.shared identifier worker)
    (running : worker.phase = .running) (terminal : worker.cursor = worker.operations.length) :
    dispatch state identifier af = .ok (replace state identifier
      (some { worker with context := returned worker.context worker.returnAddress, phase := .completed }), none) := by
  simp [dispatch, live, running, valid.running_ret_decode running terminal,
    valid.running_ret_step running terminal af, Except.mapError]

theorem dispatch_completed (state : State) (identifier : Nat) (worker : Worker) (af : Bool)
    (live : state.workers identifier = some worker) (completed : worker.phase = .completed) :
    dispatch state identifier af = .error .alreadyCompleted := by
  simp [dispatch, live, completed]

/-- Inversion records the actual body operation and the supplied AF choice.
It relates single current-memory instructions, never isolated worker runs. -/
inductive DispatchEffect (state : State) (identifier : Nat) (af : Bool) (worker : Worker) :
    State × Option Atomics64.Event → Prop where
  | logical {op updated} (running : worker.phase = .running)
      (selected : worker.operations[worker.cursor]? = some op)
      (changed : Atomics64.logicalUpdate op state.shared (principal identifier) worker.handle
        (worker.context.registers .rsi) = .ok updated) :
      DispatchEffect state identifier af worker
        ({ replace state identifier (some { worker with
          context := applied worker.context updated.2.logical.event.after af,
          cursor := worker.cursor + 1, events := worker.events ++ [updated.2] }) with
          shared := updated.1 }, some updated.2)
  | returning (running : worker.phase = .running)
      (terminal : worker.cursor = worker.operations.length) :
      DispatchEffect state identifier af worker (replace state identifier
        (some { worker with context := returned worker.context worker.returnAddress, phase := .completed }), none)

theorem dispatch_effect (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) :
    ∃ worker, state.workers identifier = some worker ∧ DispatchEffect state identifier af worker result := by
  cases live : state.workers identifier with
  | none => simp [dispatch, live] at success
  | some worker =>
    have workerValid := (valid.2 _ _ live).2
    refine ⟨worker, rfl, ?_⟩
    cases running : worker.phase with
    | completed => rw [dispatch_completed _ _ _ _ live running] at success; cases success
    | running =>
      by_cases continuing : worker.cursor < worker.operations.length
      · have selected : worker.operations[worker.cursor]? = some worker.operations[worker.cursor] :=
          List.getElem?_eq_getElem continuing
        obtain ⟨handle, cell, authorized, address, _⟩ := workerValid.authorized valid.1
        have operand : worker.context.registers .rdi = cell.address := by
          rw [workerValid.running_registers running]; exact address.symm
        obtain ⟨updated, changed, _⟩ := Atomics64.logicalUpdate_step_enabled _ state.shared
          (principal identifier) worker.handle (worker.context.registers .rsi) handle cell
          (worker.context.snapshot state.shared.legacy.shared.resources.space) af valid.1 authorized
          rfl operand rfl (workerValid.running_logical_decode running selected)
        have same := Except.ok.inj (success.symm.trans
          (dispatch_logical _ _ _ _ _ _ live valid running selected changed))
        rw [same]
        exact .logical running selected changed
      · have terminal : worker.cursor = worker.operations.length := by
          have := workerValid.phase.bound; omega
        have same := Except.ok.inj (success.symm.trans
          (dispatch_returning _ _ _ _ live workerValid running terminal))
        rw [same]
        exact .returning running terminal

/-- Present current authority/code/stack construct success for either AF. -/
theorem dispatch_enabled (state : State) (identifier : Nat) (worker : Worker) (af : Bool)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (running : worker.phase = .running) :
    ∃ result, dispatch state identifier af = .ok result := by
  have workerValid := (valid.2 _ _ live).2
  by_cases continuing : worker.cursor < worker.operations.length
  · have selected : worker.operations[worker.cursor]? = some worker.operations[worker.cursor] :=
      List.getElem?_eq_getElem continuing
    obtain ⟨handle, cell, authorized, _, _⟩ := workerValid.authorized valid.1
    obtain ⟨updated, changed⟩ := Atomics64.logicalUpdate_enabled _ _ _ _
      (worker.context.registers .rsi) handle cell valid.1 authorized
    exact ⟨_, dispatch_logical _ _ _ _ _ _ live valid running selected changed⟩
  · have terminal : worker.cursor = worker.operations.length := by
      have := workerValid.phase.bound; omega
    exact ⟨_, dispatch_returning _ _ _ _ live workerValid running terminal⟩


theorem WorkerValid.with_logical {shared identifier worker op event}
    (valid : WorkerValid shared identifier worker) (running : worker.phase = .running)
    (selected : worker.operations[worker.cursor]? = some op)
    (tag : event.logical.op = op) (actor : event.actor = principal identifier)
    (handle : event.handle = worker.handle) (cell : event.cell = worker.cell)
    (address : event.logical.event.address = worker.entry.registers .rdi)
    (mask : event.logical.mask = worker.entry.registers .rsi) (af : Bool) :
    WorkerValid shared identifier { worker with
      context := applied worker.context event.logical.event.after af,
      cursor := worker.cursor + 1, events := worker.events ++ [event] } := by
  have continuing := (List.getElem?_eq_some_iff.mp selected).1
  have chain := valid.phase.shape
  rw [running] at chain
  refine ⟨valid.parent, valid.handle, valid.code, valid.stack, valid.distinct, valid.layout,
    valid.executable, valid.target, valid.canonical, valid.stackBound, valid.postStackCanonical,
    ?_, ?_⟩
  · intro offset actual present
    change (worker.events ++ [event])[offset]? = some actual at present
    by_cases earlier : offset < worker.events.length
    · rw [List.getElem?_append_left earlier] at present
      exact valid.captured _ _ present
    · rw [List.getElem?_append_right (by omega)] at present
      have atLast : offset = worker.events.length := by
        have bound := (List.getElem?_eq_some_iff.mp present).1
        simp only [List.length_singleton] at bound
        omega
      rw [atLast, Nat.sub_self] at present
      simp only [List.getElem?_cons_zero, Option.some.injEq] at present
      subst actual
      exact ⟨by simpa only [atLast, ← valid.phase.counted, tag] using selected,
        actor, handle, cell, address, mask⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa only [List.length_append, List.length_singleton] using
        congrArg (fun count => count + 1) valid.phase.counted
    · exact continuing
    · simp only [running]
      exact .snoc chain event af

theorem WorkerValid.with_completed {shared identifier worker}
    (valid : WorkerValid shared identifier worker) (running : worker.phase = .running)
    (terminal : worker.cursor = worker.operations.length) :
    WorkerValid shared identifier { worker with
      context := returned worker.context worker.returnAddress, phase := .completed } := by
  have chain := valid.phase.shape
  rw [running] at chain
  exact ⟨valid.parent, valid.handle, valid.code, valid.stack, valid.distinct, valid.layout,
    valid.executable, valid.target, valid.canonical, valid.stackBound, valid.postStackCanonical,
    valid.captured, valid.phase.counted, valid.phase.bound, terminal, worker.context, chain, rfl⟩

/-- Generic current-RAM updates frame every worker through borrowing history.
The selected worker then extends its private event/context prefix exactly once. -/
theorem dispatch_wellFormed (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) : WellFormed result.1 := by
  obtain ⟨worker, found, effect⟩ := dispatch_effect _ _ _ _ valid success
  have workerValid := (valid.2 _ _ found).2
  cases effect with
  | returning running terminal =>
    refine ⟨valid.1, ?_⟩
    intro query current live
    by_cases selected : query = identifier
    · subst query
      simp [replace] at live
      subst current
      exact ⟨(valid.2 _ _ found).1, workerValid.with_completed running terminal⟩
    · exact valid.2 _ _ (by simpa [replace, selected] using live)
  | @logical op updated running selected changed =>
    have sound := Atomics64.logicalUpdate_sound _ _ _ _ _ _ changed
    obtain ⟨handle, cell, authorized, address, link⟩ := workerValid.authorized valid.1
    have identity := Atomics64.logicalUpdate_identity _ _ _ _ _ _ _ _ changed authorized
    have frame : ∀ query peer, state.workers query = some peer → WorkerValid updated.1 query peer := by
      intro query peer live
      exact ((valid.2 _ _ live).2).after_logicalUpdate valid.1 _ _ _ _ _ changed
    refine ⟨Atomics64.logicalUpdate_wellFormed _ _ _ _ _ _ valid.1 changed, ?_⟩
    intro query current live
    by_cases own : query = identifier
    · subst query
      simp [replace] at live
      subst current
      refine ⟨(valid.2 _ _ found).1, (frame identifier worker found).with_logical running selected
        sound.2.1 sound.2.2.2.2.1 sound.2.2.2.2.2 (identity.1.trans link)
        (identity.2.trans address) ?_ af⟩
      exact sound.2.2.1.trans (congrFun (workerValid.running_registers running) .rsi)
    · have beforeAt : state.workers query = some current := by simpa [replace, own] using live
      exact ⟨(valid.2 _ _ beforeAt).1, frame query current beforeAt⟩

theorem dispatch_frame (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) :
    result.1.nextThread = state.nextThread ∧
      ∀ query, query ≠ identifier → result.1.workers query = state.workers query := by
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect <;> exact ⟨rfl, fun query different => by simp [replace, different]⟩

theorem dispatch_keeps (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) :
    result.1.shared.handles = state.shared.handles ∧ result.1.shared.cells = state.shared.cells ∧
      result.1.shared.legacy.shared.loans = state.shared.legacy.shared.loans := by
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | returning _ _ => exact ⟨rfl, rfl, rfl⟩
  | logical _ _ changed =>
    have effect := Atomics64.logicalUpdate_effect _ _ _ _ _ _ changed
    exact ⟨effect.handles, effect.cells, effect.shared.loans⟩

theorem dispatch_borrowing (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) :
    Borrowing.History state.shared.legacy.shared result.1.shared.legacy.shared := by
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | returning _ _ => exact .refl
  | logical _ _ changed => exact logicalUpdate_borrowing _ _ _ _ _ _ changed

theorem dispatch_advances (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) :
    Atomics64.Advances state.shared result.1.shared := by
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | returning _ _ => exact .refl _
  | logical _ _ changed => exact Atomics64.logicalUpdate_advances _ _ _ _ _ _ changed

theorem dispatch_return_shared (state : State) (identifier : Nat) (af : Bool) (after : State)
    (valid : WellFormed state) (success : dispatch state identifier af = .ok (after, none)) :
    after.shared = state.shared := by
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect
  rfl

theorem dispatch_atomic_operation (state : State) (identifier : Nat) (af : Bool)
    (after : State) (event : Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok (after, some event)) :
    ∃ worker op, state.workers identifier = some worker ∧ worker.phase = .running ∧
      worker.operations[worker.cursor]? = some op ∧
      LockedSet64.decodeAt (worker.context.snapshot state.shared.legacy.shared.resources.space) =
        .ok (.logicalRdiRsi op) ∧
      Atomics64.logicalUpdate op state.shared (principal identifier) worker.handle
        (worker.context.registers .rsi) = .ok (after.shared, event) := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | logical running selected changed =>
    exact ⟨worker, _, live, running, selected,
      ((valid.2 _ _ live).2).running_logical_decode running selected, changed⟩

theorem dispatch_rank (state : State) (identifier query : Nat) (af : Bool) (worker : Worker)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : dispatch state identifier af = .ok result) :
    ∃ current, result.1.workers query = some current ∧
      current.rank + (if identifier = query then 1 else 0) = worker.rank := by
  by_cases own : identifier = query
  · subst identifier
    obtain ⟨actual, found, effect⟩ := dispatch_effect _ _ _ _ valid success
    have same := Option.some.inj (found.symm.trans live)
    subst actual
    cases effect with
    | @logical op updated running selected _ =>
      have continuing := (List.getElem?_eq_some_iff.mp selected).1
      refine ⟨{ worker with
        context := applied worker.context updated.2.logical.event.after af,
        cursor := worker.cursor + 1, events := worker.events ++ [updated.2] }, by simp [replace], ?_⟩
      simp only [Worker.rank, running, ↓reduceIte]
      omega
    | returning running terminal =>
      refine ⟨{ worker with
        context := returned worker.context worker.returnAddress,
        phase := .completed }, by simp [replace], ?_⟩
      simp [Worker.rank, running, terminal]
  · exact ⟨worker, ((dispatch_frame _ _ _ _ valid success).2 query (Ne.symm own)).trans live,
      by simp [own]⟩


/-- Event identity and current-before/readback come from the same checked
operation that actually dispatched. No captured after-word is asserted current
at a later scheduling position. -/
theorem dispatch_atomic_spec (state : State) (identifier : Nat) (af : Bool)
    (after : State) (event : Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok (after, some event)) :
    ∃ worker current op, state.workers identifier = some worker ∧
      after.workers identifier = some current ∧ worker.phase = .running ∧
      worker.operations[worker.cursor]? = some op ∧
      event.actor = principal identifier ∧ event.handle = worker.handle ∧ event.cell = worker.cell ∧
      event.logical.op = op ∧ event.logical.mask = worker.entry.registers .rsi ∧
      event.logical.event.address = worker.entry.registers .rdi ∧
      event.logical.event.after = op.eval event.logical.event.before (worker.entry.registers .rsi) ∧
      loadQWord (toMemory state.shared.legacy.shared.resources.space) event.logical.event.address =
        .ok event.logical.event.before ∧
      loadQWord (toMemory after.shared.legacy.shared.resources.space) event.logical.event.address =
        .ok event.logical.event.after ∧
      current.events = worker.events ++ [event] ∧ current.cursor = worker.cursor + 1 ∧
      current.context = applied worker.context event.logical.event.after af ∧
      current.phase = .running := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | @logical op updated running selected changed =>
    have sound := Atomics64.logicalUpdate_sound _ _ _ _ _ _ changed
    have workerValid := (valid.2 _ _ live).2
    obtain ⟨handle, cell, authorized, address, link⟩ := workerValid.authorized valid.1
    have identity := Atomics64.logicalUpdate_identity _ _ _ _ _ _ _ _ changed authorized
    have registers := workerValid.running_registers running
    refine ⟨worker, { worker with
      context := applied worker.context updated.2.logical.event.after af,
      cursor := worker.cursor + 1, events := worker.events ++ [updated.2] }, op,
      live, by simp [replace], running, selected, sound.2.2.2.2.1, sound.2.2.2.2.2,
      identity.1.trans link, sound.2.1, sound.2.2.1.trans (congrFun registers .rsi),
      identity.2.trans address, ?_, sound.1.2.2.1, sound.1.readback, rfl, rfl, rfl, running⟩
    simpa only [registers] using sound.2.2.2.1

/-- Actual CPU successor uses the complete checked operation's resulting RAM,
with the selected private context and exact operand footprint. -/
theorem dispatch_atomic_machine (state : State) (identifier : Nat) (af : Bool)
    (after : State) (event : Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok (after, some event)) :
    ∃ worker current, state.workers identifier = some worker ∧
      after.workers identifier = some current ∧
      LockedSet64.step af (worker.context.snapshot state.shared.legacy.shared.resources.space) =
        .ok ⟨.atomic64 event.logical (current.context.snapshot after.shared.legacy.shared.resources.space),
          [.rmw8 (worker.entry.registers .rdi)]⟩ := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | @logical op updated running selected changed =>
    have workerValid := (valid.2 _ _ live).2
    obtain ⟨handle, cell, authorized, address, _⟩ := workerValid.authorized valid.1
    have operand : worker.context.registers .rdi = cell.address := by
      rw [workerValid.running_registers running]; exact address.symm
    refine ⟨worker, { worker with
      context := applied worker.context updated.2.logical.event.after af,
      cursor := worker.cursor + 1, events := worker.events ++ [updated.2] }, live, by simp [replace], ?_⟩
    simpa [address, LockedSet64.afterLogical, Threads.Context.snapshot, applied, replace] using
      Atomics64.logicalUpdate_step op _ _ _ _ _ handle cell
      (worker.context.snapshot state.shared.legacy.shared.resources.space) af changed authorized
      rfl operand rfl (workerValid.running_logical_decode running selected)

/-- Inverting the actual selected CPU step supplies its operation, complete
RMW transition, all GPR/RIP/flags effects and the precise AF choice. -/
theorem dispatch_atomic_cpu_effect (state : State) (identifier : Nat) (af : Bool)
    (after : State) (event : Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok (after, some event)) :
    ∃ worker current op, state.workers identifier = some worker ∧
      after.workers identifier = some current ∧
      LockedSet64.decodeAt (worker.context.snapshot state.shared.legacy.shared.resources.space) =
        .ok (.logicalRdiRsi op) ∧
      LockedSet64.LogicalEffect op (worker.context.snapshot state.shared.legacy.shared.resources.space)
        af event.logical (current.context.snapshot after.shared.legacy.shared.resources.space) := by
  obtain ⟨worker, current, live, found, machine⟩ := dispatch_atomic_machine _ _ _ _ _ valid success
  obtain ⟨op, decoded, effect, _⟩ := LockedSet64.step_atomic64_sound machine
  exact ⟨worker, current, op, live, found, decoded, effect⟩

/-- RET is fetched and executed at the terminal cursor against CURRENT RAM.
Its stack footprint refers to the original caller slot, advanced exactly once. -/
theorem dispatch_return_machine (state : State) (identifier : Nat) (af : Bool) (after : State)
    (valid : WellFormed state) (success : dispatch state identifier af = .ok (after, none)) :
    ∃ worker, state.workers identifier = some worker ∧ worker.phase = .running ∧
      worker.cursor = worker.operations.length ∧
      after.workers identifier = some { worker with
        context := returned worker.context worker.returnAddress, phase := .completed } ∧
      LockedSet64.decodeAt (worker.context.snapshot state.shared.legacy.shared.resources.space) = .ok .ret ∧
      LockedSet64.step af (worker.context.snapshot state.shared.legacy.shared.resources.space) =
        .ok ⟨.returned ((returned worker.context worker.returnAddress).snapshot
          after.shared.legacy.shared.resources.space), [.stack8 (worker.entry.registers .rsp)]⟩ := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | returning running terminal =>
    have workerValid := (valid.2 _ _ live).2
    refine ⟨worker, live, running, terminal, by simp [replace],
      workerValid.running_ret_decode running terminal, ?_⟩
    simpa only [replace, workerValid.running_registers running] using
      workerValid.running_ret_step running terminal af

/-- Completed workers keep their exact handle and two loans. The full current
shared state, including peer writes, survives the one successful RET. -/
theorem dispatch_return_spec (state : State) (identifier : Nat) (af : Bool) (after : State)
    (valid : WellFormed state) (success : dispatch state identifier af = .ok (after, none)) :
    ∃ worker current, state.workers identifier = some worker ∧
      after.workers identifier = some current ∧ worker.cursor = worker.operations.length ∧
      current.phase = .completed ∧ current.rank = 0 ∧
      current.context.registers .rsp = worker.entry.registers .rsp + 8 ∧
      current.context.rip = worker.returnAddress ∧ current.context.flags = worker.context.flags ∧
      (∀ register, register ≠ .rsp → current.context.registers register = worker.context.registers register) ∧
      current.events = worker.events ∧ current.cursor = worker.cursor ∧
      current.handle = worker.handle ∧ current.codeLoan = worker.codeLoan ∧
      current.stackLoan = worker.stackLoan ∧ WorkerValid after.shared identifier current ∧
      after.shared = state.shared := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | returning running terminal =>
    have workerValid := (valid.2 _ _ live).2
    refine ⟨worker, { worker with
      context := returned worker.context worker.returnAddress, phase := .completed },
      live, by simp [replace], terminal, rfl, rfl, ?_, rfl, rfl, ?_,
      rfl, rfl, rfl, rfl, rfl, workerValid.with_completed running terminal, rfl⟩
    · simp only [returned, ↓reduceIte, workerValid.running_registers running]
    · intro register other
      simp only [returned, other, ↓reduceIte]

/-- A completed worker cannot execute RET a second time or consume another
stack slot; collection is a separate checked lifecycle action. -/
theorem dispatch_return_rejects_repeat (state : State) (identifier : Nat) (af : Bool) (after : State)
    (valid : WellFormed state) (success : dispatch state identifier af = .ok (after, none))
    (nextAF : Bool) : dispatch after identifier nextAF = .error .alreadyCompleted := by
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | returning _ _ => simp [dispatch, replace]

/-- Exact event-prefix append for the selected worker and exact preservation
for every peer, including completed peers that have not yet joined. -/
theorem dispatch_events (state : State) (identifier query : Nat) (af : Bool) (worker : Worker)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (live : state.workers query = some worker) (success : dispatch state identifier af = .ok result) :
    ∃ current, result.1.workers query = some current ∧
      current.events = worker.events ++ (if identifier = query then result.2.toList else []) := by
  by_cases own : identifier = query
  · subst identifier
    obtain ⟨actual, found, effect⟩ := dispatch_effect _ _ _ _ valid success
    have same := Option.some.inj (found.symm.trans live)
    subst actual
    cases effect with
    | @logical op updated _ _ _ =>
      exact ⟨{ worker with
        context := applied worker.context updated.2.logical.event.after af,
        cursor := worker.cursor + 1, events := worker.events ++ [updated.2] },
        by simp [replace], by simp⟩
    | returning _ _ =>
      exact ⟨{ worker with
        context := returned worker.context worker.returnAddress, phase := .completed },
        by simp [replace], by simp⟩
  · exact ⟨worker, ((dispatch_frame _ _ _ _ valid success).2 query (Ne.symm own)).trans live,
      by simp [own]⟩

/-- The peer's entire private worker record survives; current resource validity
is separately transported through the checked generic borrowing history. -/
theorem dispatch_peer (state : State) (identifier query : Nat) (af : Bool) (worker : Worker)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (live : state.workers query = some worker) (different : query ≠ identifier)
    (success : dispatch state identifier af = .ok result) :
    result.1.workers query = some worker ∧ WorkerValid result.1.shared query worker := by
  have found := ((dispatch_frame _ _ _ _ valid success).2 query different).trans live
  have keeps := dispatch_keeps _ _ _ _ valid success
  exact ⟨found, ((valid.2 _ _ live).2).frame valid.1 (dispatch_borrowing _ _ _ _ valid success)
    ⟨congrFun keeps.1 _, congrFun keeps.2.1 _, congrFun keeps.2.2 _, congrFun keeps.2.2 _⟩⟩

/-- Every successful selected instruction has a complete fetch window inside
its original immutable literal extent, even for a RET-only body. -/
theorem dispatch_fetch (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) :
    ∃ worker instruction, state.workers identifier = some worker ∧ worker.phase = .running ∧
      LockedSet64.decodeAt (worker.context.snapshot state.shared.legacy.shared.resources.space) = .ok instruction ∧
      CodeAt (toMemory state.shared.legacy.shared.resources.space) worker.context.rip instruction.bytes ∧
      worker.context.rip = worker.entry.rip + BitVec.ofNat 64 (4 * worker.cursor) ∧
      4 * worker.cursor + instruction.length ≤ worker.bytes.length := by
  obtain ⟨worker, live, effect⟩ := dispatch_effect _ _ _ _ valid success
  have running : worker.phase = .running := by cases effect <;> assumption
  obtain ⟨instruction, decoded, rip, covered⟩ := ((valid.2 _ _ live).2).running_fetch running
  exact ⟨worker, instruction, live, running, decoded, LockedSet64.decodeAt_code decoded, rip, covered⟩


/-- Decoding is tied to the actual bytes at the original cursor, rather than
merely to executable neighboring memory. -/
theorem WorkerValid.running_original_bytes {shared identifier worker instruction}
    (valid : WorkerValid shared identifier worker) (running : worker.phase = .running)
    (decoded : LockedSet64.decodeAt (worker.context.snapshot shared.legacy.shared.resources.space) =
      .ok instruction) :
    ∀ offset byte, instruction.bytes[offset]? = some byte →
      worker.bytes[4 * worker.cursor + offset]? = some byte := by
  intro offset byte present
  rw [valid.layout, ← List.getElem?_drop, bodyBytes_drop _ _ valid.phase.bound]
  by_cases continuing : worker.cursor < worker.operations.length
  · have selected : worker.operations[worker.cursor]? = some worker.operations[worker.cursor] :=
      List.getElem?_eq_getElem continuing
    have same := Except.ok.inj (decoded.symm.trans (valid.running_logical_decode running selected))
    subst instruction
    have tail := List.drop_eq_getElem_cons continuing
    rw [tail, bodyBytes_cons, List.getElem?_append_left]
    · exact present
    · exact (List.getElem?_eq_some_iff.mp present).1
  · have terminal : worker.cursor = worker.operations.length := by
      have := valid.phase.bound; omega
    have same := Except.ok.inj (decoded.symm.trans (valid.running_ret_decode running terminal))
    subst instruction
    rw [terminal, List.drop_length]
    exact present

/-- Every actually fetched instruction byte is inside the original loan's
nonwrapping natural-address interval and has the original literal value. -/
theorem dispatch_fetch_original (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) :
    ∃ worker instruction, state.workers identifier = some worker ∧ worker.phase = .running ∧
      LockedSet64.decodeAt (worker.context.snapshot state.shared.legacy.shared.resources.space) = .ok instruction ∧
      HasLoan state.shared.legacy.shared identifier worker.codeLoan (codeRegion worker.entry worker.bytes) ∧
      4 * worker.cursor + instruction.length ≤ worker.bytes.length ∧
      (∀ offset byte, instruction.bytes[offset]? = some byte →
        worker.bytes[4 * worker.cursor + offset]? = some byte) ∧
      (∀ offset, offset < instruction.length →
        (codeRegion worker.entry worker.bytes).Contains
          (worker.context.rip + BitVec.ofNat 64 offset)) := by
  obtain ⟨worker, instruction, live, running, decoded, _, rip, covered⟩ :=
    dispatch_fetch _ _ _ _ valid success
  have workerValid := (valid.2 _ _ live).2
  refine ⟨worker, instruction, live, running, decoded, workerValid.code, covered,
    workerValid.running_original_bytes running decoded, ?_⟩
  intro offset bound
  have originalBound := workerValid.executable.1
  have small : 4 * worker.cursor + offset < 2^64 := by omega
  have sum : worker.entry.rip.toNat + (4 * worker.cursor + offset) < 2^64 := by omega
  have address : worker.context.rip + BitVec.ofNat 64 offset =
      worker.entry.rip + BitVec.ofNat 64 (4 * worker.cursor + offset) := by
    rw [rip, BitVec.ofNat_add, BitVec.add_assoc]
  rw [address]
  change worker.entry.rip.toNat ≤
      (worker.entry.rip + BitVec.ofNat 64 (4 * worker.cursor + offset)).toNat ∧
    (worker.entry.rip + BitVec.ofNat 64 (4 * worker.cursor + offset)).toNat <
      worker.entry.rip.toNat + worker.bytes.length
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt sum]
  omega

/-- All current loan cells survive mixed decoded updates and RET, including
code and stack loans belonging to unfinished or completed peers. -/
theorem dispatch_loan_contents (state : State) (identifier : Nat) (af : Bool)
    (result : State × Option Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok result) (loanId : Nat) (loan : Borrowing.Loan)
    (live : state.shared.legacy.shared.loans loanId = some loan) :
    result.1.shared.legacy.shared.loans loanId = some loan ∧
      ∀ query, loan.region.Contains query →
        result.1.shared.legacy.shared.resources.space.cells query =
          state.shared.legacy.shared.resources.space.cells query := by
  have kept := ((congrFun (dispatch_keeps _ _ _ _ valid success).2.2 loanId).trans live)
  refine ⟨kept, ?_⟩
  obtain ⟨_, _, effect⟩ := dispatch_effect _ _ _ _ valid success
  cases effect with
  | returning _ _ => exact fun _ _ => rfl
  | logical _ _ changed => exact Atomics64.logicalUpdate_loan_contents _ _ _ _ _ _ valid.1 changed loanId loan live

/-- Every emitted RMW retains all current registries/frontiers, allocation
metadata, permissions and the complete eight-byte store frame. -/
theorem dispatch_atomic_resources (state : State) (identifier : Nat) (af : Bool)
    (after : State) (event : Atomics64.Event) (valid : WellFormed state)
    (success : dispatch state identifier af = .ok (after, some event)) :
    Atomics64.Effect state.shared after.shared event := by
  obtain ⟨_, _, _, _, _, _, changed⟩ := dispatch_atomic_operation _ _ _ _ _ valid success
  exact Atomics64.logicalUpdate_effect _ _ _ _ _ _ changed

theorem dispatch_enabled_wellFormed (state : State) (identifier : Nat) (worker : Worker) (af : Bool)
    (valid : WellFormed state) (live : state.workers identifier = some worker)
    (running : worker.phase = .running) :
    ∃ result, dispatch state identifier af = .ok result ∧ WellFormed result.1 := by
  obtain ⟨result, success⟩ := dispatch_enabled _ _ _ _ valid live running
  exact ⟨result, success, dispatch_wellFormed _ _ _ _ valid success⟩

end EDSL.OS.AtomicSetThreads64
