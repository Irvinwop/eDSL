/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Machine
import EDSL.OS.MutexReplay.Preservation
import EDSL.X86.CodeCheckComplete

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

/-- Assemble the existing checks only after constructing a concrete result and
proving its context and return boundary. -/
private theorem advance_of_perform (state : State) (identifier : Nat) (worker : Worker)
    (operation : Action) (result : Result)
    (before : contextValid worker = true)
    (code : checkCode (toMemory state.shared.shared.resources.space) worker.entry.rip bytes = true)
    (selected : action worker = .ok operation)
    (performed : perform state.shared identifier worker operation = .ok result)
    (after : contextValid (evolved worker result) = true)
    (returned : result.returned = decide ((evolved worker result).phase = .completed)) :
    advance state identifier worker = .ok result := by
  change contextValid { worker with
    context := result.context
    phase := nextPhase worker result
    guard := result.guard } = true at after
  by_cases done : nextPhase worker result = .completed
  · have yes : result.returned = true := by simpa only [evolved, done, decide_true] using returned
    simp only [done] at after
    simp [advance, before, code, selected, performed, after, yes, done]
  · have no : result.returned = false := by simpa only [evolved, done, decide_false] using returned
    simp [advance, before, code, selected, performed, after, no, done]

/-- Fixed-length instructions establish the next RIP using word arithmetic;
this lemma consumes concrete field equalities, not a future context check. -/
private theorem linear_contextValid (worker : Worker) (result : Result) (width : Nat)
    (before : contextValid worker = true) (unfinished : worker.phase ≠ .completed)
    (next : nextPhase worker result ≠ .completed)
    (rdi : result.context.registers .rdi = worker.context.registers .rdi)
    (rsi : result.context.registers .rsi = worker.context.registers .rsi)
    (rsp : result.context.registers .rsp = worker.context.registers .rsp)
    (pc : result.context.rip = worker.context.rip + BitVec.ofNat 64 width)
    (offset : worker.phase.offset + width = (nextPhase worker result).offset) :
    contextValid (evolved worker result) = true := by
  apply contextValid_next _ _ before unfinished next rdi rsi rsp
  rw [pc, (contextValid_fields _ before unfinished).2.2.2, BitVec.add_assoc,
    ← BitVec.ofNat_add, offset]

private theorem perform_plain (shared : Mutex.State) (identifier : Nat) (worker : Worker)
    (instruction : Plain) (output : Context)
    (decoded : decodeAt (worker.context.snapshot shared.shared.resources.space) = .ok instruction.instruction)
    (stepped : X86.step (worker.context.snapshot shared.shared.resources.space) =
      .ok (.next (output.snapshot shared.shared.resources.space))) :
    perform shared identifier worker (.plain instruction) =
      .ok ⟨shared, output, worker.guard, none, false⟩ := by
  have ran := runNext_of_step shared worker.context instruction.instruction _ decoded stepped
  simp only [perform, ran, ok_bind, pure_ok]
  rfl

/-- Every live unfinished worker has a successful next replay instruction.
Readiness concerns only current executable bytes and the retained return word;
protocol success and all post-context checks are proved forwards here. -/
theorem advance_enabled (state : State) (config : Mutex.Config) (identifier : Nat) (worker : Worker)
    (inv : Invariant config state) (ready : ExecutionReady state)
    (live : state.workers[identifier]? = some worker) (unfinished : worker.phase ≠ .completed) :
    ∃ result, advance state identifier worker = .ok result := by
  have privateInv := inv.workers identifier worker live
  have executable := ready identifier worker live
  have checked := checkCode_complete _ _ _ executable.code
  have fields := contextValid_fields worker privateInv.context unfinished
  have rdi : worker.context.registers .rdi = config.lockAddress :=
    fields.1.trans privateInv.operands.1
  have rsi : worker.context.registers .rsi = config.dataAddress :=
    fields.2.1.trans privateInv.operands.2
  cases phase : worker.phase with
  | entry =>
    let result : Result := ⟨state.shared, immediateContext worker.context 1, worker.guard, none, false⟩
    have decoded := decode_expected _ _ (.mov32 .rax 1) privateInv.context executable.code
      (by simp [expected, phase])
    have stepped := immediate_step _ _ 1 privateInv.context executable.code (by simp [expected, phase])
    have performed : perform state.shared identifier worker (.plain (.immediate 1)) = .ok result :=
      perform_plain _ _ _ (.immediate 1) _ decoded stepped
    have after : contextValid (evolved worker result) = true := by
      apply linear_contextValid worker result 5 privateInv.context unfinished
      · simp [nextPhase, phase]
      · simp [result, immediateContext]
      · simp [result, immediateContext]
      · simp [result, immediateContext]
      · rfl
      · simp [nextPhase, phase, Phase.offset]
    refine ⟨result, advance_of_perform state identifier worker (.plain (.immediate 1)) result privateInv.context checked
      (by simp [action, phase]) performed after ?_⟩
    simp [result, evolved, nextPhase, phase]
  | acquiring =>
    obtain ⟨record, registered, configEq⟩ := inv.registered
    have protocolRegistered : Mutex.registered state.shared = .ok record := by
      simp [Mutex.registered, registered]
    have control : worker.guard = none ∧ worker.context.registers .rax = 1 := by
      simpa only [Control, phase] using privateInv.control
    obtain ⟨attempt, acquired⟩ := Mutex.tryAcquire_enabled _ (principal identifier) record inv.shared registered
    have decoded := decode_expected _ _ .exchangeEaxRdi privateInv.context executable.code
      (by simp [expected, phase])
    have operand : (worker.context.snapshot state.shared.shared.resources.space).registers .rdi =
        record.config.lockAddress := by simpa only [Threads.Context.snapshot, configEq] using rdi
    have replacement : ((worker.context.snapshot state.shared.shared.resources.space).registers .rax).setWidth 32 = 1 := by
      simp [Threads.Context.snapshot, control.2]
    have stepped := Mutex.tryAcquire_step _ _ _ record _ acquired registered rfl operand replacement decoded
    have ran : runAtomic state.shared worker.context attempt.event =
        .ok (exchangedContext worker.context attempt.event.before) := by
      simpa only [Mutex.afterExchange, Threads.Context.ofState, Threads.Context.snapshot, X86.State.writeRegister,
        exchangedContext] using runAtomic_of_step _ _ _ _ decoded stepped
    let result : Result := ⟨attempt.state, exchangedContext worker.context attempt.event.before,
      attempt.acquired, some attempt.event, false⟩
    have performed : perform state.shared identifier worker .acquire = .ok result := by
      simp [perform, protocolRegistered, configEq, rdi, control.2, acquired, ran, result, Except.mapError]
    have after : contextValid (evolved worker result) = true := by
      apply linear_contextValid worker result 2 privateInv.context unfinished
      · simp [nextPhase, phase]
      · simp [result, exchangedContext]
      · simp [result, exchangedContext]
      · simp [result, exchangedContext]
      · rfl
      · simp [nextPhase, phase, Phase.offset]
    refine ⟨result, advance_of_perform state identifier worker .acquire result privateInv.context checked
      (by simp [action, phase, control.1]) performed after ?_⟩
    simp [result, evolved, nextPhase, phase]
  | comparing =>
    let result : Result := ⟨state.shared, compareContext worker.context, worker.guard, none, false⟩
    have decoded := decode_expected _ _ .cmpEaxZero privateInv.context executable.code (by simp [expected, phase])
    have stepped := compare_step _ _ privateInv.context executable.code phase
    have performed : perform state.shared identifier worker (.plain .compare) = .ok result :=
      perform_plain _ _ _ .compare _ decoded stepped
    have after : contextValid (evolved worker result) = true := by
      apply linear_contextValid worker result 3 privateInv.context unfinished
      · simp [nextPhase, phase]
      · simp [result, compareContext]
      · simp [result, compareContext]
      · simp [result, compareContext]
      · rfl
      · simp [nextPhase, phase, Phase.offset]
    refine ⟨result, advance_of_perform state identifier worker (.plain .compare) result privateInv.context checked
      (by simp [action, phase]) performed after ?_⟩
    simp [result, evolved, nextPhase, phase]
  | branching =>
    let result : Result := ⟨state.shared, branchContext worker.context, worker.guard, none, false⟩
    have decoded := decode_expected _ _ (.jnz 0xf4) privateInv.context executable.code (by simp [expected, phase])
    have stepped := branch_step _ _ privateInv.context executable.code phase
    have performed : perform state.shared identifier worker (.plain .branch) = .ok result :=
      perform_plain _ _ _ .branch _ decoded stepped
    have pc : worker.context.rip = worker.entry.rip + 10 := by
      simpa only [phase, Phase.offset, BitVec.ofNat_eq_ofNat] using fields.2.2.2
    have after : contextValid (evolved worker result) = true := by
      cases zero : worker.context.flags.getLsbD 6
      · have target : result.context.rip = worker.entry.rip := by
          simp only [result, branchContext, zero, Bool.false_eq_true, ite_false, pc, branch_backedge]
        have next : nextPhase worker result = .entry := by simp [nextPhase, phase, target]
        apply contextValid_next worker result privateInv.context unfinished (by simp [next])
        · rfl
        · rfl
        · rfl
        · simpa [next, Phase.offset] using target
      · have target : result.context.rip = worker.entry.rip + 12 := by
          simp only [result, branchContext, zero, ite_true, pc, BitVec.add_assoc]
          rfl
        have next : nextPhase worker result = .loading := by
          simp [nextPhase, phase, target]
        apply contextValid_next worker result privateInv.context unfinished (by simp [next])
        · rfl
        · rfl
        · rfl
        · simpa [next, Phase.offset] using target
    refine ⟨result, advance_of_perform state identifier worker (.plain .branch) result privateInv.context checked
      (by simp [action, phase]) performed after ?_⟩
    simp only [result, evolved, nextPhase, phase]
    split <;> rfl
  | loading =>
    have held : worker.guard.isSome = true := by simpa only [Control, phase] using privateInv.control
    obtain ⟨lease, guard⟩ := Option.isSome_iff_exists.mp held
    obtain ⟨record, authorized, configEq⟩ := privateInv.authority lease guard
    obtain ⟨value, loaded⟩ := Mutex.guardLoad_enabled _ _ _ record inv.shared authorized
    have decoded := decode_expected _ _ .loadEaxRsi privateInv.context executable.code (by simp [expected, phase])
    have operand : (worker.context.snapshot state.shared.shared.resources.space).registers .rsi =
        record.config.dataAddress := by simpa only [Threads.Context.snapshot, configEq] using rsi
    have stepped := Mutex.guardLoad_step _ _ _ _ record _ loaded authorized rfl operand decoded
    have ran : runNext state.shared worker.context .loadEaxRsi = .ok (exchangedContext worker.context value) := by
      simpa only [Mutex.afterLoad, Threads.Context.ofState, Threads.Context.snapshot, X86.State.writeRegister,
        exchangedContext] using runNext_of_step _ _ _ _ decoded stepped
    let result : Result := ⟨state.shared, exchangedContext worker.context value, worker.guard, none, false⟩
    have performed : perform state.shared identifier worker (.load lease) = .ok result := by
      simp [perform, authorized, configEq, rsi, loaded, ran, result, Except.mapError]
    have after : contextValid (evolved worker result) = true := by
      apply linear_contextValid worker result 2 privateInv.context unfinished
      · simp [nextPhase, phase]
      · simp [result, exchangedContext]
      · simp [result, exchangedContext]
      · simp [result, exchangedContext]
      · rfl
      · simp [nextPhase, phase, Phase.offset]
    refine ⟨result, advance_of_perform state identifier worker (.load lease) result privateInv.context checked
      (by simp [action, phase, guard]) performed after ?_⟩
    simp [result, evolved, nextPhase, phase]
  | incrementingFirst =>
    let result : Result := ⟨state.shared, incrementContext worker.context, worker.guard, none, false⟩
    have decoded := decode_expected _ _ (.leaEaxRaxDisp8 1) privateInv.context executable.code
      (by simp [expected, phase])
    have stepped := increment_step _ _ privateInv.context executable.code (by simp [expected, phase])
    have performed : perform state.shared identifier worker (.plain .increment) = .ok result :=
      perform_plain _ _ _ .increment _ decoded stepped
    have after : contextValid (evolved worker result) = true := by
      apply linear_contextValid worker result 3 privateInv.context unfinished
      · simp [nextPhase, phase]
      · simp [result, incrementContext]
      · simp [result, incrementContext]
      · simp [result, incrementContext]
      · rfl
      · simp [nextPhase, phase, Phase.offset]
    refine ⟨result, advance_of_perform state identifier worker (.plain .increment) result privateInv.context checked
      (by simp [action, phase]) performed after ?_⟩
    simp [result, evolved, nextPhase, phase]
  | storingFirst =>
    have held : worker.guard.isSome = true := by simpa only [Control, phase] using privateInv.control
    obtain ⟨lease, guard⟩ := Option.isSome_iff_exists.mp held
    obtain ⟨record, authorized, configEq⟩ := privateInv.authority lease guard
    obtain ⟨shared, stored⟩ := Mutex.guardStore_enabled _ _ _ ((worker.context.registers .rax).setWidth 32)
      record inv.shared authorized
    have decoded := decode_expected _ _ .storeEaxRsi privateInv.context executable.code (by simp [expected, phase])
    have operand : (worker.context.snapshot state.shared.shared.resources.space).registers .rsi =
        record.config.dataAddress := by simpa only [Threads.Context.snapshot, configEq] using rsi
    have stepped := Mutex.guardStore_step _ _ _ _ _ record _ stored authorized rfl operand rfl decoded
    have ran : runNext state.shared worker.context .storeEaxRsi = .ok (storedContext worker.context) := by
      simpa only [Mutex.afterStore, Threads.Context.ofState, Threads.Context.snapshot, storedContext] using
        runNext_of_step _ _ _ _ decoded stepped
    let result : Result := ⟨shared, storedContext worker.context, worker.guard, none, false⟩
    have performed : perform state.shared identifier worker (.store lease) = .ok result := by
      simp [perform, authorized, configEq, rsi, stored, ran, result, Except.mapError]
    have after : contextValid (evolved worker result) = true := by
      apply linear_contextValid worker result 2 privateInv.context unfinished
      · simp [nextPhase, phase]
      · simp [result, storedContext]
      · simp [result, storedContext]
      · simp [result, storedContext]
      · rfl
      · simp [nextPhase, phase, Phase.offset]
    refine ⟨result, advance_of_perform state identifier worker (.store lease) result privateInv.context checked
      (by simp [action, phase, guard]) performed after ?_⟩
    simp [result, evolved, nextPhase, phase]
  | incrementingSecond =>
    let result : Result := ⟨state.shared, incrementContext worker.context, worker.guard, none, false⟩
    have decoded := decode_expected _ _ (.leaEaxRaxDisp8 1) privateInv.context executable.code
      (by simp [expected, phase])
    have stepped := increment_step _ _ privateInv.context executable.code (by simp [expected, phase])
    have performed : perform state.shared identifier worker (.plain .increment) = .ok result :=
      perform_plain _ _ _ .increment _ decoded stepped
    have after : contextValid (evolved worker result) = true := by
      apply linear_contextValid worker result 3 privateInv.context unfinished
      · simp [nextPhase, phase]
      · simp [result, incrementContext]
      · simp [result, incrementContext]
      · simp [result, incrementContext]
      · rfl
      · simp [nextPhase, phase, Phase.offset]
    refine ⟨result, advance_of_perform state identifier worker (.plain .increment) result privateInv.context checked
      (by simp [action, phase]) performed after ?_⟩
    simp [result, evolved, nextPhase, phase]
  | storingSecond =>
    have held : worker.guard.isSome = true := by simpa only [Control, phase] using privateInv.control
    obtain ⟨lease, guard⟩ := Option.isSome_iff_exists.mp held
    obtain ⟨record, authorized, configEq⟩ := privateInv.authority lease guard
    obtain ⟨shared, stored⟩ := Mutex.guardStore_enabled _ _ _ ((worker.context.registers .rax).setWidth 32)
      record inv.shared authorized
    have decoded := decode_expected _ _ .storeEaxRsi privateInv.context executable.code (by simp [expected, phase])
    have operand : (worker.context.snapshot state.shared.shared.resources.space).registers .rsi =
        record.config.dataAddress := by simpa only [Threads.Context.snapshot, configEq] using rsi
    have stepped := Mutex.guardStore_step _ _ _ _ _ record _ stored authorized rfl operand rfl decoded
    have ran : runNext state.shared worker.context .storeEaxRsi = .ok (storedContext worker.context) := by
      simpa only [Mutex.afterStore, Threads.Context.ofState, Threads.Context.snapshot, storedContext] using
        runNext_of_step _ _ _ _ decoded stepped
    let result : Result := ⟨shared, storedContext worker.context, worker.guard, none, false⟩
    have performed : perform state.shared identifier worker (.store lease) = .ok result := by
      simp [perform, authorized, configEq, rsi, stored, ran, result, Except.mapError]
    have after : contextValid (evolved worker result) = true := by
      apply linear_contextValid worker result 2 privateInv.context unfinished
      · simp [nextPhase, phase]
      · simp [result, storedContext]
      · simp [result, storedContext]
      · simp [result, storedContext]
      · rfl
      · simp [nextPhase, phase, Phase.offset]
    refine ⟨result, advance_of_perform state identifier worker (.store lease) result privateInv.context checked
      (by simp [action, phase, guard]) performed after ?_⟩
    simp [result, evolved, nextPhase, phase]
  | preparingRelease =>
    let result : Result := ⟨state.shared, immediateContext worker.context 0, worker.guard, none, false⟩
    have decoded := decode_expected _ _ (.mov32 .rax 0) privateInv.context executable.code
      (by simp [expected, phase])
    have stepped := immediate_step _ _ 0 privateInv.context executable.code (by simp [expected, phase])
    have performed : perform state.shared identifier worker (.plain (.immediate 0)) = .ok result :=
      perform_plain _ _ _ (.immediate 0) _ decoded stepped
    have after : contextValid (evolved worker result) = true := by
      apply linear_contextValid worker result 5 privateInv.context unfinished
      · simp [nextPhase, phase]
      · simp [result, immediateContext]
      · simp [result, immediateContext]
      · simp [result, immediateContext]
      · rfl
      · simp [nextPhase, phase, Phase.offset]
    refine ⟨result, advance_of_perform state identifier worker (.plain (.immediate 0)) result privateInv.context checked
      (by simp [action, phase]) performed after ?_⟩
    simp [result, evolved, nextPhase, phase]
  | releasing =>
    have control : worker.guard.isSome = true ∧ worker.context.registers .rax = 0 := by
      simpa only [Control, phase] using privateInv.control
    obtain ⟨lease, guard⟩ := Option.isSome_iff_exists.mp control.1
    obtain ⟨record, authorized, configEq⟩ := privateInv.authority lease guard
    obtain ⟨released, releasedOk⟩ := release_admitted state config identifier worker lease inv live phase guard
    have decoded := decode_expected _ _ .exchangeEaxRdi privateInv.context executable.code
      (by simp [expected, phase])
    have operand : (worker.context.snapshot state.shared.shared.resources.space).registers .rdi =
        record.config.lockAddress := by simpa only [Threads.Context.snapshot, configEq] using rdi
    have replacement : ((worker.context.snapshot state.shared.shared.resources.space).registers .rax).setWidth 32 = 0 := by
      simp [Threads.Context.snapshot, control.2]
    have stepped := Mutex.release_step _ _ _ _ record _ releasedOk authorized rfl operand replacement decoded
    have ran : runAtomic state.shared worker.context released.2 =
        .ok (exchangedContext worker.context released.2.before) := by
      simpa only [Mutex.afterExchange, Threads.Context.ofState, Threads.Context.snapshot, X86.State.writeRegister,
        exchangedContext] using runAtomic_of_step _ _ _ _ decoded stepped
    let result : Result := ⟨released.1, exchangedContext worker.context released.2.before,
      none, some released.2, false⟩
    have performed : perform state.shared identifier worker (.release lease) = .ok result := by
      simp [perform, authorized, configEq, rdi, control.2, releasedOk, ran, result, Except.mapError]
    have after : contextValid (evolved worker result) = true := by
      apply linear_contextValid worker result 2 privateInv.context unfinished
      · simp [nextPhase, phase]
      · simp [result, exchangedContext]
      · simp [result, exchangedContext]
      · simp [result, exchangedContext]
      · rfl
      · simp [nextPhase, phase, Phase.offset]
    refine ⟨result, advance_of_perform state identifier worker (.release lease) result privateInv.context checked
      (by simp [action, phase, guard]) performed after ?_⟩
    simp [result, evolved, nextPhase, phase]
  | finishing =>
    let result : Result := ⟨state.shared, immediateContext worker.context 0, worker.guard, none, false⟩
    have decoded := decode_expected _ _ (.mov32 .rax 0) privateInv.context executable.code
      (by simp [expected, phase])
    have stepped := immediate_step _ _ 0 privateInv.context executable.code (by simp [expected, phase])
    have performed : perform state.shared identifier worker (.plain (.immediate 0)) = .ok result :=
      perform_plain _ _ _ (.immediate 0) _ decoded stepped
    have after : contextValid (evolved worker result) = true := by
      apply linear_contextValid worker result 5 privateInv.context unfinished
      · simp [nextPhase, phase]
      · simp [result, immediateContext]
      · simp [result, immediateContext]
      · simp [result, immediateContext]
      · rfl
      · simp [nextPhase, phase, Phase.offset]
    refine ⟨result, advance_of_perform state identifier worker (.plain (.immediate 0)) result privateInv.context checked
      (by simp [action, phase]) performed after ?_⟩
    simp [result, evolved, nextPhase, phase]
  | returning =>
    have decoded := decode_expected _ _ .ret privateInv.context executable.code (by simp [expected, phase])
    have stepped := return_step _ identifier _ privateInv.context executable phase
    let result : Result := ⟨state.shared, returnedContext worker.context worker.returnAddress,
      worker.guard, none, true⟩
    have ran : runReturn state.shared worker.context =
        .ok (returnedContext worker.context worker.returnAddress) := by
      change runReturn state.shared worker.context = .ok (.ofState
        ((returnedContext worker.context worker.returnAddress).snapshot state.shared.shared.resources.space))
      simp [runReturn, decode, decoded, stepped, Except.mapError]
    have performed : perform state.shared identifier worker .ret = .ok result := by
      simp [perform, ran, result]
    have after : contextValid (evolved worker result) = true := by
      simp [contextValid, evolved, nextPhase, phase, result, returnedContext, fields.1, fields.2.1, fields.2.2.1]
    refine ⟨result, advance_of_perform state identifier worker .ret result privateInv.context checked
      (by simp [action, phase]) performed after ?_⟩
    simp [result, evolved, nextPhase, phase]
  | completed => exact False.elim (unfinished phase)

/-- A live unfinished cohort selection has a concrete successful dispatch. -/
theorem dispatch_enabled (state : State) (config : Mutex.Config) (identifier : Nat) (worker : Worker)
    (inv : Invariant config state) (ready : ExecutionReady state)
    (live : state.workers[identifier]? = some worker) (unfinished : worker.phase ≠ .completed) :
    ∃ result, dispatch state identifier = .ok result := by
  obtain ⟨result, advanced⟩ := advance_enabled state config identifier worker inv ready live unfinished
  exact ⟨(⟨result.shared, state.workers.set identifier (evolved worker result)⟩, result.event),
    by simp [dispatch, live, advanced, evolved]⟩

end EDSL.OS.MutexReplay
