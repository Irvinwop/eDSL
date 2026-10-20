/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicSet64.Step

namespace EDSL.Grading.AtomicSet64
open X86 OS.AddressSpace

/-- Actual bounded-window execution over current coupled CPU/OS steps. Each
RMW and its full ordered label/access footprint is retained. Whole encoding
coverage includes RET; its RAM-derived target is not fetched by this relation. -/
inductive CoveredExecution (descriptor : Frame) : Choices → Shared → X86.State →
    Shared → Result → Prop where
  | ret {choices shared evolved before after accesses}
      (step : Step descriptor shared evolved before (choices 0) ⟨.returned after, accesses⟩)
      (fetch : FetchWithin descriptor before) :
      CoveredExecution descriptor choices shared before evolved ⟨after, 1, [], accesses⟩
  | atomic64 {choices shared evolved final before middle result accesses label}
      (step : Step descriptor shared evolved before (choices 0) ⟨.atomic64 label middle, accesses⟩)
      (fetch : FetchWithin descriptor before)
      (tail : CoveredExecution descriptor (choices.drop 1) evolved middle final result) :
      CoveredExecution descriptor choices shared before final (result.prepend 1 [label] accesses)

theorem CoveredExecution.machine {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result) :
    LockedSet64.Executes choices initial result := by
  induction covered with
  | ret step _ => exact .ret step.machine
  | atomic64 step _ _ induction => exact .atomic64 step.machine induction

theorem CoveredExecution.current {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) : Current descriptor evolved result.state := by
  induction covered with
  | ret step _ => exact step.current current
  | atomic64 step _ _ induction => exact induction (step.current current)

theorem CoveredExecution.preserves {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) : Preservation shared evolved := by
  induction covered with
  | ret step _ => exact step.preserves current
  | atomic64 step _ _ induction => exact (step.preserves current).trans (induction (step.current current))

theorem CoveredExecution.memory_frame {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) :
    (∀ query, 8 ≤ (query - descriptor.target).toNat →
      result.state.memory.read query = initial.memory.read query) ∧
    result.state.memory.executable = initial.memory.executable ∧
    result.state.memory.writable = initial.memory.writable := by
  induction covered with
  | ret step _ => exact step.memory_frame current
  | atomic64 step _ _ induction =>
    have first := step.memory_frame current
    have last := induction (step.current current)
    exact ⟨fun query outside => (last.1 query outside).trans (first.1 query outside),
      last.2.1.trans first.2.1, last.2.2.trans first.2.2⟩

/-- Derive the real ordered OS event sequence from the covered trace. Its
projection is exactly the machine event list, including unchanged repetitions.
No broad administrative history is admitted to obtain this endpoint. -/
theorem CoveredExecution.logicalTrace {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) :
    ∃ cell events, OS.Atomics64.LogicalTrace descriptor.cell cell shared events evolved ∧
      events.map OS.Atomics64.Event.logical = result.events := by
  induction covered with
  | ret step _ =>
    cases step with
    | ret _ _ =>
      obtain ⟨handle, cell, authorized, link, _⟩ := current.authority
      have live := (OS.Atomics64.authorize_ok _ _ _ _ authorized).2.2.1
      rw [link] at live
      exact ⟨cell, [], .refl live, rfl⟩
  | atomic64 step _ _ induction =>
    obtain ⟨op, event, operation, label⟩ := step.atomic_operation
    obtain ⟨cell, events, trace, projected⟩ := induction (step.current current)
    obtain ⟨handle, _, authorized, linked, _⟩ := current.authority
    have selected := (OS.Atomics64.logicalUpdate_identity _ _ _ _ _ _ _ _ operation authorized).1.trans linked
    exact ⟨cell, event :: events, .next operation selected trace,
      by simp [LockedSet64.Result.prepend, projected, label]⟩

/-- The ordered current-world history retains every actual operation tag,
including mixed or unchanged updates. It is not the old OR-only History. -/
theorem CoveredExecution.events {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) :
    ∃ cell events, OS.Atomics64.LogicalTrace descriptor.cell cell shared events evolved ∧
      events.map OS.Atomics64.Event.logical = result.events := by
  exact covered.logicalTrace current

/-- The current CPU reads at both endpoints are connected by the complete
actual checked event chain. An entry-time value is never restored at RET. -/
theorem CoveredExecution.chain {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) (old : Word)
    (read : loadQWord initial.memory descriptor.target = .ok old) :
    ∃ events output, events.map OS.Atomics64.Event.logical = result.events ∧
      loadQWord result.state.memory descriptor.target = .ok output ∧
      OS.Atomics64.LogicalChain old events output := by
  obtain ⟨cell, events, trace, projected⟩ := covered.logicalTrace current
  obtain ⟨handle, selected, authorized, linked, address⟩ := current.authority
  have stored := (OS.Atomics64.authorize_ok _ _ _ _ authorized).2.2.1
  rw [linked, trace.initial_cell] at stored
  have registered : cell.address = descriptor.target :=
    (congrArg OS.Atomics64.Cell.address (Option.some.inj stored)).trans address
  obtain ⟨output, readback, chain⟩ := trace.chain old (by
    rw [←current.coupled, registered]
    exact read)
  refine ⟨events, output, projected, ?_, chain⟩
  rw [(covered.current current).coupled, ←registered]
  exact readback

/-- Ordered mixed folding is derived behavior of the retained actual events,
separate from the independent desired set result in Post. -/
theorem CoveredExecution.readback {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) (old : Word)
    (read : loadQWord initial.memory descriptor.target = .ok old) :
    loadQWord result.state.memory descriptor.target = .ok
      (Logical64.applyUpdates old (result.events.map (fun event => (event.op, event.mask)))) := by
  obtain ⟨events, output, projected, finalRead, chain⟩ := covered.chain current old read
  rw [chain.value] at finalRead
  simpa only [←projected, List.map_map, Function.comp_def] using finalRead

theorem CoveredExecution.fetchWithin {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result) :
    FetchWithin descriptor initial := by
  cases covered with
  | ret _ fetch | atomic64 _ fetch _ => exact fetch

/-- Every actual preterminal CPU preceding has a current OS world and complete
fetch coverage in the original extent. This also covers the final RET's PC. -/
theorem CoveredExecution.prefix {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) {before count events accesses}
    (preceding : LockedSet64.Block choices initial before count events accesses)
    (bound : count < result.instructions) :
    ∃ middle, Current descriptor middle before ∧ FetchWithin descriptor before := by
  induction covered generalizing before count events accesses with
  | ret step fetch =>
    cases preceding with
    | nil => exact ⟨_, current, fetch⟩
    | atomic64 actual _ =>
      have impossible := Except.ok.inj (step.machine.symm.trans actual)
      cases impossible
  | atomic64 step fetch tail induction =>
    cases preceding with
    | nil => exact ⟨_, current, fetch⟩
    | atomic64 actual rest =>
      have same := Except.ok.inj (step.machine.symm.trans actual)
      cases same
      exact induction (step.current current) rest (by simp only [LockedSet64.Result.prepend] at bound; omega)

/-- Each operand access originates at an actual covered instruction and its
current resources. Complete encoding coverage cannot substitute for operand
permission: AccessSucceeds comes from the real successful machine step. -/
theorem CoveredExecution.access_origin {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) {access : LockedSet64.Access}
    (present : access ∈ result.accesses) :
    ∃ count before priorEvents priorAccesses observation middle,
      count < result.instructions ∧
      LockedSet64.Block choices initial before count priorEvents priorAccesses ∧
      Current descriptor middle before ∧ FetchWithin descriptor before ∧
      LockedSet64.step (choices count) before = .ok observation ∧
      access ∈ observation.accesses ∧ LockedSet64.AccessSucceeds before access := by
  obtain ⟨count, before, priorEvents, priorAccesses, observation, bound, preceding, actual, member, succeeds⟩ :=
    covered.machine.access_origin present
  obtain ⟨middle, currentBefore, fetch⟩ := covered.prefix current preceding bound
  exact ⟨count, before, priorEvents, priorAccesses, observation, middle, bound, preceding,
    currentBefore, fetch, actual, member, succeeds⟩

/-- Terminal return has a covered RET encoding and the original caller slot;
the world at that RET is exactly the returned current OS endpoint. -/
theorem CoveredExecution.terminal_origin {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) :
    ∃ count before priorEvents priorAccesses lastAccesses,
      count + 1 = result.instructions ∧
      LockedSet64.Block choices initial before count priorEvents priorAccesses ∧
      Current descriptor evolved before ∧ FetchWithin descriptor before ∧
      before.registers .rsp = descriptor.stack ∧
      LockedSet64.step (choices count) before = .ok ⟨.returned result.state, lastAccesses⟩ ∧
      result.events = priorEvents ∧ result.accesses = priorAccesses ++ lastAccesses := by
  induction covered with
  | ret step fetch =>
    have original := step.ret_original
    have world := step.ret_world
    cases world
    exact ⟨0, _, [], [], _, rfl, .nil, current, fetch, original, step.machine, rfl, rfl⟩
  | @atomic64 choices shared nextShared final before middle result accesses label step fetch tail induction =>
    obtain ⟨count, beforeReturn, priorEvents, priorAccesses, last, cost, preceding,
      returnCurrent, returnFetch, original, actual, eventTrace, accessTrace⟩ := induction (step.current current)
    refine ⟨count + 1, beforeReturn, label :: priorEvents, accesses ++ priorAccesses, last,
      by simp only [LockedSet64.Result.prepend]; omega,
      .atomic64 step.machine preceding, returnCurrent, returnFetch, original, ?_, ?_, ?_⟩
    · simpa [LockedSet64.Choices.drop, LockedSet64.Result.prepend, Nat.add_comm] using actual
    · simp [LockedSet64.Result.prepend, eventTrace]
    · simp [LockedSet64.Result.prepend, accessTrace, List.append_assoc]

/-- ABI and nonarithmetic flags follow from actual logical/RET effects. This is
separate from the independent requested value property. -/
theorem CoveredExecution.abi {descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial) :
    result.state.rip = descriptor.input.returnAddress ∧
      result.state.registers .rsp = descriptor.stack + 8 ∧
      (∀ register, register ≠ .rsp → result.state.registers register = initial.registers register) ∧
      result.state.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask := by
  induction covered with
  | ret step fetch =>
    have effect := (LockedSet64.step_returned_sound step.machine).2.1
    have read := effect.read
    rw [step.ret_original, current.stack] at read
    exact ⟨(Except.ok.inj read).symm, effect.rsp.trans (congrArg (fun value => value + 8) step.ret_original),
      effect.register_frame, by rw [effect.flags]⟩
  | atomic64 step fetch tail induction =>
    obtain ⟨_, _, effect, _⟩ := LockedSet64.step_atomic64_sound step.machine
    obtain ⟨rip, rsp, registers, flags⟩ := induction (step.current current)
    exact ⟨rip, rsp, fun register other => (registers register other).trans
      (congrFun effect.registers register), flags.trans effect.nonarithmetic_flags⟩

theorem Post.of_value {desired descriptor choices shared initial evolved result}
    (covered : CoveredExecution descriptor choices shared initial evolved result)
    (current : Current descriptor shared initial)
    (value : ∃ old output,
      loadQWord initial.memory descriptor.target = .ok old ∧
      loadQWord result.state.memory descriptor.target = .ok output ∧
      Logical64.MathematicalResult desired old (initial.registers .rsi) output) :
    Post desired descriptor shared initial evolved result.state := by
  have abi := covered.abi current
  have memory := covered.memory_frame current
  refine ⟨covered.current current, value, abi.1, abi.2.1, ?_, abi.2.2.2,
    memory.1, memory.2.1, memory.2.2, covered.preserves current⟩
  intro register member
  apply abi.2.2.1 register
  intro same
  subst register
  simp [Logical64.calleeSaved] at member

end EDSL.Grading.AtomicSet64
