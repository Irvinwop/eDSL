/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Invariant

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

private theorem bind_ok {first : Except ε α} {next : α → Except ε β} {value : β} :
    (first >>= next) = .ok value ↔ ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp

private theorem mapError_ok {first : Except ε α} {map : ε → ε'} {value : α} :
    first.mapError map = .ok value ↔ first = .ok value := by
  cases first <;> simp [Except.mapError]

/-- Both context checks are consequences of a successful advance. -/
theorem advance_contexts (state : State) (identifier : Nat) (worker : Worker) (result : Result)
    (success : advance state identifier worker = .ok result) :
    contextValid worker = true ∧ contextValid (evolved worker result) = true := by
  by_cases before : contextValid worker = true
  · refine ⟨before, ?_⟩
    obtain ⟨code, operation, selected, performed, _⟩ := advance_ok _ _ _ _ success
    by_cases after : contextValid (evolved worker result) = true
    · exact after
    · simp only [evolved] at after
      simp [advance, before, code, selected, performed, after] at success
  · simp [advance, before] at success

/-- An immediate write establishes the full 64-bit zero-extended accumulator. -/
theorem runNext_immediate_rax (shared : Mutex.State) (before after : Context) (value : BitVec 32)
    (success : runNext shared before (.mov32 .rax value) = .ok after) :
    after.registers .rax = value.setWidth 64 := by
  obtain ⟨output, decoded, stepped, same⟩ := runNext_ok _ _ _ _ success
  subst after
  simp [X86.step, decoded] at stepped
  subst output
  simp [Threads.Context.ofState, executeMov32, X86.State.writeRegister]

/-- CMP retains RAX and computes the actual zero flag from EAX. -/
theorem runNext_compare (shared : Mutex.State) (before after : Context)
    (success : runNext shared before .cmpEaxZero = .ok after) :
    after.registers = before.registers ∧
      after.flags.getLsbD 6 = ((before.registers .rax).setWidth 32 == 0) := by
  obtain ⟨output, decoded, stepped, same⟩ := runNext_ok _ _ _ _ success
  subst after
  simp [X86.step, decoded] at stepped
  subst output
  refine ⟨rfl, ?_⟩
  simpa only [Threads.Context.ofState, executeCmpEaxZero, Threads.Context.snapshot] using
    (cmpZeroFlags32_bits before.flags ((before.registers .rax).setWidth 32)).2.2.2.1

/-- The conditional jump observes current ZF and current RIP. A successful
taken branch also establishes the machine's canonical-target check. -/
theorem runNext_branch (shared : Mutex.State) (before after : Context)
    (success : runNext shared before (.jnz 0xf4) = .ok after) :
    after.registers = before.registers ∧
      after.rip = if before.flags.getLsbD 6 then before.rip + 2
        else before.rip + 2 + (0xf4 : Byte).signExtend 64 := by
  obtain ⟨output, decoded, stepped, same⟩ := runNext_ok _ _ _ _ success
  subst after
  cases jumped : executeJnz (before.snapshot shared.shared.resources.space) 0xf4 with
  | error fault =>
    simp only [BitVec.ofNat_eq_ofNat] at jumped
    simp [X86.step, decoded, jumped] at stepped
  | ok actual =>
    simp only [BitVec.ofNat_eq_ofNat] at jumped
    simp [X86.step, decoded, jumped] at stepped
    subst output
    have registers := executeShortBranch_registers jumped
    refine ⟨registers, ?_⟩
    change ((if !before.flags.getLsbD 6 then
      if canonical (before.rip + 2 + (0xf4 : Byte).signExtend 64) then
        .ok { before.snapshot shared.shared.resources.space with
          rip := before.rip + 2 + (0xf4 : Byte).signExtend 64 }
      else .error (.noncanonicalBranch (before.rip + 2 + (0xf4 : Byte).signExtend 64))
      else .ok { before.snapshot shared.shared.resources.space with rip := before.rip + 2 }) :
        Except X86.Error X86.State) = .ok actual at jumped
    cases zero : before.flags.getLsbD 6 with
    | true =>
      simp only [zero, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at jumped
      subst actual
      rfl
    | false =>
      simp only [zero, Bool.not_false, ↓reduceIte] at jumped
      split at jumped
      · cases jumped
        rfl
      · cases jumped

/-- RET changes RSP and RIP while retaining the full accumulator. -/
theorem runReturn_rax (shared : Mutex.State) (before after : Context)
    (success : runReturn shared before = .ok after) :
    after.registers .rax = before.registers .rax := by
  obtain ⟨output, decoded, stepped, same⟩ := runReturn_ok _ _ _ success
  subst after
  cases read : readWord (before.snapshot shared.shared.resources.space).memory
      ((before.snapshot shared.shared.resources.space).registers .rsp) with
  | error fault => simp [X86.step, decoded, executeRet, read] at stepped
  | ok target =>
    by_cases valid : canonical target = true
    · simp [X86.step, decoded, executeRet, read, valid] at stepped
      subst output
      simp [Threads.Context.ofState, X86.State.writeRegister, Threads.Context.snapshot]
    · simp [X86.step, decoded, executeRet, read, valid] at stepped

/-- The checked atomic event contains the exact old dword, zero-extended
into the full architectural accumulator by XCHG. -/
theorem runAtomic_rax (shared : Mutex.State) (before after : Context) (event : AtomicEvent)
    (success : runAtomic shared before event = .ok after) :
    after.registers .rax = event.before.setWidth 64 := by
  obtain ⟨output, decoded, stepped, same⟩ := runAtomic_ok _ _ _ _ success
  have actual := (step_atomic_sound decoded stepped).2.2.2.1
  simpa only [same, Threads.Context.ofState] using actual

private theorem perform_control_effect (shared : Mutex.State) (identifier : Nat) (worker : Worker)
    (operation : Action) (result : Result) (valid : Mutex.WellFormed shared)
    (success : perform shared identifier worker operation = .ok result) :
    match operation with
    | .plain instruction => result.guard = worker.guard ∧ match instruction with
      | .immediate value => result.context.registers .rax = value.setWidth 64
      | .increment => True
      | .compare => result.context.registers = worker.context.registers ∧
          result.context.flags.getLsbD 6 = ((worker.context.registers .rax).setWidth 32 == 0)
      | .branch => result.context.registers = worker.context.registers ∧
          result.context.rip = if worker.context.flags.getLsbD 6 then worker.context.rip + 2
            else worker.context.rip + 2 + (0xf4 : Byte).signExtend 64
    | .acquire => match result.guard with
      | none => result.context.registers .rax = 1
      | some _ => result.context.registers .rax = 0
    | .load _ | .store _ => result.guard = worker.guard
    | .release _ => result.guard = none
    | .ret => result.guard = worker.guard ∧ result.context.registers .rax = worker.context.registers .rax := by
  cases operation with
  | plain instruction =>
    simp only [perform, bind_ok, pure_ok, Except.ok.injEq] at success
    obtain ⟨context, ran, same⟩ := success
    subst result
    refine ⟨rfl, ?_⟩
    cases instruction with
    | immediate value => exact runNext_immediate_rax _ _ _ _ ran
    | increment => trivial
    | compare => exact runNext_compare _ _ _ ran
    | branch => exact runNext_branch _ _ _ ran
  | acquire =>
    simp only [perform, bind_ok, mapError_ok, pure_ok] at success
    obtain ⟨record, _, success⟩ := success
    split at success
    · cases success
    · simp only [bind_ok, mapError_ok, Except.ok.injEq] at success
      obtain ⟨attempt, acquired, context, ran, same⟩ := success
      subst result
      have actual := runAtomic_rax _ _ _ _ ran
      rcases Mutex.acquisition shared (principal identifier) attempt valid acquired with granted | busy
      · obtain ⟨lease, _, guard, _, _, _, _, _, old, _⟩ := granted
        simpa [guard, old] using actual
      · simpa [busy.1, busy.2.2.1] using actual
  | load guard =>
    simp only [perform, bind_ok, mapError_ok, pure_ok] at success
    obtain ⟨record, _, success⟩ := success
    split at success
    · cases success
    · simp only [bind_ok, mapError_ok, Except.ok.injEq] at success
      obtain ⟨_, _, context, _, same⟩ := success
      subst result
      rfl
  | store guard =>
    simp only [perform, bind_ok, mapError_ok, pure_ok] at success
    obtain ⟨record, _, success⟩ := success
    split at success
    · cases success
    · simp only [bind_ok, mapError_ok, Except.ok.injEq] at success
      obtain ⟨_, _, context, _, same⟩ := success
      subst result
      rfl
  | release guard =>
    simp only [perform, bind_ok, mapError_ok, pure_ok] at success
    obtain ⟨record, _, success⟩ := success
    split at success
    · cases success
    · simp only [bind_ok, mapError_ok, Except.ok.injEq] at success
      obtain ⟨_, _, context, _, same⟩ := success
      subst result
      rfl
  | ret =>
    simp only [perform, bind_ok, pure_ok, Except.ok.injEq] at success
    obtain ⟨context, ran, same⟩ := success
    subst result
    exact ⟨rfl, runReturn_rax _ _ _ ran⟩

/-- Every successful selected-worker advance preserves private control.
The busy retry and acquired fall-through follow actual XCHG, CMP and JNZ
semantics; neither an endpoint check nor a future invariant is assumed. -/
theorem advance_control (state : State) (identifier : Nat) (worker : Worker) (result : Result)
    (sharedValid : Mutex.WellFormed state.shared) (control : Control worker)
    (success : advance state identifier worker = .ok result) :
    Control (evolved worker result) := by
  obtain ⟨_, operation, selected, performed, _⟩ := advance_ok _ _ _ _ success
  have effects := perform_control_effect _ _ _ _ _ sharedValid performed
  cases phase : worker.phase with
  | entry =>
    simp [action, phase] at selected
    cases selected
    obtain ⟨guard, rax⟩ := effects
    simpa [Control, evolved, nextPhase, phase, guard, rax] using control
  | acquiring =>
    simp only [Control, phase] at control
    have free : worker.guard = none := control.1
    simp [action, phase, free] at selected
    cases selected
    cases held : result.guard <;>
      simpa only [Control, evolved, nextPhase, phase, held] using effects
  | comparing =>
    simp [action, phase] at selected
    cases selected
    obtain ⟨guard, registers, flags⟩ := effects
    simp only [Control, phase] at control
    simp only [Control, evolved, nextPhase, phase, guard, registers]
    refine ⟨?_, control⟩
    cases held : worker.guard with
    | none =>
      simp only [held] at control
      simpa [held, control] using flags
    | some lease =>
      simp only [held] at control
      simpa [held, control] using flags
  | branching =>
    simp [action, phase] at selected
    cases selected
    obtain ⟨guard, _, rip⟩ := effects
    simp only [Control, phase] at control
    rw [control.1] at rip
    have context := (advance_contexts _ _ _ _ success).1
    have pc := (of_decide_eq_true context).2.2.2
    have here : worker.context.rip = worker.entry.rip + 10 := by
      simpa [phase, Phase.offset] using pc
    cases held : worker.guard with
    | none =>
      have landed : result.context.rip = worker.entry.rip := by
        simpa [held, here, BitVec.add_assoc] using rip
      simp [Control, evolved, nextPhase, phase, landed, guard, held]
    | some lease =>
      have landed : result.context.rip = worker.entry.rip + 12 := by
        simpa [held, here, BitVec.add_assoc] using rip
      have different : result.context.rip ≠ worker.entry.rip := by
        rw [landed]
        simp [BitVec.add_right_eq_self]
      simp [Control, evolved, nextPhase, phase, different, guard, held]
  | loading =>
    cases held : worker.guard with
    | none => simp [Control, phase, held] at control
    | some lease =>
      simp [action, phase, held] at selected
      cases selected
      simp [Control, evolved, nextPhase, phase, effects, held]
  | incrementingFirst =>
    simp [action, phase] at selected
    cases selected
    simpa [Control, evolved, nextPhase, phase, effects.1] using control
  | storingFirst =>
    cases held : worker.guard with
    | none => simp [Control, phase, held] at control
    | some lease =>
      simp [action, phase, held] at selected
      cases selected
      simp [Control, evolved, nextPhase, phase, effects, held]
  | incrementingSecond =>
    simp [action, phase] at selected
    cases selected
    simpa [Control, evolved, nextPhase, phase, effects.1] using control
  | storingSecond =>
    cases held : worker.guard with
    | none => simp [Control, phase, held] at control
    | some lease =>
      simp [action, phase, held] at selected
      cases selected
      simp [Control, evolved, nextPhase, phase, effects, held]
  | preparingRelease =>
    simp [action, phase] at selected
    cases selected
    obtain ⟨guard, rax⟩ := effects
    simpa [Control, evolved, nextPhase, phase, guard, rax] using control
  | releasing =>
    cases held : worker.guard with
    | none => simp [Control, phase, held] at control
    | some lease =>
      simp [action, phase, held] at selected
      cases selected
      simpa only [Control, evolved, nextPhase, phase] using effects
  | finishing =>
    simp [action, phase] at selected
    cases selected
    obtain ⟨guard, rax⟩ := effects
    simpa [Control, evolved, nextPhase, phase, guard, rax] using control
  | returning =>
    simp [action, phase] at selected
    cases selected
    obtain ⟨guard, rax⟩ := effects
    simpa [Control, evolved, nextPhase, phase, guard, rax] using control
  | completed => simp [action, phase] at selected

end EDSL.OS.MutexReplay
