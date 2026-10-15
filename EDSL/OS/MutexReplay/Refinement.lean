/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Model

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

def Result.outcome (result : Result) : X86.StepResult :=
  let output := result.context.snapshot result.shared.shared.resources.space
  if result.returned then .returned output else
    match result.event with | none => .next output | some event => .atomic event output

theorem decode_ok (shared : Mutex.State) (context : Context) (expected : Instruction)
    (success : decode shared context expected = .ok ()) :
    decodeAt (context.snapshot shared.shared.resources.space) = .ok expected := by
  cases decoded : decodeAt (context.snapshot shared.shared.resources.space) with
  | error fault => simp [decode, decoded, Except.mapError] at success
  | ok actual =>
    by_cases equal : actual = expected
    · subst actual
      rfl
    · simp [decode, decoded, Except.mapError, equal] at success

theorem runNext_ok (shared : Mutex.State) (context : Context) (expected : Instruction)
    (after : Context) (success : runNext shared context expected = .ok after) :
    ∃ output, decodeAt (context.snapshot shared.shared.resources.space) = .ok expected ∧
      X86.step (context.snapshot shared.shared.resources.space) = .ok (.next output) ∧
      after = Threads.Context.ofState output := by
  cases checked : decode shared context expected with
  | error fault => simp [runNext, checked] at success
  | ok checkedResult =>
    cases checkedResult
    cases stepped : X86.step (context.snapshot shared.shared.resources.space) with
    | error fault => simp [runNext, checked, stepped, Except.mapError] at success
    | ok outcome =>
      cases outcome <;> simp [runNext, checked, stepped, Except.mapError] at success
      case next output => exact ⟨output, decode_ok _ _ _ checked, rfl, success.symm⟩

theorem runAtomic_ok (shared : Mutex.State) (context : Context) (event : AtomicEvent)
    (after : Context) (success : runAtomic shared context event = .ok after) :
    ∃ output, decodeAt (context.snapshot shared.shared.resources.space) = .ok .exchangeEaxRdi ∧
      X86.step (context.snapshot shared.shared.resources.space) = .ok (.atomic event output) ∧
      after = Threads.Context.ofState output := by
  cases checked : decode shared context .exchangeEaxRdi with
  | error fault => simp [runAtomic, checked] at success
  | ok checkedResult =>
    cases checkedResult
    cases stepped : X86.step (context.snapshot shared.shared.resources.space) with
    | error fault => simp [runAtomic, checked, stepped, Except.mapError] at success
    | ok outcome =>
      cases outcome with
      | next output | returned output | syscall output => simp [runAtomic, checked, stepped, Except.mapError] at success
      | atomic actual output =>
        by_cases equal : actual = event
        · subst actual
          simp [runAtomic, checked, stepped, Except.mapError] at success
          exact ⟨output, decode_ok _ _ _ checked, rfl, success.symm⟩
        · simp [runAtomic, checked, stepped, Except.mapError, equal] at success

theorem runReturn_ok (shared : Mutex.State) (context : Context)
    (after : Context) (success : runReturn shared context = .ok after) :
    ∃ output, decodeAt (context.snapshot shared.shared.resources.space) = .ok .ret ∧
      X86.step (context.snapshot shared.shared.resources.space) = .ok (.returned output) ∧
      after = Threads.Context.ofState output := by
  cases checked : decode shared context .ret with
  | error fault => simp [runReturn, checked] at success
  | ok checkedResult =>
    cases checkedResult
    cases stepped : X86.step (context.snapshot shared.shared.resources.space) with
    | error fault => simp [runReturn, checked, stepped, Except.mapError] at success
    | ok outcome =>
      cases outcome <;> simp [runReturn, checked, stepped, Except.mapError] at success
      case returned output => exact ⟨output, decode_ok _ _ _ checked, rfl, success.symm⟩

theorem snapshot_ofState (output : X86.State) (space : Space)
    (memory : output.memory = toMemory space) :
    (Threads.Context.ofState output).snapshot space = output := by
  cases output with
  | mk registers rip flags cells =>
    change cells = toMemory space at memory
    subst cells
    rfl

private theorem shortBranch_memory (initial output : X86.State) (taken : Bool) (displacement : Byte)
    (success : executeShortBranch initial taken displacement = .ok output) : output.memory = initial.memory := by
  unfold executeShortBranch at success
  split at success
  · dsimp only at success
    split at success
    · cases success; rfl
    · cases success
  · cases success; rfl

theorem plain_memory (initial output : X86.State) (instruction : Plain)
    (decoded : decodeAt initial = .ok instruction.instruction)
    (success : X86.step initial = .ok (.next output)) : output.memory = initial.memory := by
  cases instruction with
  | immediate value =>
    simp [X86.step, decoded, Plain.instruction] at success
    cases success
    rfl
  | increment =>
    simp [X86.step, decoded, Plain.instruction] at success
    cases success
    rfl
  | compare =>
    simp [X86.step, decoded, Plain.instruction] at success
    cases success
    rfl
  | branch =>
    cases jumped : executeJnz initial 0xf4 with
    | error fault =>
      simp only [BitVec.ofNat_eq_ofNat] at jumped
      simp [X86.step, decoded, Plain.instruction, jumped] at success
    | ok actual =>
      simp only [BitVec.ofNat_eq_ofNat] at jumped
      simp [X86.step, decoded, Plain.instruction, jumped] at success
      cases success
      exact shortBranch_memory _ _ _ _ jumped

theorem return_memory (initial output : X86.State)
    (decoded : decodeAt initial = .ok .ret)
    (success : X86.step initial = .ok (.returned output)) : output.memory = initial.memory := by
  cases read : readWord initial.memory (initial.registers .rsp) with
  | error fault => simp [X86.step, decoded, executeRet, read] at success
  | ok target =>
    by_cases valid : canonical target = true
    · simp [X86.step, decoded, executeRet, read, valid] at success
      cases success
      rfl
    · simp [X86.step, decoded, executeRet, read, valid] at success

/-- Exact successful branches of the protocol/machine runner. -/
inductive PerformEffect (shared : Mutex.State) (identifier : Nat) (worker : Worker) : Result → Prop where
  | plain (instruction : Plain) (context : Context)
      (ran : runNext shared worker.context instruction.instruction = .ok context) :
      PerformEffect shared identifier worker ⟨shared, context, worker.guard, none, false⟩
  | acquire (record : Mutex.Registered) (attempt : Mutex.Attempt) (context : Context)
      (found : Mutex.registered shared = .ok record)
      (operand : worker.context.registers .rdi = record.config.lockAddress)
      (replacement : (worker.context.registers .rax).setWidth 32 = 1)
      (acquired : Mutex.tryAcquire shared (principal identifier) = .ok attempt)
      (ran : runAtomic shared worker.context attempt.event = .ok context) :
      PerformEffect shared identifier worker ⟨attempt.state, context, attempt.acquired, some attempt.event, false⟩
  | load (guard : Mutex.Lease) (record : Mutex.Registered) (value : BitVec 32) (context : Context)
      (authorized : Mutex.authorize shared (principal identifier) guard = .ok record)
      (operand : worker.context.registers .rsi = record.config.dataAddress)
      (loaded : Mutex.guardLoad shared (principal identifier) guard = .ok value)
      (ran : runNext shared worker.context .loadEaxRsi = .ok context) :
      PerformEffect shared identifier worker ⟨shared, context, worker.guard, none, false⟩
  | store (guard : Mutex.Lease) (record : Mutex.Registered) (after : Mutex.State) (context : Context)
      (authorized : Mutex.authorize shared (principal identifier) guard = .ok record)
      (operand : worker.context.registers .rsi = record.config.dataAddress)
      (stored : Mutex.guardStore shared (principal identifier) guard ((worker.context.registers .rax).setWidth 32) = .ok after)
      (ran : runNext shared worker.context .storeEaxRsi = .ok context) :
      PerformEffect shared identifier worker ⟨after, context, worker.guard, none, false⟩
  | release (guard : Mutex.Lease) (record : Mutex.Registered) (released : Mutex.State × AtomicEvent) (context : Context)
      (authorized : Mutex.authorize shared (principal identifier) guard = .ok record)
      (operand : worker.context.registers .rdi = record.config.lockAddress)
      (replacement : (worker.context.registers .rax).setWidth 32 = 0)
      (finished : Mutex.release shared (principal identifier) guard = .ok released)
      (ran : runAtomic shared worker.context released.2 = .ok context) :
      PerformEffect shared identifier worker ⟨released.1, context, none, some released.2, false⟩
  | ret (context : Context) (ran : runReturn shared worker.context = .ok context) :
      PerformEffect shared identifier worker ⟨shared, context, worker.guard, none, true⟩

theorem perform_effect (shared : Mutex.State) (identifier : Nat) (worker : Worker) (operation : Action)
    (result : Result) (success : perform shared identifier worker operation = .ok result) :
    PerformEffect shared identifier worker result := by
  cases operation with
  | plain instruction =>
    cases ran : runNext shared worker.context instruction.instruction with
    | error fault => simp [perform, ran] at success
    | ok context =>
      simp [perform, ran] at success
      subst result
      exact .plain instruction context ran
  | acquire =>
    cases found : Mutex.registered shared with
    | error fault => simp [perform, found, Except.mapError] at success
    | ok record =>
      by_cases operands : worker.context.registers .rdi = record.config.lockAddress ∧
          (worker.context.registers .rax).setWidth 32 = 1
      · simp only [BitVec.ofNat_eq_ofNat] at operands
        cases acquired : Mutex.tryAcquire shared (principal identifier) with
        | error fault => simp [perform, found, operands, acquired, Except.mapError] at success
        | ok attempt =>
          cases ran : runAtomic shared worker.context attempt.event with
          | error fault => simp [perform, found, operands, acquired, ran, Except.mapError] at success
          | ok context =>
            simp [perform, found, operands, acquired, ran, Except.mapError] at success
            subst result
            exact .acquire record attempt context found operands.1 operands.2 acquired ran
      · have denied : worker.context.registers .rdi ≠ record.config.lockAddress ∨
            (worker.context.registers .rax).setWidth 32 ≠ 1 := by
          by_cases first : worker.context.registers .rdi = record.config.lockAddress
          · exact Or.inr (fun second => operands ⟨first, second⟩)
          · exact Or.inl first
        simp only [BitVec.ofNat_eq_ofNat] at denied
        simp [perform, found, Except.mapError, denied] at success
  | load guard =>
    cases authorized : Mutex.authorize shared (principal identifier) guard with
    | error fault => simp [perform, authorized, Except.mapError] at success
    | ok record =>
      by_cases operand : worker.context.registers .rsi = record.config.dataAddress
      · cases loaded : Mutex.guardLoad shared (principal identifier) guard with
        | error fault => simp [perform, authorized, operand, loaded, Except.mapError] at success
        | ok value =>
          cases ran : runNext shared worker.context .loadEaxRsi with
          | error fault => simp [perform, authorized, operand, loaded, ran, Except.mapError] at success
          | ok context =>
            simp [perform, authorized, operand, loaded, ran, Except.mapError] at success
            subst result
            exact .load guard record value context authorized operand loaded ran
      · simp [perform, authorized, operand, Except.mapError] at success
  | store guard =>
    cases authorized : Mutex.authorize shared (principal identifier) guard with
    | error fault => simp [perform, authorized, Except.mapError] at success
    | ok record =>
      by_cases operand : worker.context.registers .rsi = record.config.dataAddress
      · cases stored : Mutex.guardStore shared (principal identifier) guard ((worker.context.registers .rax).setWidth 32) with
        | error fault => simp [perform, authorized, operand, stored, Except.mapError] at success
        | ok after =>
          cases ran : runNext shared worker.context .storeEaxRsi with
          | error fault => simp [perform, authorized, operand, stored, ran, Except.mapError] at success
          | ok context =>
            simp [perform, authorized, operand, stored, ran, Except.mapError] at success
            subst result
            exact .store guard record after context authorized operand stored ran
      · simp [perform, authorized, operand, Except.mapError] at success
  | release guard =>
    cases authorized : Mutex.authorize shared (principal identifier) guard with
    | error fault => simp [perform, authorized, Except.mapError] at success
    | ok record =>
      by_cases operands : worker.context.registers .rdi = record.config.lockAddress ∧
          (worker.context.registers .rax).setWidth 32 = 0
      · simp only [BitVec.ofNat_eq_ofNat] at operands
        cases finished : Mutex.release shared (principal identifier) guard with
        | error fault => simp [perform, authorized, operands, finished, Except.mapError] at success
        | ok released =>
          cases ran : runAtomic shared worker.context released.2 with
          | error fault => simp [perform, authorized, operands, finished, ran, Except.mapError] at success
          | ok context =>
            simp [perform, authorized, operands, finished, ran, Except.mapError] at success
            subst result
            exact .release guard record released context authorized operands.1 operands.2 finished ran
      · have denied : worker.context.registers .rdi ≠ record.config.lockAddress ∨
            (worker.context.registers .rax).setWidth 32 ≠ 0 := by
          by_cases first : worker.context.registers .rdi = record.config.lockAddress
          · exact Or.inr (fun second => operands ⟨first, second⟩)
          · exact Or.inl first
        simp only [BitVec.ofNat_eq_ofNat] at denied
        simp [perform, authorized, Except.mapError, denied] at success
  | ret =>
    cases ran : runReturn shared worker.context with
    | error fault => simp [perform, ran] at success
    | ok context =>
      simp [perform, ran] at success
      subst result
      exact .ret context ran

/-- Every successful replay action is a genuine complete architectural step;
protocol checks do not replace or assume its actual resulting machine state. -/
theorem perform_refines (shared : Mutex.State) (identifier : Nat) (worker : Worker) (operation : Action)
    (result : Result) (success : perform shared identifier worker operation = .ok result) :
    X86.step (worker.context.snapshot shared.shared.resources.space) = .ok result.outcome := by
  have effect := perform_effect _ _ _ _ _ success
  cases effect with
  | plain instruction context ran =>
    obtain ⟨output, decoded, stepped, same⟩ := runNext_ok _ _ _ _ ran
    have memory := plain_memory _ _ instruction decoded stepped
    have projected := snapshot_ofState output shared.shared.resources.space memory
    simp only [Result.outcome, Bool.false_eq_true, ↓reduceIte]
    rw [same, projected]
    exact stepped
  | acquire record attempt context found operand replacement acquired ran =>
    obtain ⟨output, decoded, stepped, same⟩ := runAtomic_ok _ _ _ _ ran
    have bridge := Mutex.tryAcquire_step shared (principal identifier) attempt record
      (worker.context.snapshot shared.shared.resources.space) acquired (Mutex.registered_ok _ _ found)
      rfl operand replacement decoded
    have equal := X86.StepResult.atomic.inj (Except.ok.inj (stepped.symm.trans bridge))
    have projected := snapshot_ofState output attempt.state.shared.resources.space (congrArg X86.State.memory equal.2)
    simp only [Result.outcome, Bool.false_eq_true, ↓reduceIte]
    rw [same, projected]
    exact stepped
  | load guard record value context authorized operand loaded ran =>
    obtain ⟨output, decoded, stepped, same⟩ := runNext_ok _ _ _ _ ran
    have bridge := Mutex.guardLoad_step shared (principal identifier) guard value record
      (worker.context.snapshot shared.shared.resources.space) loaded authorized rfl operand decoded
    have equal := X86.StepResult.next.inj (Except.ok.inj (stepped.symm.trans bridge))
    have projected := snapshot_ofState output shared.shared.resources.space (congrArg X86.State.memory equal)
    simp only [Result.outcome, Bool.false_eq_true, ↓reduceIte]
    rw [same, projected]
    exact stepped
  | store guard record after context authorized operand stored ran =>
    obtain ⟨output, decoded, stepped, same⟩ := runNext_ok _ _ _ _ ran
    have bridge := Mutex.guardStore_step shared (principal identifier) guard _ after record
      (worker.context.snapshot shared.shared.resources.space) stored authorized rfl operand rfl decoded
    have equal := X86.StepResult.next.inj (Except.ok.inj (stepped.symm.trans bridge))
    have projected := snapshot_ofState output after.shared.resources.space (congrArg X86.State.memory equal)
    simp only [Result.outcome, Bool.false_eq_true, ↓reduceIte]
    rw [same, projected]
    exact stepped
  | release guard record released context authorized operand replacement finished ran =>
    obtain ⟨output, decoded, stepped, same⟩ := runAtomic_ok _ _ _ _ ran
    have bridge := Mutex.release_step shared (principal identifier) guard released record
      (worker.context.snapshot shared.shared.resources.space) finished authorized rfl operand replacement decoded
    have equal := X86.StepResult.atomic.inj (Except.ok.inj (stepped.symm.trans bridge))
    have projected := snapshot_ofState output released.1.shared.resources.space (congrArg X86.State.memory equal.2)
    simp only [Result.outcome, Bool.false_eq_true, ↓reduceIte]
    rw [same, projected]
    exact stepped
  | ret context ran =>
    obtain ⟨output, decoded, stepped, same⟩ := runReturn_ok _ _ _ ran
    have memory := return_memory _ _ decoded stepped
    have projected := snapshot_ofState output shared.shared.resources.space memory
    simp only [Result.outcome, ↓reduceIte]
    rw [same, projected]
    exact stepped

theorem perform_history (shared : Mutex.State) (identifier : Nat) (worker : Worker) (operation : Action)
    (result : Result) (success : perform shared identifier worker operation = .ok result) :
    Mutex.History shared result.shared := by
  have effect := perform_effect _ _ _ _ _ success
  cases effect with
  | plain _ _ _ | load _ _ _ _ _ _ _ _ | ret _ _ => exact .refl
  | acquire _ _ _ _ _ _ acquired _ => exact .next (.acquire acquired) .refl
  | store _ _ _ _ _ _ stored _ => exact .next (.store stored) .refl
  | release _ _ _ _ _ _ _ released _ => exact .next (.release released) .refl

theorem perform_return_event (shared : Mutex.State) (identifier : Nat) (worker : Worker) (operation : Action)
    (result : Result) (success : perform shared identifier worker operation = .ok result)
    (returned : result.returned = true) : result.event = none := by
  cases perform_effect _ _ _ _ _ success <;> simp_all

end EDSL.OS.MutexReplay
