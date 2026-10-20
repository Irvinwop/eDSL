/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Invariant

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

private theorem bind_ok {first : Except ε α} {next : α → Except ε β} {value : β} :
    (first >>= next) = .ok value ↔
      ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp

private theorem mapError_ok {first : Except ε α} {map : ε → ε'} {value : α} :
    first.mapError map = .ok value ↔ first = .ok value := by
  cases first <;> simp [Except.mapError]

/-- A successful protocol lookup selects the unique registered configuration,
including its invariant function. No decidability of function equality is used. -/
theorem Registered.config_eq {shared : Mutex.State} {config : Mutex.Config}
    (registered : Registered shared config) {record : Mutex.Registered}
    (live : shared.mutex = some record) : record.config = config := by
  obtain ⟨original, present, same⟩ := registered
  have equal := Option.some.inj (live.symm.trans present)
  exact (congrArg Mutex.Registered.config equal).trans same

theorem tryAcquire_data_frame (shared : Mutex.State) (config : Mutex.Config)
    (actor : Nat) (attempt : Mutex.Attempt) (valid : Mutex.WellFormed shared)
    (registered : Registered shared config)
    (success : Mutex.tryAcquire shared actor = .ok attempt) :
    loadDWord (toMemory attempt.state.shared.resources.space) config.dataAddress =
      loadDWord (toMemory shared.shared.resources.space) config.dataAddress := by
  obtain ⟨record, exchanged, live, exchange, branches⟩ := Mutex.tryAcquire_ok _ _ _ success
  have configEq := registered.config_eq live
  have data := Mutex.exchange_data _ _ _ _ valid live exchange
  rw [configEq] at data
  rcases branches with ⟨_, same⟩ | ⟨_, same⟩ <;> rw [same] <;> exact data

theorem release_data_frame (shared : Mutex.State) (config : Mutex.Config)
    (actor : Nat) (lease : Mutex.Lease) (released : Mutex.State × AtomicEvent)
    (valid : Mutex.WellFormed shared) (registered : Registered shared config)
    (success : Mutex.release shared actor lease = .ok released) :
    loadDWord (toMemory released.1.shared.resources.space) config.dataAddress =
      loadDWord (toMemory shared.shared.resources.space) config.dataAddress := by
  obtain ⟨record, _, exchanged, authorized, _, _, exchange, same⟩ := Mutex.release_ok _ _ _ _ success
  have live := (Mutex.authorize_ok _ _ _ _ authorized).1
  have configEq := registered.config_eq live
  have data := Mutex.exchange_data _ _ _ _ valid live exchange
  rw [configEq] at data
  rw [same]
  exact data

/-- Even a reentrant attempt executes its exchange, but cannot replace a live
holder or grant a second guard. -/
theorem tryAcquire_held (shared : Mutex.State) (actor : Nat) (attempt : Mutex.Attempt)
    (record : Mutex.Registered) (lease : Mutex.Lease) (valid : Mutex.WellFormed shared)
    (live : shared.mutex = some record) (held : record.holder = some lease)
    (success : Mutex.tryAcquire shared actor = .ok attempt) :
    attempt.acquired = none ∧ attempt.state.mutex = shared.mutex := by
  obtain ⟨actual, exchanged, present, exchange, branches⟩ := Mutex.tryAcquire_ok _ _ _ success
  have equal := Option.some.inj (present.symm.trans live)
  subst actual
  have phase := (valid.2 _ live).phase
  rw [held] at phase
  have observed := (AtomicExchange.exchangeWord_sound _ _ _ _ _ _ exchange).2.2.1
  have oldOne := Except.ok.inj (observed.symm.trans phase.2)
  rcases branches with ⟨free, _⟩ | ⟨_, same⟩
  · have impossible : (0 : BitVec 32) = 1 := free.symm.trans oldOne
    exact False.elim ((by decide : (0 : BitVec 32) ≠ 1) impossible)
  · rw [same]
    exact ⟨rfl, rfl⟩

theorem Payload.data_frame {before after : Mutex.State} {config : Mutex.Config}
    {worker : Worker}
    (data : loadDWord (toMemory after.shared.resources.space) config.dataAddress =
      loadDWord (toMemory before.shared.resources.space) config.dataAddress)
    (payload : Payload before config worker) : Payload after config worker := by
  simpa only [Payload, Mutex.Closed, data] using payload

/-- An unchanged guard needs only its registration and payload observation to
be framed; its private context, operands, and control facts are unchanged. -/
theorem WorkerInvariant.frame {before after : Mutex.State} {config : Mutex.Config}
    {identifier : Nat} {worker : Worker} (invariant : WorkerInvariant before config identifier worker)
    (mutex : after.mutex = before.mutex)
    (data : loadDWord (toMemory after.shared.resources.space) config.dataAddress =
      loadDWord (toMemory before.shared.resources.space) config.dataAddress) :
    WorkerInvariant after config identifier worker := by
  refine ⟨invariant.context, invariant.operands, invariant.control, ?_, ?_⟩
  · intro lease held
    obtain ⟨record, authorized, configEq⟩ := invariant.authority lease held
    obtain ⟨live, holder, actor⟩ := Mutex.authorize_ok _ _ _ _ authorized
    exact ⟨record, Mutex.authorize_of_held _ _ _ _ (mutex.trans live) holder actor, configEq⟩
  · intro lease held
    exact (invariant.payload lease held).data_frame data

theorem perform_registered (shared : Mutex.State) (config : Mutex.Config)
    (identifier : Nat) (worker : Worker) (operation : Action) (result : Result)
    (registered : Registered shared config)
    (success : perform shared identifier worker operation = .ok result) :
    Registered result.shared config := by
  cases perform_effect _ _ _ _ _ success with
  | plain _ _ _ | load _ _ _ _ _ _ _ _ | ret _ _ => exact registered
  | acquire _ attempt _ _ _ _ acquired _ =>
    obtain ⟨record, _, live, _, branches⟩ := Mutex.tryAcquire_ok _ _ _ acquired
    have configEq := registered.config_eq live
    rcases branches with ⟨_, same⟩ | ⟨_, same⟩
    · rw [same]
      exact ⟨_, rfl, configEq⟩
    · rw [same]
      exact registered
  | store _ _ _ _ _ _ stored _ =>
    obtain ⟨_, _, _, _, same⟩ := Mutex.guardStore_ok _ _ _ _ _ stored
    rw [same]
    exact registered
  | release _ _ _ _ _ _ _ released _ =>
    obtain ⟨record, _, _, authorized, _, _, _, same⟩ := Mutex.release_ok _ _ _ _ released
    have configEq := registered.config_eq (Mutex.authorize_ok _ _ _ _ authorized).1
    rw [same]
    exact ⟨_, rfl, configEq⟩

/-- Guard authority follows the actual successful runner. This stronger form
also applies before restricting the operation to the worker's current action. -/
theorem perform_authority (shared : Mutex.State) (config : Mutex.Config)
    (identifier : Nat) (worker : Worker) (operation : Action) (result : Result)
    (registered : Registered shared config)
    (authority : ∀ lease, worker.guard = some lease →
      ∃ record, Mutex.authorize shared (principal identifier) lease = .ok record ∧ record.config = config)
    (success : perform shared identifier worker operation = .ok result) :
    ∀ lease, result.guard = some lease →
      ∃ record, Mutex.authorize result.shared (principal identifier) lease = .ok record ∧ record.config = config := by
  cases perform_effect _ _ _ _ _ success with
  | plain _ _ _ | load _ _ _ _ _ _ _ _ | ret _ _ => exact authority
  | acquire _ attempt _ _ _ _ acquired _ =>
    obtain ⟨record, _, live, _, branches⟩ := Mutex.tryAcquire_ok _ _ _ acquired
    have configEq := registered.config_eq live
    intro lease held
    rcases branches with ⟨_, same⟩ | ⟨_, same⟩
    · rw [same] at held ⊢
      cases held
      exact ⟨_, Mutex.authorize_of_held _ _ _ _ rfl rfl rfl, configEq⟩
    · rw [same] at held
      cases held
  | store _ _ _ _ selectedAuth _ stored _ =>
    intro lease held
    obtain ⟨record, authorized, configEq⟩ := authority lease held
    have sameGuard := (Mutex.exclusive _ _ _ _ _ _ _ selectedAuth authorized).1
    rw [sameGuard] at stored
    exact ⟨record, Mutex.guardStore_authorized _ _ _ _ _ _ authorized stored, configEq⟩
  | release _ _ _ _ _ _ _ _ _ =>
    intro lease held
    cases held

theorem perform_self_authority (shared : Mutex.State) (config : Mutex.Config)
    (identifier : Nat) (worker : Worker) (operation : Action) (result : Result)
    (_selected : action worker = .ok operation) (registered : Registered shared config)
    (authority : ∀ lease, worker.guard = some lease →
      ∃ record, Mutex.authorize shared (principal identifier) lease = .ok record ∧ record.config = config)
    (success : perform shared identifier worker operation = .ok result) :
    ∀ lease, result.guard = some lease →
      ∃ record, Mutex.authorize result.shared (principal identifier) lease = .ok record ∧ record.config = config :=
  perform_authority _ _ _ _ _ _ registered authority success

/-- Only the protected store action changes the payload observation. The
acquisition and release cases frame it across their actual lock exchanges. -/
theorem perform_data_frame (shared : Mutex.State) (config : Mutex.Config)
    (identifier : Nat) (worker : Worker) (operation : Action) (result : Result)
    (valid : Mutex.WellFormed shared) (registered : Registered shared config)
    (nonstore : ∀ lease, operation ≠ .store lease)
    (success : perform shared identifier worker operation = .ok result) :
    loadDWord (toMemory result.shared.shared.resources.space) config.dataAddress =
      loadDWord (toMemory shared.shared.resources.space) config.dataAddress := by
  cases operation with
  | plain instruction =>
    simp only [perform, bind_ok] at success
    obtain ⟨context, _, same⟩ := success
    simp only [pure_ok, Except.ok.injEq] at same
    subst result
    rfl
  | acquire =>
    simp only [perform, bind_ok, mapError_ok] at success
    obtain ⟨record, _, success⟩ := success
    split at success
    · simp_all
    · simp only [bind_ok, mapError_ok] at success
      obtain ⟨attempt, acquired, context, _, same⟩ := success
      simp only [pure_ok, Except.ok.injEq] at same
      subst result
      exact tryAcquire_data_frame _ _ _ _ valid registered acquired
  | load lease =>
    simp only [perform, bind_ok, mapError_ok] at success
    obtain ⟨record, _, success⟩ := success
    split at success
    · simp_all
    · simp only [bind_ok, mapError_ok] at success
      obtain ⟨value, _, context, _, same⟩ := success
      simp only [pure_ok, Except.ok.injEq] at same
      subst result
      rfl
  | store lease => exact False.elim (nonstore lease rfl)
  | release lease =>
    simp only [perform, bind_ok, mapError_ok] at success
    obtain ⟨record, _, success⟩ := success
    split at success
    · simp_all
    · simp only [bind_ok, mapError_ok] at success
      obtain ⟨released, finished, context, _, same⟩ := success
      simp only [pure_ok, Except.ok.injEq] at same
      subst result
      exact release_data_frame _ _ _ _ _ valid registered finished
  | ret =>
    simp only [perform, bind_ok] at success
    obtain ⟨context, _, same⟩ := success
    simp only [pure_ok, Except.ok.injEq] at same
    subst result
    rfl

/-- A peer without a guard has no shared payload or authority obligation.
A peer with one excludes selected stores/releases by mutex exclusivity. -/
theorem perform_peer (shared : Mutex.State) (config : Mutex.Config)
    (selectedId peerId : Nat) (selected peer : Worker) (operation : Action) (result : Result)
    (valid : Mutex.WellFormed shared) (registered : Registered shared config)
    (different : selectedId ≠ peerId) (invariant : WorkerInvariant shared config peerId peer)
    (success : perform shared selectedId selected operation = .ok result) :
    WorkerInvariant result.shared config peerId peer := by
  cases guard : peer.guard with
  | none =>
    refine ⟨invariant.context, invariant.operands, invariant.control, ?_, ?_⟩
    · intro lease held; rw [guard] at held; cases held
    · intro lease held; rw [guard] at held; cases held
  | some lease =>
    obtain ⟨record, authorized, _⟩ := invariant.authority lease guard
    obtain ⟨live, held, _⟩ := Mutex.authorize_ok _ _ _ _ authorized
    have excludes : ∀ otherLease otherRecord,
        Mutex.authorize shared (principal selectedId) otherLease = .ok otherRecord → False := by
      intro otherLease otherRecord otherAuth
      have principals := (Mutex.exclusive _ _ _ _ _ _ _ otherAuth authorized).2
      exact different (Nat.add_right_cancel principals)
    cases perform_effect _ _ _ _ _ success with
    | plain _ _ _ | load _ _ _ _ _ _ _ _ | ret _ _ => exact invariant
    | acquire _ attempt _ _ _ _ acquired _ =>
      exact invariant.frame (tryAcquire_held _ _ _ _ _ valid live held acquired).2
        (tryAcquire_data_frame _ _ _ _ valid registered acquired)
    | store _ _ _ _ otherAuth _ _ _ => exact False.elim (excludes _ _ otherAuth)
    | release _ _ _ _ otherAuth _ _ _ _ => exact False.elim (excludes _ _ otherAuth)

/-- Replay changes cells through stores and exchanges but never creates,
revokes, or edits the retained code/stack loans. -/
theorem perform_loans (shared : Mutex.State) (identifier : Nat) (worker : Worker)
    (operation : Action) (result : Result)
    (success : perform shared identifier worker operation = .ok result) :
    result.shared.shared.loans = shared.shared.loans ∧
      result.shared.shared.nextLoan = shared.shared.nextLoan := by
  cases perform_effect _ _ _ _ _ success with
  | plain _ _ _ | load _ _ _ _ _ _ _ _ | ret _ _ => exact ⟨rfl, rfl⟩
  | acquire _ _ _ _ _ _ acquired _ =>
    obtain ⟨_, _, _, exchange, branches⟩ := Mutex.tryAcquire_ok _ _ _ acquired
    have effect := Mutex.exchange_effect exchange
    rcases branches with ⟨_, same⟩ | ⟨_, same⟩ <;> rw [same]
    all_goals exact ⟨effect.loans, effect.nextLoan⟩
  | store _ _ _ _ _ _ stored _ =>
    obtain ⟨record, output, _, changed, same⟩ := Mutex.guardStore_ok _ _ _ _ _ stored
    have noTicket := Mutex.store_none changed
    have changedNone : Borrowing.mutate shared.shared
        (.store record.config.owner record.config.dataTicket record.config.dataAddress (accumulator worker)) =
        .ok (output.1, none) := by
      rw [← noTicket]
      exact changed
    have effect := Mutex.store_effect changedNone
    rw [same]
    exact ⟨effect.loans, effect.nextLoan⟩
  | release _ _ _ _ _ _ _ released _ =>
    obtain ⟨_, _, _, _, _, _, exchange, same⟩ := Mutex.release_ok _ _ _ _ released
    have effect := Mutex.exchange_effect exchange
    rw [same]
    exact ⟨effect.loans, effect.nextLoan⟩

theorem perform_wellFormed (shared : Mutex.State) (identifier : Nat) (worker : Worker)
    (operation : Action) (result : Result) (valid : Mutex.WellFormed shared)
    (success : perform shared identifier worker operation = .ok result) :
    Mutex.WellFormed result.shared := (perform_history _ _ _ _ _ success).wellFormed valid

end EDSL.OS.MutexReplay
