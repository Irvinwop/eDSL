/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Setup
import EDSL.OS.AtomicThreads64.Framing
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Post-return resource retirement for the production TSO64 worker model.
Only the last worker is removed, so every retained scheduler slot keeps its
original index. The supported cleanup shape is exactly one existing atomic
handle plus the worker's original code/caller loans. The persistent cell and
its allocation remain registered; ordinary ownership grants are not released.

Ready and Separate describe current, independently decidable resource data.
No future successful operation, execution, return or final RAM value is an
admission premise. This adapter is explicit administrative post-processing,
not a new issue/drain action or a native OS join/authentication theorem.
-/

namespace EDSL.OS.TSO64.Lifecycle
open X86 AddressSpace

/-- Present admission for the supported cleanup shape. The completed phase and
empty FIFO are current observations. Loan identities are logical capabilities;
this model supplies no native authentication for the actor label. -/
def Ready (world : World) (worker : Worker) (identifier : Atomics64.HandleId64) : Prop :=
  worker.phase = .returned ∧ worker.pending = [] ∧
    worker.resources.atomics = [identifier] ∧ ResourcesValid world worker.resources ∧
    worker.resources.code.identifier ≠ worker.resources.caller.identifier

instance (world : World) (worker : Worker) (identifier : Atomics64.HandleId64) :
    Decidable (Ready world worker identifier) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A retained peer names none of the released capabilities. Different actor
labels are unnecessary and are not confused with scheduler slot indices. -/
def Separate (retiring peer : Resources) : Prop :=
  peer.code.identifier ≠ retiring.code.identifier ∧
    peer.code.identifier ≠ retiring.caller.identifier ∧
    peer.caller.identifier ≠ retiring.code.identifier ∧
    peer.caller.identifier ≠ retiring.caller.identifier ∧
    ∀ identifier ∈ peer.atomics, identifier ∉ retiring.atomics

instance (retiring peer : Resources) : Decidable (Separate retiring peer) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ (∀ identifier ∈ peer.atomics, _)))

/-- Every operation rechecks its current authority. An error exposes no
partially updated state. The immutable input world remains the caller's value. -/
def release (world : World) (worker : Worker) : Except Fault World := do
  if worker.phase ≠ .returned ∨ !worker.pending.isEmpty then throw .resource
  match worker.resources.atomics with
  | [identifier] =>
    let data ← (Atomics64.close world worker.resources.actor identifier).mapError Fault.os
    let code ← (Atomics64.finishLoan data worker.resources.actor
      worker.resources.code.identifier).mapError Fault.os
    (Atomics64.finishLoan code worker.resources.actor
      worker.resources.caller.identifier).mapError Fault.os
  | _ => throw .resource

/-- Remove only the last completed record; retained scheduler tids do not move.
The result is the current private context, including its actual RAX value. -/
def retireLast (state : State) : Except Fault (State × Context) := do
  let worker :: peers := state.workers.reverse | throw .missingWorker
  let after ← release state.world worker
  return (⟨after, peers.reverse⟩, worker.context)

/-- Exact checked operations, extracted from release; never a caller-supplied
substitute for the Ready manifest in the enabledness theorem. -/
def Release (before : World) (worker : Worker) (after : World) : Prop :=
  ∃ (identifier : Atomics64.HandleId64) (data code : World),
    worker.resources.atomics = [identifier] ∧ worker.phase = .returned ∧
    worker.pending = [] ∧
    Atomics64.close before worker.resources.actor identifier = .ok data ∧
    Atomics64.finishLoan data worker.resources.actor worker.resources.code.identifier = .ok code ∧
    Atomics64.finishLoan code worker.resources.actor worker.resources.caller.identifier = .ok after

private def dropLoan (world : World) (identifier : Nat) : World :=
  { world with legacy := { world.legacy with shared := { world.legacy.shared with
    loans := fun query => if query = identifier then none else world.legacy.shared.loans query } } }

private theorem finishLoan_shape {before after : World} {actor identifier : Nat}
    (success : Atomics64.finishLoan before actor identifier = .ok after) :
    after = dropLoan before identifier := by
  obtain ⟨legacy, finished, same⟩ := Atomics64.finishLoan_ok _ _ _ _ success
  obtain ⟨shared, checked, legacyEq⟩ := Atomics.finishLoan_ok _ _ _ _ finished
  obtain ⟨_loan, _authorized, sharedEq⟩ := Borrowing.finishLoan_ok _ _ _ _ checked
  rw [same, legacyEq, sharedEq]
  rfl

private theorem finishLoan_present (world : World) (actor identifier : Nat)
    (loan : Borrowing.Loan) (live : world.legacy.shared.loans identifier = some loan)
    (borrower : loan.borrower = actor) :
    Atomics64.finishLoan world actor identifier = .ok (dropLoan world identifier) := by
  simp [Atomics64.finishLoan, Atomics.finishLoan, Borrowing.finishLoan,
    Borrowing.authorize, live, borrower, dropLoan, Except.mapError]

/-- Successful release exposes actual checked close/finishLoan operations. -/
theorem release_ok {before after : World} {worker : Worker}
    (success : release before worker = .ok after) : Release before worker after := by
  by_cases phase : worker.phase = .returned
  · by_cases empty : worker.pending.isEmpty = true
    · cases handles : worker.resources.atomics with
      | nil => simp [release, phase, empty, handles] at success
      | cons identifier rest =>
        cases rest with
        | cons other tail => simp [release, phase, empty, handles] at success
        | nil =>
          cases closed : Atomics64.close before worker.resources.actor identifier with
          | error fault => simp [release, phase, empty, handles, closed, Except.mapError] at success
          | ok data =>
            cases codeDone : Atomics64.finishLoan data worker.resources.actor
                worker.resources.code.identifier with
            | error fault => simp [release, phase, empty, handles, closed, codeDone,
                Except.mapError] at success
            | ok code =>
              have callerDone : Atomics64.finishLoan code worker.resources.actor
                  worker.resources.caller.identifier = .ok after := by
                cases done : Atomics64.finishLoan code worker.resources.actor
                    worker.resources.caller.identifier with
                | error fault => simp [release, phase, empty, handles, closed, codeDone,
                    done, Except.mapError] at success
                | ok output =>
                  simp [release, phase, empty, handles, closed, codeDone, done,
                    Except.mapError] at success
                  simp only [success]
              exact ⟨identifier, data, code, handles, phase, List.isEmpty_iff.mp empty,
                closed, codeDone, callerDone⟩
    · simp [release, phase, empty] at success
  · simp [release, phase] at success

/-- Present current capabilities prove enabledness; success is concluded. -/
theorem release_enabled {world : World} {worker : Worker} {identifier : Atomics64.HandleId64}
    (ready : Ready world worker identifier) : ∃ after, release world worker = .ok after := by
  obtain ⟨phase, empty, handles, valid, distinct⟩ := ready
  have authorized : (Atomics64.authorize world worker.resources.actor identifier).isOk = true :=
    valid.2.2.2.2 identifier (by simp [handles])
  cases selected : Atomics64.authorize world worker.resources.actor identifier with
  | error fault => simp [selected, Except.isOk, Except.toBool] at authorized
  | ok descriptor =>
    have closed : Atomics64.close world worker.resources.actor identifier =
        .ok (Atomics64.removeHandle world identifier) := by
      simp [Atomics64.close, selected]
    have codeLive : (Atomics64.removeHandle world identifier).legacy.shared.loans
        worker.resources.code.identifier = some worker.resources.code.loan := valid.1.1
    have codeDone := finishLoan_present _ _ _ _ codeLive valid.1.2.1
    have callerLive : (dropLoan (Atomics64.removeHandle world identifier)
        worker.resources.code.identifier).legacy.shared.loans worker.resources.caller.identifier =
          some worker.resources.caller.loan := by
      exact (AtomicThreads64.finishLoan_other codeDone distinct.symm).trans valid.2.1.1
    have callerDone := finishLoan_present _ _ _ _ callerLive valid.2.1.2.1
    refine ⟨dropLoan (dropLoan (Atomics64.removeHandle world identifier)
      worker.resources.code.identifier) worker.resources.caller.identifier, ?_⟩
    simp [release, phase, empty, handles, closed, codeDone, callerDone, Except.mapError]

/-- Extraction preserves the original last worker and gives a concrete suffix
removal; it never treats an abstract AtomicThreads64 worker as a TSO64 worker. -/
theorem retireLast_ok {state : State} {result : State × Context}
    (success : retireLast state = .ok result) :
    ∃ (peers : List Worker) (worker : Worker),
      state.workers = peers ++ [worker] ∧ Release state.world worker result.1.world ∧
      result.1.workers = peers ∧ result.2 = worker.context := by
  cases reversed : state.workers.reverse with
  | nil => simp [retireLast, reversed] at success
  | cons worker rest =>
    cases released : release state.world worker with
    | error fault => simp [retireLast, reversed, released] at success
    | ok after =>
      simp only [retireLast, reversed, released, ok_bind, pure_ok, Except.ok.injEq] at success
      have workers : state.workers = rest.reverse ++ [worker] := by
        have same := congrArg List.reverse reversed
        simpa using same
      rw [← success]
      exact ⟨rest.reverse, worker, workers, release_ok released, rfl, rfl⟩

theorem retireLast_enabled {state : State} {peers : List Worker} {worker : Worker}
    {identifier : Atomics64.HandleId64} (workers : state.workers = peers ++ [worker])
    (ready : Ready state.world worker identifier) : ∃ result, retireLast state = .ok result := by
  obtain ⟨after, released⟩ := release_enabled ready
  exact ⟨(⟨after, peers⟩, worker.context), by simp [retireLast, workers, released]⟩

private theorem Release.shape {before after : World} {worker : Worker}
    (effect : Release before worker after) :
    ∃ identifier, worker.resources.atomics = [identifier] ∧
      after = dropLoan (dropLoan (Atomics64.removeHandle before identifier)
        worker.resources.code.identifier) worker.resources.caller.identifier := by
  obtain ⟨identifier, data, code, handles, _phase, _empty, closed, codeDone, callerDone⟩ := effect
  refine ⟨identifier, handles, ?_⟩
  obtain ⟨_selected, _authorized, dataEq⟩ := Atomics64.close_ok _ _ _ _ closed
  rw [finishLoan_shape callerDone, finishLoan_shape codeDone, dataEq]

theorem Release.history {before after : World} {worker : Worker}
    (effect : Release before worker after) :
    Atomics64.History before [none, none, none] after := by
  obtain ⟨_identifier, _data, _code, _handles, _phase, _empty, closed, codeDone, callerDone⟩ := effect
  exact .next (.close closed) (.next (.finishLoan codeDone) (.next (.finishLoan callerDone) .refl))

/-- All CURRENT bytes, permissions and ownership metadata are unchanged. In
particular this does not restore a counter value captured at worker return. -/
theorem Release.resources {before after : World} {worker : Worker}
    (effect : Release before worker after) :
    after.legacy.shared.resources = before.legacy.shared.resources ∧ after.cells = before.cells := by
  obtain ⟨_identifier, _handles, same⟩ := effect.shape
  rw [same]
  exact ⟨rfl, rfl⟩

theorem Release.currentRAM {before after : World} {worker : Worker}
    (effect : Release before worker after) : published after = published before := by
  simp only [published, effect.resources.1]

/-- Persistent registration, legacy handles and every monotone frontier remain
current. Only one 64-bit handle and the two named loans can change. -/
theorem Release.registry {before after : World} {worker : Worker}
    (effect : Release before worker after) :
    after.nextCell = before.nextCell ∧ after.nextHandle = before.nextHandle ∧
      after.legacy.handles = before.legacy.handles ∧
      after.legacy.nextHandle = before.legacy.nextHandle ∧
      after.legacy.shared.nextLoan = before.legacy.shared.nextLoan := by
  obtain ⟨_identifier, _handles, same⟩ := effect.shape
  rw [same]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every unrelated resource entry is exactly unchanged, even when it is not
owned by a worker. Persistent cells and allocation resources are framed above. -/
theorem Release.onlyResources {before after : World} {worker : Worker}
    (effect : Release before worker after) :
    (∀ query, query ∉ worker.resources.atomics → after.handles query = before.handles query) ∧
      (∀ query, query ≠ worker.resources.code.identifier → query ≠ worker.resources.caller.identifier →
        after.legacy.shared.loans query = before.legacy.shared.loans query) := by
  obtain ⟨identifier, handles, same⟩ := effect.shape
  constructor
  · intro query unrelated
    have different : query ≠ identifier := by simpa [handles] using unrelated
    simp [same, dropLoan, Atomics64.removeHandle, different]
  · intro query notCode notCaller
    simp [same, dropLoan, Atomics64.removeHandle, notCode, notCaller]

/-- Real close and loan completion revoke their monotone logical identities. -/
theorem Release.revokes {before after : World} {worker : Worker}
    (effect : Release before worker after) (valid : Atomics64.WellFormed before) :
    (∀ identifier ∈ worker.resources.atomics, Atomics64.HandleRevoked after identifier) ∧
      Borrowing.Revoked after.legacy.shared worker.resources.code.identifier ∧
      Borrowing.Revoked after.legacy.shared worker.resources.caller.identifier := by
  obtain ⟨identifier, data, code, handles, _phase, _empty, closed, codeDone, callerDone⟩ := effect
  have dataValid := Atomics64.close_wellFormed _ _ _ _ valid closed
  have codeValid := Atomics64.finishLoan_wellFormed _ _ _ _ dataValid codeDone
  refine ⟨?_, ?_, ?_⟩
  · intro query member
    have same : query = identifier := by simpa [handles] using member
    subst query
    exact (Atomics64.History.next (.finishLoan codeDone) (.next (.finishLoan callerDone) .refl)).handle_revoked
      (Atomics64.close_revokes _ _ _ _ valid closed)
  · exact Atomics64.finished_for_history _ _ dataValid codeDone (.next (.finishLoan callerDone) .refl)
  · exact Atomics64.finished_for_history _ _ codeValid callerDone .refl

private theorem authorize_frame {before after : World} {actor : Nat}
    {identifier : Atomics64.HandleId64}
    (resources : after.legacy.shared.resources = before.legacy.shared.resources)
    (cells : after.cells = before.cells) (handle : after.handles identifier = before.handles identifier) :
    Atomics64.authorize after actor identifier = Atomics64.authorize before actor identifier := by
  have validate (cell : Atomics64.Cell) :
      Atomics64.validateCell after cell = Atomics64.validateCell before cell := by
    simp only [Atomics64.validateCell, resources]
  simp only [Atomics64.authorize, handle, Atomics64.currentCell, cells, validate]

/-- Retained peers keep exactly the same current handle authorization and
original code/caller authority, without imposing distinct actor labels. -/
theorem Release.peerResources {before after : World} {worker : Worker} {peer : Resources}
    (effect : Release before worker after) (separate : Separate worker.resources peer)
    (valid : ResourcesValid before peer) : ResourcesValid after peer := by
  have resourceEq := effect.resources.1
  have loans := effect.onlyResources.2
  have codeEq := loans peer.code.identifier separate.1 separate.2.1
  have callerEq := loans peer.caller.identifier separate.2.2.1 separate.2.2.2.1
  refine ⟨?_, ?_, valid.2.2.1, ?_, ?_⟩
  · simpa only [LeaseCurrent, OwnsRegion, resourceEq, codeEq] using valid.1
  · simpa only [LeaseCurrent, OwnsRegion, resourceEq, callerEq] using valid.2.1
  · intro ticket member
    simpa only [TicketCurrent, resourceEq] using valid.2.2.2.1 ticket member
  · intro identifier member
    rw [authorize_frame resourceEq effect.resources.2
      (effect.onlyResources.1 identifier (separate.2.2.2.2 identifier member))]
    exact valid.2.2.2.2 identifier member

private theorem allowed_dropLoan (world : World) (identifier : Nat) (operation : Ownership.Mutation)
    (allowed : Borrowing.allowed world.legacy.shared operation = true) :
    Borrowing.allowed (dropLoan world identifier).legacy.shared operation = true := by
  apply List.all_eq_true.mpr
  intro query member
  have original := List.all_eq_true.mp allowed query member
  by_cases removed : query = identifier
  · simp [dropLoan, removed]
  · simpa only [dropLoan, ite_eq_right removed] using original

private theorem Release.allowed {before after : World} {worker : Worker}
    (effect : Release before worker after) (operation : Ownership.Mutation)
    (allowed : Borrowing.allowed before.legacy.shared operation = true) :
    Borrowing.allowed after.legacy.shared operation = true := by
  obtain ⟨identifier, _handles, same⟩ := effect.shape
  rw [same]
  apply allowed_dropLoan
  apply allowed_dropLoan
  exact allowed

/-- Removing read loans can only loosen ordinary publication gates; it does
not lower any permission, reservation, ownership or alignment requirement. -/
theorem Release.storeGate {before after : World} {worker : Worker}
    (effect : Release before worker after) {actor : Nat} {ticket : Ownership.Ticket} {store : Store}
    (valid : StoreGate before actor ticket store) : StoreGate after actor ticket store := by
  obtain ⟨owned, scalarOK, dataOK, unreserved, legacyUnreserved, allowed⟩ := valid
  have resourceEq := effect.resources.1
  have registry := effect.registry
  refine ⟨?_, ?_, ?_, ?_, ?_, effect.allowed _ allowed⟩
  · simpa only [OwnsRegion, resourceEq] using owned
  · simpa only [effect.currentRAM] using scalarOK
  · simpa only [effect.currentRAM] using dataOK
  · simpa only [Atomics64.reserved, effect.resources.2, registry.1] using unreserved
  · simpa only [Atomics.reserved, registry.2.2.1, registry.2.2.2.1] using legacyUnreserved

/-- Peer FIFOs remain valid under either explicit production profile. The
queue is retained verbatim; no pending write is drained or silently dropped. -/
theorem Release.peerWorker {before after : World} {worker peer : Worker} {profile : Profile}
    (effect : Release before worker after) (separate : Separate worker.resources peer.resources)
    (valid : WorkerValid before peer profile) : WorkerValid after peer profile := by
  refine ⟨effect.peerResources separate valid.1, ?_⟩
  intro pending member
  have pendingValid := valid.2 pending member
  cases pending with
  | ordinary ticket store => exact ⟨pendingValid.1, effect.storeGate pendingValid.2⟩
  | managed reference value occurrence =>
    refine ⟨pendingValid.1, pendingValid.2.1, ?_⟩
    rw [authorize_frame effect.resources.1 effect.resources.2
      (effect.onlyResources.1 reference.identifier
        (separate.2.2.2.2 reference.identifier pendingValid.2.1))]
    exact pendingValid.2.2

/-- Exact current RAM and all earlier private records survive retirement. -/
theorem retireLast_frames {state : State} {result : State × Context}
    (success : retireLast state = .ok result) :
    published result.1.world = published state.world ∧
      ∃ peers worker, state.workers = peers ++ [worker] ∧ result.1.workers = peers ∧
        result.2 = worker.context ∧
        ∀ tid, tid < peers.length → result.1.workers[tid]? = state.workers[tid]? := by
  obtain ⟨peers, worker, workers, effect, kept, context⟩ := retireLast_ok success
  refine ⟨effect.currentRAM, peers, worker, workers, kept, context, ?_⟩
  intro tid beforeLast
  rw [kept, workers, List.getElem?_append_left beforeLast]

/-- The released record is absent before validity is claimed at the new world.
The finite separation manifest concerns current peer resource names only. -/
theorem retireLast_wellFormed {state : State} {result : State × Context} {profile : Profile}
    {peers : List Worker} {worker : Worker} (workers : state.workers = peers ++ [worker])
    (valid : WellFormed state profile) (success : retireLast state = .ok result)
    (separate : ∀ peer ∈ peers, Separate worker.resources peer.resources) :
    WellFormed result.1 profile := by
  cases released : release state.world worker with
  | error fault => simp [retireLast, workers, released] at success
  | ok after =>
    have same : (⟨after, peers⟩, worker.context) = result := by
      simpa [retireLast, workers, released] using success
    rw [← same]
    have effect := release_ok released
    refine ⟨effect.history.wellFormed valid.1, ?_⟩
    intro peer member
    exact effect.peerWorker (separate peer member)
      (valid.2 peer (by rw [workers]; exact List.mem_append_left _ member))

/-- One present manifest constructs a real enabled retirement and establishes
its checked resource, revocation and current-memory postconditions together. -/
theorem retireLast_ready {state : State} {profile : Profile}
    {peers : List Worker} {worker : Worker} {identifier : Atomics64.HandleId64}
    (workers : state.workers = peers ++ [worker]) (valid : WellFormed state profile)
    (ready : Ready state.world worker identifier)
    (separate : ∀ peer ∈ peers, Separate worker.resources peer.resources) :
    ∃ result, retireLast state = .ok result ∧ WellFormed result.1 profile ∧
      published result.1.world = published state.world ∧ result.1.workers = peers ∧
      result.2 = worker.context ∧
      (∀ handle ∈ worker.resources.atomics, Atomics64.HandleRevoked result.1.world handle) ∧
      Borrowing.Revoked result.1.world.legacy.shared worker.resources.code.identifier ∧
      Borrowing.Revoked result.1.world.legacy.shared worker.resources.caller.identifier := by
  obtain ⟨after, released⟩ := release_enabled ready
  have success : retireLast state = .ok (⟨after, peers⟩, worker.context) := by
    simp [retireLast, workers, released]
  have effect := release_ok released
  exact ⟨_, success, retireLast_wellFormed workers valid success separate, effect.currentRAM,
    rfl, rfl, effect.revokes valid.1⟩

#print axioms Ready
#print axioms Separate
#print axioms release
#print axioms retireLast
#print axioms Release
#print axioms release_ok
#print axioms release_enabled
#print axioms retireLast_ok
#print axioms retireLast_enabled
#print axioms Release.history
#print axioms Release.resources
#print axioms Release.currentRAM
#print axioms Release.registry
#print axioms Release.onlyResources
#print axioms Release.revokes
#print axioms Release.peerResources
#print axioms Release.storeGate
#print axioms Release.peerWorker
#print axioms retireLast_frames
#print axioms retireLast_wellFormed
#print axioms retireLast_ready

end EDSL.OS.TSO64.Lifecycle

#audit_edsl
