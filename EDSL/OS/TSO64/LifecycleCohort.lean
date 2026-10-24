/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Lifecycle

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Finite administrative cleanup for the production TSO64 State and Worker.
Each iteration calls the actual Lifecycle.retireLast on its CURRENT successor
state. There is no instruction scheduler, snapshot restoration or assumption
of future cleanup success. Contexts are returned in last-to-first removal order.
On any error, Except exposes no intermediate state, including states from
earlier successful iterations. Persistent cells, allocations and ownership
grants remain; this is logical capability cleanup, not native OS join.
-/

namespace EDSL.OS.TSO64.Lifecycle
open X86

/-- Exactly `count` actual last-record retirements, against successive worlds.
An iteration with no remaining workers fails with missingWorker; an earlier
iteration may instead fail its checked phase, queue or resource gates. -/
def retireN : Nat → State → Except Fault (State × List Context)
  | 0, state => .ok (state, [])
  | count + 1, state => do
    let head ← retireLast state
    let tail ← retireN count head.1
    return (tail.1, head.2 :: tail.2)

/-- Retire precisely the number of records present at entry. -/
def retireAll (state : State) : Except Fault (State × List Context) :=
  retireN state.workers.length state

/-- Revocation of the worker's actual original logical capabilities. This
does not assert revocation of allocation tickets or destruction of a cell. -/
def WorkerRevoked (world : World) (worker : Worker) : Prop :=
  (∀ identifier ∈ worker.resources.atomics, Atomics64.HandleRevoked world identifier) ∧
    Borrowing.Revoked world.legacy.shared worker.resources.code.identifier ∧
    Borrowing.Revoked world.legacy.shared worker.resources.caller.identifier

/-- A retained record's present Ready data survives one separated release.
Only current resource validity needs transport; the record itself is unchanged. -/
theorem Release.peerReady {before after : World} {worker peer : Worker}
    {identifier : Atomics64.HandleId64} (effect : Release before worker after)
    (separate : Separate worker.resources peer.resources)
    (ready : Ready before peer identifier) : Ready after peer identifier := by
  obtain ⟨phase, empty, handles, valid, distinct⟩ := ready
  exact ⟨phase, empty, handles, effect.peerResources separate valid, distinct⟩

/-- Actual checked histories preserve earlier handle and loan revocations.
Loan persistence uses well-formedness at the history's current starting world. -/
theorem WorkerRevoked.persists {before after : World} {worker : Worker}
    {labels : List (Option Atomics64.Event)} (revoked : WorkerRevoked before worker)
    (valid : Atomics64.WellFormed before) (history : Atomics64.History before labels after) :
    WorkerRevoked after worker := by
  exact ⟨fun identifier member => history.handle_revoked (revoked.1 identifier member),
    history.loan_revoked valid revoked.2.1, history.loan_revoked valid revoked.2.2⟩

/-- Any successful bounded cleanup removes an exact suffix of original
records, returns their current contexts and leaves every retained tid fixed.
Every slot at or beyond the new length is absent, including all removed slots.
This conclusion needs no readiness or well-formedness admission premise. -/
theorem retireN_slots {count : Nat} {state : State} {result : State × List Context}
    (success : retireN count state = .ok result) :
    ∃ removed : List Worker,
      state.workers = result.1.workers ++ removed.reverse ∧ removed.length = count ∧
      result.2 = removed.map Worker.context ∧
      (∀ tid, tid < result.1.workers.length →
        result.1.workers[tid]? = state.workers[tid]?) ∧
      (∀ tid, result.1.workers.length ≤ tid → result.1.workers[tid]? = none) := by
  induction count generalizing state result with
  | zero =>
    have same : (state, []) = result := by
      simpa only [retireN, Except.ok.injEq] using success
    rw [← same]
    refine ⟨[], by simp, rfl, rfl, ?_, ?_⟩
    · intro _ _
      rfl
    · intro tid bound
      exact List.getElem?_eq_none bound
  | succ count ih =>
    cases first : retireLast state with
    | error fault => simp [retireN, first] at success
    | ok middle =>
      cases tail : retireN count middle.1 with
      | error fault => simp [retireN, first, tail] at success
      | ok final =>
        have same : (final.1, middle.2 :: final.2) = result := by
          simpa only [retireN, first, ok_bind, tail, pure_ok, Except.ok.injEq] using success
        obtain ⟨_prefixWorkers, worker, before, _effect, kept, context⟩ := retireLast_ok first
        obtain ⟨removed, middleWorkers, removedLength, contexts, _frames, _absent⟩ := ih tail
        have shape : state.workers = final.1.workers ++ (worker :: removed).reverse := by
          rw [before, ← kept, middleWorkers, List.reverse_cons, List.append_assoc]
        rw [← same]
        refine ⟨worker :: removed, shape, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons, removedLength]
        · simp only [List.map_cons, context, contexts]
        · intro tid bound
          rw [shape, List.getElem?_append_left bound]
        · intro tid bound
          exact List.getElem?_eq_none bound

/-- Present Ready for each original suffix worker, finite ordered pairwise
separation, separation from the retained prefix and current WellFormed CONSTRUCT
a successful finite cleanup. `order` lists workers in last-to-first removal
order; it is proof data, not an alternative executable scheduler.

Every recursive call receives the actual successor world. Its WellFormed and
Ready facts are proved from the preceding release, after the released record
has been removed. All original suffix revocations persist to the final world.
The whole current Ownership.World is preserved, including RAM, permissions,
allocation registry, ownership epochs and the allocation frontier. -/
theorem retireN_ready (order : List Worker) {state : State} {profile : Profile}
    {peers : List Worker} (workers : state.workers = peers ++ order.reverse)
    (valid : WellFormed state profile)
    (ready : ∀ worker ∈ order, ∃ identifier, Ready state.world worker identifier)
    (separate : order.Pairwise (fun retiring peer => Separate retiring.resources peer.resources))
    (prefixSeparate : ∀ worker ∈ order, ∀ peer ∈ peers,
      Separate worker.resources peer.resources) :
    ∃ result, retireN order.length state = .ok result ∧ WellFormed result.1 profile ∧
      result.1.workers = peers ∧ result.2 = order.map Worker.context ∧
      result.1.world.legacy.shared.resources = state.world.legacy.shared.resources ∧
      result.1.world.cells = state.world.cells ∧ published result.1.world = published state.world ∧
      (∃ labels, Atomics64.History state.world labels result.1.world) ∧
      ∀ worker ∈ order, WorkerRevoked result.1.world worker := by
  induction order generalizing state with
  | nil =>
    have kept : state.workers = peers := by
      simpa only [List.reverse_nil, List.append_nil] using workers
    refine ⟨(state, []), rfl, valid, kept, rfl, rfl, rfl, rfl, ⟨[], .refl⟩, ?_⟩
    intro worker member
    cases member
  | cons worker rest ih =>
    obtain ⟨againstRest, restSeparate⟩ := List.pairwise_cons.mp separate
    have currentWorkers : state.workers = (peers ++ rest.reverse) ++ [worker] := by
      simpa only [List.reverse_cons, List.append_assoc] using workers
    have againstRemaining : ∀ peer ∈ peers ++ rest.reverse,
        Separate worker.resources peer.resources := by
      intro peer member
      rcases List.mem_append.mp member with retained | remaining
      · exact prefixSeparate worker List.mem_cons_self peer retained
      · exact againstRest peer (List.mem_reverse.mp remaining)
    obtain ⟨identifier, readyWorker⟩ := ready worker List.mem_cons_self
    obtain ⟨afterWorld, released⟩ := release_enabled readyWorker
    let middle : State := ⟨afterWorld, peers ++ rest.reverse⟩
    have step : retireLast state = .ok (middle, worker.context) := by
      change retireLast state = .ok (⟨afterWorld, peers ++ rest.reverse⟩, worker.context)
      simp [retireLast, currentWorkers, released]
    have middleValid : WellFormed middle profile :=
      retireLast_wellFormed currentWorkers valid step againstRemaining
    have effect : Release state.world worker middle.world := release_ok released
    have readyRest : ∀ peer ∈ rest, ∃ handle, Ready middle.world peer handle := by
      intro peer member
      obtain ⟨handle, peerReady⟩ := ready peer (List.mem_cons_of_mem worker member)
      exact ⟨handle, effect.peerReady (againstRest peer member) peerReady⟩
    have prefixRest : ∀ retiring ∈ rest, ∀ peer ∈ peers,
        Separate retiring.resources peer.resources := by
      intro retiring member peer retained
      exact prefixSeparate retiring (List.mem_cons_of_mem worker member) peer retained
    obtain ⟨tail, tailSuccess, tailValid, tailWorkers, tailContexts, tailResources,
        tailCells, tailRAM, ⟨labels, tailHistory⟩, tailRevoked⟩ :=
      ih (state := middle) rfl middleValid readyRest restSeparate prefixRest
    refine ⟨(tail.1, worker.context :: tail.2), ?_, tailValid, tailWorkers, ?_,
      tailResources.trans effect.resources.1, tailCells.trans effect.resources.2,
      tailRAM.trans effect.currentRAM,
      ⟨[none, none, none] ++ labels, effect.history.trans tailHistory⟩, ?_⟩
    · simp only [List.length_cons, retireN, step, ok_bind, tailSuccess, pure_ok]
    · exact congrArg (List.cons worker.context) tailContexts
    · intro retired member
      rcases List.mem_cons.mp member with same | earlier
      · subst retired
        have revoked : WorkerRevoked middle.world worker := effect.revokes valid.1
        exact revoked.persists middleValid.1 tailHistory
      · exact tailRevoked retired earlier

/-- The whole-cohort specialization. Admission is solely current WellFormed,
Ready for each original worker and finite pairwise Separate in retirement
order. The empty worker list and final revocations are conclusions. No counter
value, spawn/return snapshot, desired successor validity or future success is
an input. No actor/tid equality or inequality is required, and actor labels
carry no native authentication claim. -/
theorem retireAll_ready {state : State} {profile : Profile}
    (valid : WellFormed state profile)
    (ready : ∀ worker ∈ state.workers, ∃ identifier, Ready state.world worker identifier)
    (separate : state.workers.reverse.Pairwise
      (fun retiring peer => Separate retiring.resources peer.resources)) :
    ∃ result, retireAll state = .ok result ∧ WellFormed result.1 profile ∧
      result.1.workers = [] ∧ result.2 = state.workers.reverse.map Worker.context ∧
      result.1.world.legacy.shared.resources = state.world.legacy.shared.resources ∧
      result.1.world.cells = state.world.cells ∧ published result.1.world = published state.world ∧
      (∃ labels, Atomics64.History state.world labels result.1.world) ∧
      ∀ worker ∈ state.workers, WorkerRevoked result.1.world worker := by
  obtain ⟨result, success, afterValid, kept, contexts, resources, cells, ram, history, revoked⟩ :=
    retireN_ready state.workers.reverse (state := state) (peers := [])
      (by simp only [List.reverse_reverse, List.nil_append]) valid
      (fun worker member => ready worker (List.mem_reverse.mp member)) separate
      (by intro _ _ _ impossible; cases impossible)
  refine ⟨result, ?_, afterValid, kept, contexts, resources, cells, ram, history, ?_⟩
  · simpa only [retireAll, List.length_reverse] using success
  · intro worker member
    exact revoked worker (List.mem_reverse.mpr member)

#print axioms retireN
#print axioms retireAll
#print axioms WorkerRevoked
#print axioms Release.peerReady
#print axioms WorkerRevoked.persists
#print axioms retireN_slots
#print axioms retireN_ready
#print axioms retireAll_ready

end EDSL.OS.TSO64.Lifecycle

#audit_edsl
