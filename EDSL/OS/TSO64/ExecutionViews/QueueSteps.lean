/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Run
import EDSL.OS.TSO64.Queue.SelectionOrder

/-!
Exact cursor changes of the production scheduler, viewed from any live worker.
The classification follows successful dispatch, admission and finish effects;
it introduces no executor, future-success premise or restriction on accesses.

The selector lemmas concern the production exact-start `newestQWord` lookup.
Ignoring a DWORD or a different qword start in that lookup does not frame its
bytes. Byte-overlay/load guarantees still require the existing resources and
compatibility theorems. Managed fresh/other-address append, head removal and
occurrence uniqueness remain the results of `Queue.SelectionOrder`.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.ExecutionViews.QueueSteps
open X86 StoreBuffer.Mixed
open Queue.SelectionOrder

/-- Full cursor equality retains both the complete tagged FIFO and counter. -/
theorem cursor_eq_iff {prior current : Worker} :
    current.storeCursor = prior.storeCursor ↔
      current.pending = prior.pending ∧ current.nextStore = prior.nextStore := by
  constructor
  · intro same
    exact ⟨congrArg Queue.Cursor.pending same, congrArg Queue.Cursor.nextStore same⟩
  · rintro ⟨pending, counter⟩
    change Queue.Cursor.mk current.pending current.nextStore =
      Queue.Cursor.mk prior.pending prior.nextStore
    rw [pending, counter]

/-- A structural cursor-change description. `step_cursor` derives it from an
actual successful scheduler step and both live worker lookups. Append
cases retain the original request and current admission, including the full
ticket or managed reference. Removal records the actual own drain observation,
literal original head/tail, unchanged counter and checked publication effect.
The stable case includes peer steps, blocked issues and successful locked RMWs;
ordinary finish covers both next-instruction and return observations. -/
inductive CursorStep (state : State) (action : Action) (result : State × Observation)
    (profile : Profile) (tid : Nat) (prior current : Worker) : Prop where
  | stable (same : current.storeCursor = prior.storeCursor) :
      CursorStep state action result profile tid prior current
  | ordinary (af : Bool) (instruction : Sequential.Instruction) (store : Store)
      (ticket : Ownership.Ticket)
      (issuing : action = .issue tid af)
      (intent : storeIntent instruction (localCPU state prior) = some store)
      (admission : Queue.Admission state.world prior.resources store prior.nextStore
        profile (.ordinary ticket store))
      (cursor : current.storeCursor = prior.storeCursor.enqueueOrdinary ticket store) :
      CursorStep state action result profile tid prior current
  | managed (af : Bool) (instruction : Sequential.Instruction) (store : Store)
      (reference : Queue.ManagedRef) (value : Word)
      (issuing : action = .issue tid af)
      (intent : storeIntent instruction (localCPU state prior) = some store)
      (admission : Queue.Admission state.world prior.resources store prior.nextStore
        profile (.managed reference value prior.nextStore))
      (authority : Queue.Current state.world prior.resources reference)
      (cursor : current.storeCursor = prior.storeCursor.enqueueManaged reference value) :
      CursorStep state action result profile tid prior current
  | drained (head : Pending) (tail : List Pending)
      (output : World × Option Atomics64.StoreEvent64)
      (draining : action = .drain tid)
      (observed : result.2 = .drained tid head)
      (fifo : prior.pending = head :: tail)
      (pending : current.pending = tail)
      (counter : current.nextStore = prior.nextStore)
      (gate : PendingValid state.world prior.resources head profile)
      (changed : Queue.Effect state.world prior.resources head output)
      (installed : result.1 = install state tid output.1 { prior with pending := tail }) :
      CursorStep state action result profile tid prior current

private theorem installed_worker_eq {state : State} {tid : Nat} {world : World}
    {prior replacement current : Worker}
    (priorLive : state.workers[tid]? = some prior)
    (currentLive : (install state tid world replacement).workers[tid]? = some current) :
    current = replacement := by
  have installed : (install state tid world replacement).workers[tid]? = some replacement :=
    List.getElem?_set_self (List.getElem_of_getElem? priorLive).1
  exact Option.some.inj (currentLive.symm.trans installed)

private theorem finish_cursor {state : State} {tid : Nat} {worker current : Worker}
    {pending : List Pending} {observation : Sequential.Observation}
    {result : State × Observation} {nextStore : Nat}
    (live : state.workers[tid]? = some worker)
    (finish : FinishEffect state tid worker pending observation result nextStore)
    (currentLive : result.1.workers[tid]? = some current) :
    current.storeCursor = ⟨pending, nextStore⟩ := by
  cases finish <;> exact congrArg Worker.storeCursor (installed_worker_eq live currentLive)

/-- Peer actions retain the entire viewed cursor, regardless of publication
or RMW changes to the shared world. Both endpoint workers are actual lookups. -/
theorem step_peer_cursor {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {tid : Nat} {prior current : Worker}
    (success : step state action profile = .ok result)
    (different : tid ≠ (match action with | .issue issuer _ | .drain issuer => issuer))
    (priorLive : state.workers[tid]? = some prior)
    (currentLive : result.1.workers[tid]? = some current) :
    current.storeCursor = prior.storeCursor := by
  have unchanged := step_peer success different
  have same : current = prior :=
    Option.some.inj (currentLive.symm.trans (unchanged.trans priorLive))
  exact congrArg Worker.storeCursor same

/-- Exhaustive cursor classification for an arbitrary viewed live worker.
There is no well-formedness, empty-initial-queue or single-access premise.
Every append comes from the current real admission; the removal case is the
real drain of this worker, rather than an assumed pending-entry disappearance. -/
theorem step_cursor {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {tid : Nat} {prior current : Worker}
    (success : step state action profile = .ok result)
    (priorLive : state.workers[tid]? = some prior)
    (currentLive : result.1.workers[tid]? = some current) :
    CursorStep state action result profile tid prior current := by
  cases action with
  | issue issuer af =>
    by_cases same : tid = issuer
    · subst issuer
      obtain ⟨worker, live, _running, _code, _caller, instruction, _fetched, effect⟩ :=
        issue_effect (profile := profile) success
      have workerEq : worker = prior := Option.some.inj (live.symm.trans priorLive)
      subst worker
      cases instruction with
      | ordinary instruction =>
        cases effect with
        | intro _supported _bounds _decoded _reads queue _executed finish =>
          cases queue with
          | unchanged _intent => exact .stable (finish_cursor live finish currentLive)
          | enqueued intent admission =>
            cases admission with
            | ordinary ticket selected =>
              exact .ordinary af instruction _ ticket rfl intent (.ordinary ticket selected)
                (finish_cursor live finish currentLive)
            | managed reference value ordinaryAbsent shared qword selected =>
              have admitted : Queue.Admission state.world prior.resources _ prior.nextStore profile
                  (.managed reference value prior.nextStore) :=
                .managed reference value ordinaryAbsent shared qword selected
              exact .managed af instruction _ reference value rfl intent admitted admitted.valid.2
                (finish_cursor live finish currentLive)
      | locked instruction =>
        cases effect with
        | blocked _bounds _nonempty =>
          have workerEq : current = prior := Option.some.inj (currentLive.symm.trans priorLive)
          exact .stable (congrArg Worker.storeCursor workerEq)
        | rmw _bounds _empty _decoded _selected _changed _executed =>
          have same := installed_worker_eq live currentLive
          subst current
          exact .stable rfl
    · exact .stable (step_peer_cursor success same priorLive currentLive)
  | drain issuer =>
    by_cases same : tid = issuer
    · subst issuer
      obtain ⟨worker, head, tail, output, live, fifo, gate, changed, resultEq⟩ :=
        drain_effect (profile := profile) success
      have workerEq : worker = prior := Option.some.inj (live.symm.trans priorLive)
      subst worker
      subst result
      have currentEq : current = { prior with pending := tail } :=
        installed_worker_eq live currentLive
      subst current
      exact .drained head tail output rfl rfl fifo rfl rfl gate changed rfl
    · exact .stable (step_peer_cursor success same priorLive currentLive)

/-- A real own RMW retains an actually empty FIFO at both endpoints, as well
as the full unchanged cursor. Peer RMWs need no emptiness of the viewed FIFO. -/
theorem step_own_rmw_empty {state after : State} {action : Action} {profile : Profile}
    {tid : Nat} {event : Atomics64.FetchAddEvent} {prior current : Worker}
    (success : step state action profile = .ok (after, .rmw tid event))
    (priorLive : state.workers[tid]? = some prior)
    (currentLive : after.workers[tid]? = some current) :
    prior.pending = [] ∧ current.pending = [] ∧ current.storeCursor = prior.storeCursor := by
  cases step_origin (profile := profile) success with
  | ordinary _live _running _code _caller _fetched effect =>
    cases effect with
    | intro _supported _bounds _decoded _reads _queue _executed finish => cases finish
  | rmw live _running _code _caller _fetched _bounds empty _grant _effect =>
    have workerEq := Option.some.inj (priorLive.symm.trans live)
    subst prior
    have currentEq := installed_worker_eq live currentLive
    subst current
    exact ⟨empty, empty, rfl⟩

/-- Connect an actual literal head removal to SelectionOrder's existing
dropHead results. This equality alone makes no publication claim. -/
theorem dropHead_cursor {prior current : Worker} {head : Pending} {tail : List Pending}
    (fifo : prior.pending = head :: tail) (remaining : current.pending = tail)
    (counter : current.nextStore = prior.nextStore) :
    current.storeCursor = prior.storeCursor.dropHead := by
  change Queue.Cursor.mk current.pending current.nextStore =
    Queue.Cursor.mk prior.pending.tail prior.nextStore
  simp only [fifo, remaining, counter, List.tail_cons]

/-- Exact-start selection ignores an appended DWORD even at the queried start.
Its bytes still participate in the production overlay. -/
theorem newestQWord_append_dword (buffer : Buffer) (address other : Word)
    (value : BitVec 32) :
    newestQWord (buffer ++ [⟨other, .dword value⟩]) address = newestQWord buffer address := by
  induction buffer with
  | nil => rfl
  | cons head tail ih => simp only [List.cons_append, newestQWord, ih]

/-- A different qword start preserves the exact selector, including absence
and the original snapshot index. Distinct starts need not have disjoint bytes. -/
theorem newestQWord_append_qword_other (buffer : Buffer) (address other value : Word)
    (different : other ≠ address) :
    newestQWord (buffer ++ [⟨other, .qword value⟩]) address = newestQWord buffer address := by
  induction buffer with
  | nil => simp [newestQWord, different]
  | cons head tail ih => simp only [List.cons_append, newestQWord, ih]

/-- The ordinary ticket is retained while projecting the exact appended DWORD. -/
theorem newestQWord_append_ordinary_dword (entries : List Pending)
    (ticket : Ownership.Ticket) (address other : Word) (value : BitVec 32) :
    newestQWord (Queue.payload (entries ++ [.ordinary ticket ⟨other, .dword value⟩])) address =
      newestQWord (Queue.payload entries) address := by
  rw [Queue.payload_enqueue]
  exact newestQWord_append_dword (Queue.payload entries) address other value

/-- Ordinary qword appends at a different start retain the exact production
selector. This structural result requires no authority or byte framing. -/
theorem newestQWord_append_ordinary_qword_other (entries : List Pending)
    (ticket : Ownership.Ticket) (address other value : Word) (different : other ≠ address) :
    newestQWord (Queue.payload (entries ++ [.ordinary ticket ⟨other, .qword value⟩])) address =
      newestQWord (Queue.payload entries) address := by
  rw [Queue.payload_enqueue]
  exact newestQWord_append_qword_other (Queue.payload entries) address other value different

/-- Current ordinary authority cannot start at any current managed target,
including a target authorized by another worker's resources. The stronger byte
disjointness fact comes from StoreGate.managed_disjoint, not address inequality. -/
theorem ordinary_address_ne {world : World} {actor : Nat} {ticket : Ownership.Ticket}
    {store : Store} {targetResources : Resources} {target : Queue.ManagedRef}
    (valid : Atomics64.WellFormed world) (gate : StoreGate world actor ticket store)
    (current : Queue.Current world targetResources target) : store.address ≠ target.cell.address := by
  intro same
  have separate := gate.managed_disjoint valid current 0 (by decide)
  rw [← same] at separate
  cases value : store.value <;> simp [StoreBuffer.Mixed.Store.width, value] at separate

/-- A currently authorized ordinary append retains selection or absence at a
current managed target. This is independent of any future drain or run order. -/
theorem newestQWord_enqueue_ordinary {world : World} {actor : Nat}
    {ticket : Ownership.Ticket} {store : Store} {targetResources : Resources}
    {target : Queue.ManagedRef} (cursor : Queue.Cursor)
    (valid : Atomics64.WellFormed world) (gate : StoreGate world actor ticket store)
    (current : Queue.Current world targetResources target) :
    newestQWord (Queue.payload (cursor.enqueueOrdinary ticket store).pending) target.cell.address =
      newestQWord (Queue.payload cursor.pending) target.cell.address := by
  have different := ordinary_address_ne valid gate current
  cases store with
  | mk address value =>
    cases value with
    | dword value =>
      exact newestQWord_append_ordinary_dword cursor.pending ticket target.cell.address address value
    | qword value =>
      exact newestQWord_append_ordinary_qword_other cursor.pending ticket
        target.cell.address address value different

/-- The real ordinary admission supplies StoreGate; a selector result need
not be supplied. The equality preserves both some-origin and none results. -/
theorem newestQWord_enqueue_ordinary_admitted {world : World} {resources : Resources}
    {ticket : Ownership.Ticket} {store : Store} {profile : Profile}
    {targetResources : Resources} {target : Queue.ManagedRef} (cursor : Queue.Cursor)
    (valid : Atomics64.WellFormed world)
    (admission : Queue.Admission world resources store cursor.nextStore profile (.ordinary ticket store))
    (current : Queue.Current world targetResources target) :
    newestQWord (Queue.payload (cursor.enqueueOrdinary ticket store).pending) target.cell.address =
      newestQWord (Queue.payload cursor.pending) target.cell.address :=
  newestQWord_enqueue_ordinary cursor valid admission.valid.2 current

/-- An ordinary admitted append retains the selected complete managed tag,
value, occurrence and snapshot index at the current target. -/
def enqueueOrdinary_selection {world : World} {resources : Resources}
    {ticket : Ownership.Ticket} {store : Store} {profile : Profile}
    {targetResources : Resources} {target : Queue.ManagedRef} {cursor : Queue.Cursor}
    {origin : QWordOrigin}
    (selection : ManagedSelection cursor target.cell.address origin)
    (valid : Atomics64.WellFormed world)
    (admission : Queue.Admission world resources store cursor.nextStore profile (.ordinary ticket store))
    (current : Queue.Current world targetResources target) :
    ManagedSelection (cursor.enqueueOrdinary ticket store) target.cell.address origin where
  reference := selection.reference
  occurrence := selection.occurrence
  selected := by
    change (cursor.pending ++ [.ordinary ticket store])[origin.index]? = _
    rw [List.getElem?_append_left (List.getElem_of_getElem? selection.selected).1]
    exact selection.selected
  address := selection.address
  newest := (newestQWord_enqueue_ordinary_admitted cursor valid admission current).trans selection.newest

/-- Equal full cursors retain the exact selector result at every address. -/
theorem newestQWord_of_cursor_eq {prior current : Queue.Cursor}
    (same : current = prior) (address : Word) :
    newestQWord (Queue.payload current.pending) address =
      newestQWord (Queue.payload prior.pending) address := by
  rw [same]

/-- Transport an actual selection through full cursor equality, keeping the
complete descriptor and occurrence rather than reselecting by equal values. -/
def transportSelection {prior current : Queue.Cursor} {address : Word} {origin : QWordOrigin}
    (same : current = prior) (selection : ManagedSelection prior address origin) :
    ManagedSelection current address origin where
  reference := selection.reference
  occurrence := selection.occurrence
  selected := by
    rw [congrArg Queue.Cursor.pending same]
    exact selection.selected
  address := selection.address
  newest := (newestQWord_of_cursor_eq same address).trans selection.newest

end EDSL.OS.TSO64.ExecutionViews.QueueSteps

#audit_edsl
