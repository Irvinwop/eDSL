/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Model

/-!
Executable annotation of the production scheduler. The annotation is never an
execution input. Its source contracts mention actual operand reads, queue tags,
authorization lookups and successful instruction effects independently of the
classifier. No source orders or C23 legality assumptions occur here.

Execution erasure holds for arbitrary inputs. Event soundness additionally uses
the existing world/resource and queue-numbering invariants. Incoming queues and
writer maps are explicit boundaries, not invented earlier instruction issues.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open X86

/-- Select a writer by the production forwarding selector and its exact tagged
entry. Payload equality is never used to search for a writer. An inconsistent
arbitrary queue may fail classification; `WellFormed` and `Sequenced` exclude
that case for an actual admitted managed read. -/
def readKey (worker : Worker) (tid : Nat) (reference : Queue.ManagedRef)
    (writers : PublishedHistory.Writers) : Option WriterId :=
  match StoreBuffer.Mixed.newestQWord (payload worker.pending) reference.cell.address with
  | none => some (publishedSource writers reference.handle.cell)
  | some selector =>
      match worker.pending[selector.index]? with
      | some (.managed _ _ occurrence) => some (.store tid occurrence)
      | _ => none

/-- Independent source facts for the actual loaded word. The forwarded case
retains the exact selector, complete entry, current authority and occurrence
bound. The published case retains absence of forwarding and the real RAM read;
its writer key is precisely the supplied map's selection for this cell. -/
inductive LoadSource (state : State) (worker : Worker) (tid : Nat)
    (reference : Queue.ManagedRef) (value : Word) (writers : PublishedHistory.Writers) :
    WriterId → Prop where
  | forwarded (selector : StoreBuffer.Mixed.QWordOrigin) (writer : Queue.ManagedRef)
      (occurrence : Nat)
      (newest : StoreBuffer.Mixed.newestQWord (payload worker.pending)
        reference.cell.address = some selector)
      (entry : worker.pending[selector.index]? = some (.managed writer value occurrence))
      (payload : selector.value = value)
      (address : writer.cell.address = reference.cell.address)
      (current : Queue.Current state.world worker.resources writer)
      (below : occurrence < worker.nextStore) :
      LoadSource state worker tid reference value writers (.store tid occurrence)
  | published
      (absent : StoreBuffer.Mixed.newestQWord (payload worker.pending)
        reference.cell.address = none)
      (read : loadQWord (published state.world) reference.cell.address = .ok value) :
      LoadSource state worker tid reference value writers
        (publishedSource writers reference.handle.cell)

theorem LoadSource.key {state : State} {worker : Worker} {tid : Nat}
    {reference : Queue.ManagedRef} {value : Word} {writers : PublishedHistory.Writers}
    {source : WriterId} (actual : LoadSource state worker tid reference value writers source) :
    readKey worker tid reference writers = some source := by
  cases actual with
  | forwarded selector writer occurrence newest entry payload address current below =>
      simp only [readKey, newest, entry]
  | published absent read => simp only [readKey, absent]

/-- Forget only the key annotation, retaining the existing production read
source contract. This permits reuse of `ManagedReadSource.history`. -/
theorem LoadSource.managed {state : State} {worker : Worker} {tid : Nat}
    {reference : Queue.ManagedRef} {value : Word} {writers : PublishedHistory.Writers}
    {source : WriterId} (actual : LoadSource state worker tid reference value writers source) :
    ManagedReadSource state worker reference value := by
  cases actual with
  | forwarded selector writer occurrence newest entry payload address current below =>
      exact .forwarded selector writer occurrence newest entry payload address current below
  | published absent read => exact .published absent read

/-- A source at a real prefix also retains the existing exact initial-entry or
same-thread instruction-issue provenance for its forwarded occurrence. -/
theorem LoadSource.history {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {worker : Worker} {tid : Nat}
    {reference : Queue.ManagedRef} {value : Word} {writers : PublishedHistory.Writers}
    {source : WriterId} (actual : LoadSource result.1 worker tid reference value writers source)
    (success : schedule initial actions profile = .ok result)
    (live : result.1.workers[tid]? = some worker) :
    ManagedReadHistory initial actions result profile tid worker reference value :=
  ManagedReadSource.history actual.managed success live

/-- Source existence follows from the actual local load and preserved resource
and numerical invariants, rather than a caller's classification oracle. -/
theorem load_source_exists {state : State} {worker : Worker} {tid : Nat}
    {profile : Profile} {reference : Queue.ManagedRef} {value : Word}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (live : state.workers[tid]? = some worker)
    (current : Queue.Current state.world worker.resources reference)
    (loaded : loadQWord (localCPU state worker).memory reference.cell.address = .ok value)
    (writers : PublishedHistory.Writers) :
    ∃ source, LoadSource state worker tid reference value writers source := by
  have actual := managed_read_source valid (valid.2 worker (List.mem_of_getElem? live))
    (sequenced worker (List.mem_of_getElem? live)) current loaded
  cases actual with
  | forwarded selector writer occurrence newest entry payload address current below =>
      exact ⟨.store tid occurrence,
        .forwarded selector writer occurrence newest entry payload address current below⟩
  | published absent read =>
      exact ⟨publishedSource writers reference.handle.cell, .published absent read⟩

private theorem readKey_sound {state : State} {worker : Worker} {tid : Nat}
    {profile : Profile} {reference : Queue.ManagedRef} {value : Word}
    {writers : PublishedHistory.Writers} {source : WriterId}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (live : state.workers[tid]? = some worker)
    (current : Queue.Current state.world worker.resources reference)
    (loaded : loadQWord (localCPU state worker).memory reference.cell.address = .ok value)
    (selected : readKey worker tid reference writers = some source) :
    LoadSource state worker tid reference value writers source := by
  obtain ⟨actual, origin⟩ := load_source_exists valid sequenced live current loaded writers
  have same : source = actual := Option.some.inj (selected.symm.trans origin.key)
  subst source
  exact origin

/-- A real retiring, guarded decoded MOV64 with the executor's managed fallback
admission and the exact evaluated prestate operand. These facts do not mention
`capture`. In particular an ordinary owned read is not a managed read. -/
inductive LoadOrigin (state : State) (action : Action) (result : State × Observation)
    (profile : Profile) (tid : Nat) (reference : Queue.ManagedRef) (value : Word) : Prop where
  | intro {af : Bool} {worker : Worker} {destination : Register} {address : Sequential.Address}
      (issuing : action = .issue tid af)
      (live : state.workers[tid]? = some worker)
      (fetched : decode (fetchCPU state worker) =
        .ok (.ordinary (.loadMem64 destination address)))
      (effect : OrdinaryEffect state tid worker (.loadMem64 destination address) af result profile)
      (shared : profile = .sharedCell)
      (ordinaryAbsent : grantFor state.world worker.resources
        ⟨address.eval (localCPU state worker), .qword 0⟩ = none)
      (selected : atomicFor state.world worker.resources (address.eval (localCPU state worker)) =
        some (reference.identifier, reference.handle, reference.cell))
      (current : Queue.Current state.world worker.resources reference)
      (operand : reference.cell.address = address.eval (localCPU state worker))
      (loaded : loadQWord (localCPU state worker).memory reference.cell.address = .ok value) :
      LoadOrigin state action result profile tid reference value

/-- Source-independent successful access origins. Stores are actual committed
issues; RMWs retain the complete actual observed event and `Run.Origin`'s
authority/context bridge. Loads retain both their instruction and their exact
forwarding-or-publication contract. -/
inductive AtomicStep (state : State) (action : Action) (result : State × Observation)
    (profile : Profile) (position : Nat) (writers : PublishedHistory.Writers) : Event → Prop where
  | load {tid : Nat} {worker : Worker} {reference : Queue.ManagedRef} {value : Word}
      {source : WriterId}
      (origin : LoadOrigin state action result profile tid reference value)
      (live : state.workers[tid]? = some worker)
      (read : LoadSource state worker tid reference value writers source) :
      AtomicStep state action result profile position writers
        ⟨position, tid, .load reference value source⟩
  | store {tid occurrence : Nat} {reference : Queue.ManagedRef} {value : Word}
      (issued : StoreHistory.Issued state action result profile tid (.managed reference value occurrence)) :
      AtomicStep state action result profile position writers
        ⟨position, tid, .store reference value occurrence⟩
  | rmw {tid : Nat} {changed : Atomics64.FetchAddEvent}
      (observed : result.2 = .rmw tid changed)
      (origin : Origin state action result profile) :
      AtomicStep state action result profile position writers
        ⟨position, tid, .rmw changed (publishedSource writers changed.cell)⟩

theorem AtomicStep.position {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {position : Nat} {writers : PublishedHistory.Writers} {event : Event}
    (actual : AtomicStep state action result profile position writers event) :
    event.position = position := by
  cases actual <;> rfl

/-- The load branch reads exactly the current worker's prestate local CPU.
The shared profile and absent ordinary grant reproduce production admission;
only the actual `atomicFor` result is retained, including handle aliases. -/
private def captureRead (state : State) (tid : Nat) (worker : Worker)
    (address : Sequential.Address) (profile : Profile) (position : Nat)
    (writers : PublishedHistory.Writers) : Option Event :=
  match profile with
  | .ownedOnly => none
  | .sharedCell =>
      match grantFor state.world worker.resources ⟨address.eval (localCPU state worker), .qword 0⟩ with
      | some _ => none
      | none =>
          match atomicFor state.world worker.resources (address.eval (localCPU state worker)) with
          | none => none
          | some (identifier, handle, cell) =>
              let reference : Queue.ManagedRef := ⟨identifier, handle, cell⟩
              match loadQWord (localCPU state worker).memory reference.cell.address with
              | .error _ => none
              | .ok value =>
                  (readKey worker tid reference writers).map fun source =>
                    ⟨position, tid, .load reference value source⟩

private def captureLoad (state : State) (action : Action) (profile : Profile)
    (position : Nat) (writers : PublishedHistory.Writers) : Option Event :=
  match action with
  | .drain _ => none
  | .issue tid _ =>
      match state.workers[tid]? with
      | none => none
      | some worker =>
          match decode (fetchCPU state worker) with
          | .ok (.ordinary (.loadMem64 _ address)) =>
              captureRead state tid worker address profile position writers
          | _ => none

/-- Classify a prestate using the *actual* step observation. This performs no
step and supplies no input to execution. Managed plain stores reuse the existing
store-issue classifier. DWORDs, owned accesses, drains, blocked attempts, RET and
register-only instructions contribute no atomic event. -/
def capture (state : State) (action : Action) (actualObservation : Observation)
    (profile : Profile) (position : Nat) (writersBefore : PublishedHistory.Writers) : Option Event :=
  match actualObservation with
  | .rmw tid event =>
      some ⟨position, tid, .rmw event (publishedSource writersBefore event.cell)⟩
  | .ordinary _ =>
      match StoreHistory.Trace.capture state action profile with
      | some (tid, .managed reference value occurrence) =>
          some ⟨position, tid, .store reference value occurrence⟩
      | _ => captureLoad state action profile position writersBefore
  | _ => none

private theorem captureRead_sound {state : State} {tid : Nat} {worker : Worker}
    {destination : Register} {address : Sequential.Address} {af : Bool}
    {result : State × Observation} {profile : Profile} {position : Nat}
    {writers : PublishedHistory.Writers} {event : Event}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (live : state.workers[tid]? = some worker)
    (fetched : decode (fetchCPU state worker) = .ok (.ordinary (.loadMem64 destination address)))
    (effect : OrdinaryEffect state tid worker (.loadMem64 destination address) af result profile)
    (captured : captureRead state tid worker address profile position writers = some event) :
    AtomicStep state (.issue tid af) result profile position writers event := by
  cases profile with
  | ownedOnly => simp only [captureRead, reduceCtorEq] at captured
  | sharedCell =>
      cases grant : grantFor state.world worker.resources
          ⟨address.eval (localCPU state worker), .qword 0⟩ with
      | some ticket => simp only [captureRead, grant, reduceCtorEq] at captured
      | none =>
          cases selected : atomicFor state.world worker.resources (address.eval (localCPU state worker)) with
          | none => simp only [captureRead, grant, selected, reduceCtorEq] at captured
          | some descriptor =>
              rcases descriptor with ⟨identifier, handle, cell⟩
              let reference : Queue.ManagedRef := ⟨identifier, handle, cell⟩
              have current : Queue.Current state.world worker.resources reference :=
                ⟨(atomicFor_sound selected).1, (atomicFor_sound selected).2.1⟩
              have operand : reference.cell.address = address.eval (localCPU state worker) :=
                (atomicFor_sound selected).2.2
              cases loaded : loadQWord (localCPU state worker).memory reference.cell.address with
              | error fault =>
                  dsimp only [reference] at loaded
                  simp only [captureRead, grant, selected, loaded, reduceCtorEq] at captured
              | ok value =>
                  dsimp only [reference] at loaded
                  cases key : readKey worker tid reference writers with
                  | none =>
                      dsimp only [reference] at key
                      simp only [captureRead, grant, selected, loaded, key,
                        Option.map_none, reduceCtorEq] at captured
                  | some source =>
                      dsimp only [reference] at key
                      have same : (⟨position, tid, .load reference value source⟩ : Event) = event := by
                        simpa only [captureRead, grant, selected, loaded, key,
                          Option.map_some, Option.some.injEq] using captured
                      subst event
                      exact .load (.intro rfl live fetched effect rfl grant selected current operand loaded)
                        live (readKey_sound valid sequenced live current loaded key)

private theorem captureLoad_sound {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {position : Nat} {writers : PublishedHistory.Writers} {event : Event}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (success : step state action profile = .ok result)
    (captured : captureLoad state action profile position writers = some event) :
    AtomicStep state action result profile position writers event := by
  cases action with
  | drain tid => simp only [captureLoad, reduceCtorEq] at captured
  | issue tid af =>
      cases live : state.workers[tid]? with
      | none => simp only [captureLoad, live, reduceCtorEq] at captured
      | some worker =>
          cases fetched : decode (fetchCPU state worker) with
          | error fault => simp only [captureLoad, live, fetched, reduceCtorEq] at captured
          | ok decoded =>
              cases decoded with
              | locked instruction => simp only [captureLoad, live, fetched, reduceCtorEq] at captured
              | ordinary instruction =>
                  cases instruction <;>
                    simp only [captureLoad, live, fetched, reduceCtorEq] at captured
                  exact captureRead_sound valid sequenced live fetched
                    (issue_ordinary_effect live fetched success) captured

/-- Sound classification needs the existing invariants only for recovering the
managed tag behind actual whole-word forwarding. The executor's success supplies
the guarded instruction, real admission and RMW authority, not the classifier. -/
theorem capture_sound {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {position : Nat} {writers : PublishedHistory.Writers} {event : Event}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (success : step state action profile = .ok result)
    (captured : capture state action result.2 profile position writers = some event) :
    AtomicStep state action result profile position writers event := by
  cases observed : result.2 with
  | returned tid => simp only [capture, observed, reduceCtorEq] at captured
  | blocked tid => simp only [capture, observed, reduceCtorEq] at captured
  | drained tid entry => simp only [capture, observed, reduceCtorEq] at captured
  | rmw tid changed =>
      have same : (⟨position, tid, .rmw changed (publishedSource writers changed.cell)⟩ : Event) = event := by
        simpa only [capture, observed, Option.some.injEq] using captured
      subst event
      exact .rmw observed (step_origin success)
  | ordinary observedTid =>
      cases selected : StoreHistory.Trace.capture state action profile with
      | none =>
          apply captureLoad_sound valid sequenced success
          simpa only [capture, observed, selected] using captured
      | some pair =>
          rcases pair with ⟨tid, entry⟩
          cases entry with
          | ordinary ticket store =>
              apply captureLoad_sound valid sequenced success
              simpa only [capture, observed, selected] using captured
          | managed reference value occurrence =>
              have same : (⟨position, tid, .store reference value occurrence⟩ : Event) = event := by
                simpa only [capture, observed, selected, Option.some.injEq] using captured
              subst event
              exact .store (StoreHistory.Trace.capture_sound success selected)

private theorem issued_observation {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {tid : Nat} {entry : Pending}
    (issued : StoreHistory.Issued state action result profile tid entry) :
    result.2 = .ordinary tid := by
  cases issued with
  | ordinary issuing success live fetched effect intent admission committed =>
      cases effect with
      | intro supported bounds decoded reads queue actual finish =>
          cases finish with
          | next outcome => rfl
          | returned outcome =>
              have executed := actual
              rw [Sequential.step_eq_execute _ decoded] at executed
              have onlyRet := Sequential.execute_returned_only_ret executed outcome
              rw [onlyRet] at intent
              simp only [storeIntent, Sequential.Instruction.storeIntent64,
                Sequential.Instruction.storeIntent, X86.Instruction.storeIntent,
                Option.map_none, reduceCtorEq] at intent

private theorem load_store_absent {state : State} {tid : Nat} {af : Bool} {worker : Worker}
    {destination : Register} {address : Sequential.Address} {profile : Profile}
    (live : state.workers[tid]? = some worker)
    (fetched : decode (fetchCPU state worker) = .ok (.ordinary (.loadMem64 destination address))) :
    StoreHistory.Trace.capture state (.issue tid af) profile = none := by
  simp only [StoreHistory.Trace.capture, live, fetched, storeIntent,
    Sequential.Instruction.storeIntent64, Sequential.Instruction.storeIntent, Option.map_none]

/-- Every independently specified actual access is captured. This converse
does not need additional invariants: the load-source witness already retains
the actual selector/entry or absent-forwarding facts. -/
theorem capture_complete {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {position : Nat} {writers : PublishedHistory.Writers} {event : Event}
    (actual : AtomicStep state action result profile position writers event) :
    capture state action result.2 profile position writers = some event := by
  cases actual with
  | store issued =>
      simp only [capture, issued_observation issued, StoreHistory.Trace.capture_complete issued]
  | rmw observed origin => simp only [capture, observed]
  | load origin sourceLive source =>
      cases origin with
      | @intro af worker destination address issuing live fetched effect shared ordinaryAbsent selected current operand loaded =>
          subst action
          have sameWorker := Option.some.inj (sourceLive.symm.trans live)
          cases sameWorker
          obtain ⟨value, read, authority, installed⟩ := effect.loadMem64
          have observed := congrArg Prod.snd installed
          have storeAbsent := load_store_absent (af := af) (profile := profile) live fetched
          rw [shared] at storeAbsent
          simp only [capture, observed, storeAbsent, captureLoad, live, fetched,
            captureRead, shared, ordinaryAbsent, selected, loaded, source.key, Option.map_some]

theorem capture_iff_atomicStep {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {position : Nat} {writers : PublishedHistory.Writers} {event : Event}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (success : step state action profile = .ok result) :
    capture state action result.2 profile position writers = some event ↔
      AtomicStep state action result profile position writers event :=
  ⟨capture_sound valid sequenced success, capture_complete⟩

private theorem managed_load_admission {state : State} {worker : Worker} {profile : Profile}
    {address : Sequential.Address} {reference : Queue.ManagedRef}
    (valid : WellFormed state profile)
    (current : Queue.Current state.world worker.resources reference)
    (operand : reference.cell.address = address.eval (localCPU state worker))
    (authority : ReadCurrent state worker ⟨.data, address.eval (localCPU state worker), 8⟩ profile) :
    profile = .sharedCell ∧ grantFor state.world worker.resources
      ⟨address.eval (localCPU state worker), .qword 0⟩ = none := by
  have excluded : ∀ ticket, StoreGate state.world worker.resources.actor ticket
      ⟨address.eval (localCPU state worker), .qword 0⟩ → False := by
    intro ticket gate
    have separate := gate.managed_disjoint valid.1 current
    have impossible := separate 0 (by decide)
    simp [StoreBuffer.Mixed.Store.width, operand] at impossible
  have absent : grantFor state.world worker.resources
      ⟨address.eval (localCPU state worker), .qword 0⟩ = none := by
    cases grant : grantFor state.world worker.resources
        ⟨address.eval (localCPU state worker), .qword 0⟩ with
    | none => rfl
    | some ticket => exact False.elim (excluded ticket (grantFor_sound grant).2)
  cases profile with
  | sharedCell => exact ⟨rfl, absent⟩
  | ownedOnly =>
      simp [ReadCurrent] at authority
      obtain ⟨ticket, member, gate⟩ := authority
      exact False.elim (excluded ticket gate)

private theorem loadMem64_checked {state : State} {tid : Nat} {worker : Worker}
    {destination : Register} {address : Sequential.Address} {af : Bool}
    {result : State × Observation} {profile : Profile}
    (effect : OrdinaryEffect state tid worker (.loadMem64 destination address) af result profile) :
    checkRead state worker ⟨.data, address.eval (localCPU state worker), 8⟩ profile = .ok () := by
  cases effect with
  | intro supported bounds decoded reads queue actual finish =>
      obtain ⟨units, checked⟩ := reads
      cases gate : checkRead state worker ⟨.data, address.eval (localCPU state worker), 8⟩ profile with
      | error fault =>
          simp [Sequential.Instruction.operandReads, List.mapM_cons, gate] at checked
      | ok outcome =>
          cases outcome
          rfl

/-- Any actual MOV64 whose operand has current managed authority produces an
atomic access. The exact descriptor is obtained from the executor's `atomicFor`
lookup, even if the supplied authority uses another handle for that address.
Neither source facts nor a successful classification are caller premises. -/
theorem managed_load_exists {state : State} {tid : Nat} {worker : Worker}
    {destination : Register} {address : Sequential.Address} {af : Bool}
    {result : State × Observation} {profile : Profile} {authorized : Queue.ManagedRef}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (live : state.workers[tid]? = some worker)
    (fetched : decode (fetchCPU state worker) = .ok (.ordinary (.loadMem64 destination address)))
    (effect : OrdinaryEffect state tid worker (.loadMem64 destination address) af result profile)
    (current : Queue.Current state.world worker.resources authorized)
    (operand : authorized.cell.address = address.eval (localCPU state worker))
    (position : Nat) (writers : PublishedHistory.Writers) :
    ∃ (reference : Queue.ManagedRef) (value : Word) (source : WriterId),
      atomicFor state.world worker.resources (address.eval (localCPU state worker)) =
        some (reference.identifier, reference.handle, reference.cell) ∧
      AtomicStep state (.issue tid af) result profile position writers
        ⟨position, tid, .load reference value source⟩ := by
  obtain ⟨value, loaded, authority, installed⟩ := effect.loadMem64
  obtain ⟨shared, ordinaryAbsent⟩ := managed_load_admission valid current operand authority
  have checked := loadMem64_checked effect
  change grantFor state.world worker.resources
    ⟨address.eval (localCPU state worker), .qword (0#64)⟩ = none at ordinaryAbsent
  cases selected : atomicFor state.world worker.resources (address.eval (localCPU state worker)) with
  | none => simp [checkRead, shared, ordinaryAbsent, selected] at checked
  | some descriptor =>
      rcases descriptor with ⟨identifier, handle, cell⟩
      let reference : Queue.ManagedRef := ⟨identifier, handle, cell⟩
      have selectedCurrent : Queue.Current state.world worker.resources reference :=
        ⟨(atomicFor_sound selected).1, (atomicFor_sound selected).2.1⟩
      have selectedOperand : reference.cell.address = address.eval (localCPU state worker) :=
        (atomicFor_sound selected).2.2
      have actualLoad : loadQWord (localCPU state worker).memory reference.cell.address = .ok value := by
        simpa only [selectedOperand] using loaded
      obtain ⟨source, read⟩ := load_source_exists valid sequenced live selectedCurrent actualLoad writers
      exact ⟨reference, value, source, rfl,
        .load (.intro rfl live fetched effect shared ordinaryAbsent selected selectedCurrent
          selectedOperand actualLoad) live read⟩

/-- A real access at an exact original action index. Each constructor retains
the production step and suffix execution. Writer maps advance on *every*
observation, independently of whether an atomic event was emitted. -/
inductive EventAt (profile : Profile) (event : Event) :
    Nat → State → List Action → (State × List Observation) →
      Nat → PublishedHistory.Writers → Prop where
  | head {state : State} {action : Action} {rest : List Action}
      {first : State × Observation} {tail : State × List Observation}
      {offset : Nat} {writers : PublishedHistory.Writers}
      (stepped : step state action profile = .ok first)
      (following : schedule first.1 rest profile = .ok tail)
      (actual : AtomicStep state action first profile offset writers event) :
      EventAt profile event 0 state (action :: rest)
        (tail.1, first.2 :: tail.2) offset writers
  | later {state : State} {action : Action} {rest : List Action}
      {first : State × Observation} {tail : State × List Observation}
      {index offset : Nat} {writers : PublishedHistory.Writers}
      (stepped : step state action profile = .ok first)
      (following : schedule first.1 rest profile = .ok tail)
      (actual : EventAt profile event index first.1 rest tail (offset + 1)
        (PublishedHistory.update writers offset first.2)) :
      EventAt profile event (index + 1) state (action :: rest)
        (tail.1, first.2 :: tail.2) offset writers

theorem EventAt.scheduled {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {index offset : Nat} {writers : PublishedHistory.Writers}
    (actual : EventAt profile event index state actions result offset writers) :
    schedule state actions profile = .ok result := by
  cases actual with
  | head stepped following actual => simp [schedule, stepped, following]
  | later stepped following actual => simp [schedule, stepped, following]

theorem EventAt.position {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {index offset : Nat} {writers : PublishedHistory.Writers}
    (actual : EventAt profile event index state actions result offset writers) :
    event.position = offset + index := by
  induction actual with
  | head stepped following origin => exact origin.position
  | later stepped following actual ih => omega

theorem EventAt.bound {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {index offset : Nat} {writers : PublishedHistory.Writers}
    (actual : EventAt profile event index state actions result offset writers) :
    index < actions.length := by
  induction actual with
  | head => exact Nat.zero_lt_succ _
  | later stepped following actual ih => exact Nat.succ_lt_succ ih

/-- The event's *real* prestate is reached by the successful original prefix.
In the final conjunct `writersBefore` is exactly `after originalOffset
prefixObservations initialWriters`. The parent can therefore use publication
history to resolve RF origins, including silent actions and initial boundaries. -/
theorem EventAt.prestate {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {index offset : Nat} {writers : PublishedHistory.Writers}
    (actual : EventAt profile event index state actions result offset writers) :
    ∃ before action first,
      schedule state (actions.take index) profile = .ok (before, result.2.take index) ∧
      actions[index]? = some action ∧ result.2[index]? = some first.2 ∧
      step before action profile = .ok first ∧
      AtomicStep before action first profile (offset + index)
        (PublishedHistory.after offset (result.2.take index) writers) event := by
  induction actual with
  | head stepped following origin => exact ⟨_, _, _, rfl, rfl, rfl, stepped, origin⟩
  | later stepped following actual ih =>
      obtain ⟨before, action, first, prefixRun, selected, observed, executed, origin⟩ := ih
      refine ⟨before, action, first, ?_, ?_, ?_, executed, ?_⟩
      · simp only [List.take_succ_cons, schedule, stepped, ok_bind, prefixRun, pure_ok]
      · simpa only [List.getElem?_cons_succ] using selected
      · simpa only [List.getElem?_cons_succ] using observed
      · simpa only [List.take_succ_cons, PublishedHistory.after_cons,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using origin

/-- Conversely an independent access origin after a real successful prefix is
an event at that action in the complete execution. Deterministic production
execution identifies the intermediate state and observation; no trace oracle
or equality with `capture` is a premise. -/
theorem EventAt.of_prestate {state before : State} {actions : List Action}
    {result : State × List Observation} {action : Action} {first : State × Observation}
    {profile : Profile} {event : Event} {index offset : Nat} {writers : PublishedHistory.Writers}
    (success : schedule state actions profile = .ok result)
    (prefixRun : schedule state (actions.take index) profile = .ok (before, result.2.take index))
    (selected : actions[index]? = some action)
    (executed : step before action profile = .ok first)
    (origin : AtomicStep before action first profile (offset + index)
      (PublishedHistory.after offset (result.2.take index) writers) event) :
    EventAt profile event index state actions result offset writers := by
  induction index generalizing state before actions result action first offset writers with
  | zero =>
      cases actions with
      | nil => simp at selected
      | cons head rest =>
          obtain ⟨actualFirst, tail, stepped, following, same⟩ := schedule_cons_ok success
          have beforeEq : state = before := congrArg Prod.fst (Except.ok.inj prefixRun)
          subst before
          have actionEq : head = action := by
            simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
          subst action
          have firstEq := Except.ok.inj (stepped.symm.trans executed)
          cases firstEq
          rw [same]
          exact .head stepped following origin
  | succ index ih =>
      cases actions with
      | nil => simp at selected
      | cons head rest =>
          obtain ⟨middle, tail, stepped, following, same⟩ := schedule_cons_ok success
          have prefixNext : schedule middle.1 (rest.take index) profile =
              .ok (before, tail.2.take index) := by
            cases priorRun : schedule middle.1 (rest.take index) profile with
            | error fault =>
                simp [List.take_succ_cons, schedule, stepped, priorRun] at prefixRun
            | ok prior =>
                have equal : (prior.1, middle.2 :: prior.2) =
                    (before, middle.2 :: tail.2.take index) := by
                  simpa only [same, List.take_succ_cons, schedule, stepped, ok_bind,
                    priorRun, pure_ok, Except.ok.injEq] using prefixRun
                have stateEq : prior.1 = before :=
                  congrArg (fun pair : State × List Observation => pair.1) equal
                have observationsEq : middle.2 :: prior.2 = middle.2 :: tail.2.take index :=
                  congrArg (fun pair : State × List Observation => pair.2) equal
                have priorEq : prior = (before, tail.2.take index) :=
                  Prod.ext stateEq (List.cons.inj observationsEq).2
                exact congrArg Except.ok priorEq
          have selectedNext : rest[index]? = some action := by
            simpa only [List.getElem?_cons_succ] using selected
          have originNext : AtomicStep before action first profile (offset + 1 + index)
              (PublishedHistory.after (offset + 1) (tail.2.take index)
                (PublishedHistory.update writers offset middle.2)) event := by
            simpa only [same, List.take_succ_cons, PublishedHistory.after_cons,
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using origin
          rw [same]
          exact .later stepped following (ih following prefixNext selectedNext executed originNext)

private def record (captured : Option Event) (events : List Event) : List Event :=
  match captured with
  | none => events
  | some event => event :: events

private theorem record_mem {captured : Option Event} {events : List Event} {event : Event} :
    event ∈ record captured events ↔ captured = some event ∨ event ∈ events := by
  cases captured with
  | none => simp only [record, reduceCtorEq, false_or]
  | some emitted => simp only [record, List.mem_cons, Option.some.injEq, eq_comm]

/-- Annotate the production scheduler, calling `step` exactly once per action.
Capture uses the prestate and the actual returned observation. The publication
map is updated afterwards; even a nonwriting observation advances the offset.
The first fault is propagated verbatim, with no additional execution check. -/
def scan (state : State) (actions : List Action) (profile : Profile := .ownedOnly)
    (offset : Nat := 0) (writers : PublishedHistory.Writers := PublishedHistory.empty) :
    Except Fault Result :=
  match actions with
  | [] => .ok ⟨state, [], []⟩
  | action :: rest => do
      let first ← step state action profile
      let tail ← scan first.1 rest profile (offset + 1)
        (PublishedHistory.update writers offset first.2)
      return ⟨tail.state, first.2 :: tail.observations,
        record (capture state action first.2 profile offset writers) tail.events⟩

/-- Erasure is the real scheduler, for every input, including every fault.
No well-formedness, sequencing, legality or source-history premise is needed. -/
theorem scan_execution (state : State) (actions : List Action) (profile : Profile)
    (offset : Nat) (writers : PublishedHistory.Writers) :
    (scan state actions profile offset writers).map Result.execution = schedule state actions profile := by
  induction actions generalizing state offset writers with
  | nil => rfl
  | cons action rest ih =>
      cases stepped : step state action profile with
      | error fault => simp [scan, schedule, stepped, Except.map]
      | ok first =>
          have tailExecution := ih first.1 (offset + 1) (PublishedHistory.update writers offset first.2)
          cases following : scan first.1 rest profile (offset + 1)
              (PublishedHistory.update writers offset first.2) with
          | error fault =>
              have scheduled : schedule first.1 rest profile = .error fault := by
                simpa only [following, Except.map] using tailExecution.symm
              simp [scan, schedule, stepped, following, scheduled, Except.map]
          | ok tail =>
              have scheduled : schedule first.1 rest profile = .ok tail.execution := by
                simpa only [following, Except.map] using tailExecution.symm
              simp [scan, schedule, stepped, following, scheduled, Except.map, Result.execution]

theorem scan_scheduled {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {writers : PublishedHistory.Writers} {result : Result}
    (success : scan state actions profile offset writers = .ok result) :
    schedule state actions profile = .ok result.execution := by
  have execution := scan_execution state actions profile offset writers
  rw [success] at execution
  exact execution.symm

theorem scan_error_iff (state : State) (actions : List Action) (profile : Profile)
    (offset : Nat) (writers : PublishedHistory.Writers) (fault : Fault) :
    scan state actions profile offset writers = .error fault ↔
      schedule state actions profile = .error fault := by
  rw [← scan_execution state actions profile offset writers]
  cases scan state actions profile offset writers <;> simp [Except.map]

private theorem scan_cons_ok {state : State} {action : Action} {rest : List Action}
    {profile : Profile} {offset : Nat} {writers : PublishedHistory.Writers} {result : Result}
    (success : scan state (action :: rest) profile offset writers = .ok result) :
    ∃ first tail, step state action profile = .ok first ∧
      scan first.1 rest profile (offset + 1) (PublishedHistory.update writers offset first.2) = .ok tail ∧
      result = ⟨tail.state, first.2 :: tail.observations,
        record (capture state action first.2 profile offset writers) tail.events⟩ := by
  cases stepped : step state action profile with
  | error fault => simp [scan, stepped] at success
  | ok first =>
      cases following : scan first.1 rest profile (offset + 1)
          (PublishedHistory.update writers offset first.2) with
      | error fault => simp [scan, stepped, following] at success
      | ok tail =>
          simp [scan, stepped, following] at success
          exact ⟨first, tail, rfl, following, success.symm⟩

/-- Every emitted event has its independently specified real access origin at
the exact original action index. Initial invariants are preserved by production
execution; callers do not supply invariants or origins for intermediate states. -/
theorem scan_sound {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {writers : PublishedHistory.Writers} {result : Result} {event : Event}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (success : scan state actions profile offset writers = .ok result)
    (member : event ∈ result.events) :
    ∃ index, EventAt profile event index state actions result.execution offset writers := by
  induction actions generalizing state result offset writers with
  | nil =>
      have same : (⟨state, [], []⟩ : Result) = result := Except.ok.inj success
      subst result
      cases member
  | cons action rest ih =>
      obtain ⟨first, tail, stepped, following, same⟩ := scan_cons_ok success
      have scheduled := scan_scheduled following
      have selected : event ∈ record (capture state action first.2 profile offset writers) tail.events := by
        simpa only [same] using member
      rcases record_mem.mp selected with captured | later
      · refine ⟨0, ?_⟩
        rw [same]
        exact .head stepped scheduled (capture_sound valid sequenced stepped captured)
      · obtain ⟨index, actual⟩ := ih (step_wellFormed valid stepped)
          (step_sequenced sequenced stepped) following later
        refine ⟨index + 1, ?_⟩
        rw [same]
        exact .later stepped scheduled actual

/-- No actual specified atomic access is omitted. Determinism identifies the
actual run with the scanner's run; no origin list is supplied to `scan`. -/
theorem scan_complete {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {writers : PublishedHistory.Writers} {result : Result}
    {execution : State × List Observation} {event : Event} {index : Nat}
    (success : scan state actions profile offset writers = .ok result)
    (actual : EventAt profile event index state actions execution offset writers) :
    event ∈ result.events := by
  induction actual generalizing result with
  | head actualStep actualFollowing origin =>
      obtain ⟨first, tail, stepped, following, same⟩ := scan_cons_ok success
      have equal := Except.ok.inj (actualStep.symm.trans stepped)
      cases equal
      rw [same]
      exact record_mem.mpr (.inl (capture_complete origin))
  | later actualStep actualFollowing actual ih =>
      obtain ⟨first, tail, stepped, following, same⟩ := scan_cons_ok success
      have equal := Except.ok.inj (actualStep.symm.trans stepped)
      cases equal
      rw [same]
      exact record_mem.mpr (.inr (ih following))

theorem scan_events_iff {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {writers : PublishedHistory.Writers} {result : Result} {event : Event}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (success : scan state actions profile offset writers = .ok result) :
    event ∈ result.events ↔
      ∃ index, EventAt profile event index state actions result.execution offset writers :=
  ⟨scan_sound valid sequenced success, fun ⟨_, actual⟩ => scan_complete success actual⟩

/-- Coverage usable directly with a successful production prefix and an
independent access origin at its next action. -/
theorem scan_at {state before : State} {actions : List Action} {result : Result}
    {action : Action} {first : State × Observation} {profile : Profile} {event : Event}
    {index offset : Nat} {writers : PublishedHistory.Writers}
    (success : scan state actions profile offset writers = .ok result)
    (prefixRun : schedule state (actions.take index) profile =
      .ok (before, result.observations.take index))
    (selected : actions[index]? = some action)
    (executed : step before action profile = .ok first)
    (origin : AtomicStep before action first profile (offset + index)
      (PublishedHistory.after offset (result.observations.take index) writers) event) :
    event ∈ result.events :=
  scan_complete success (EventAt.of_prestate (scan_scheduled success)
    prefixRun selected executed origin)

/-- Every actual managed store issue is present, with its full original entry
and issue position, whether or not it has drained by the end of the run. -/
theorem scan_store_coverage {state : State} {actions : List Action} {profile : Profile}
    {offset tid occurrence index : Nat} {writers : PublishedHistory.Writers} {result : Result}
    {reference : Queue.ManagedRef} {value : Word}
    (success : scan state actions profile offset writers = .ok result)
    (issued : StoreHistory.IssuedAt profile tid (.managed reference value occurrence)
      index state actions result.execution) :
    (⟨offset + index, tid, .store reference value occurrence⟩ : Event) ∈ result.events := by
  obtain ⟨before, action, first, prefixRun, selected, executed, origin⟩ := issued.prestate
  exact scan_at success prefixRun selected executed (.store origin)

/-- Every actual RMW observation is present, including zero-delta and repeated
equal-valued events. Its source is selected from the map *before* that RMW,
using the original offset and all prefix observations. -/
theorem scan_rmw_coverage {state : State} {actions : List Action} {profile : Profile}
    {offset tid index : Nat} {writers : PublishedHistory.Writers} {result : Result}
    {changed : Atomics64.FetchAddEvent}
    (success : scan state actions profile offset writers = .ok result)
    (observed : result.observations[index]? = some (.rmw tid changed)) :
    (⟨offset + index, tid, .rmw changed (publishedSource
      (PublishedHistory.after offset (result.observations.take index) writers) changed.cell)⟩ : Event) ∈
      result.events := by
  obtain ⟨before, action, next, prefixRun, selected, executed⟩ :=
    ScheduleTrace.observation_at (scan_scheduled success) observed
  exact scan_at success prefixRun selected executed (.rmw rfl (step_origin executed))

/-- No actual valid managed MOV64 can be omitted. The caller supplies the real
prefix, successful step and current operand authority. The scanner theorems
derive both the exact selected handle and the source key, including forwarding
from a nonempty initial FIFO. No quiescence or C23 legality premise is needed. -/
theorem scan_load_coverage {state before : State} {actions : List Action} {result : Result}
    {first : State × Observation} {profile : Profile} {index offset tid : Nat} {af : Bool}
    {writers : PublishedHistory.Writers} {worker : Worker} {authorized : Queue.ManagedRef}
    {destination : Register} {address : Sequential.Address}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (success : scan state actions profile offset writers = .ok result)
    (prefixRun : schedule state (actions.take index) profile =
      .ok (before, result.observations.take index))
    (selected : actions[index]? = some (.issue tid af))
    (executed : step before (.issue tid af) profile = .ok first)
    (live : before.workers[tid]? = some worker)
    (fetched : decode (fetchCPU before worker) = .ok (.ordinary (.loadMem64 destination address)))
    (current : Queue.Current before.world worker.resources authorized)
    (operand : authorized.cell.address = address.eval (localCPU before worker)) :
    ∃ (reference : Queue.ManagedRef) (value : Word) (source : WriterId),
      atomicFor before.world worker.resources (address.eval (localCPU before worker)) =
        some (reference.identifier, reference.handle, reference.cell) ∧
      (⟨offset + index, tid, .load reference value source⟩ : Event) ∈ result.events := by
  obtain ⟨reference, value, source, actualSelection, actual⟩ := managed_load_exists
    (schedule_wellFormed valid prefixRun) (schedule_sequenced sequenced prefixRun)
    live fetched (issue_ordinary_effect live fetched executed) current operand (offset + index)
    (PublishedHistory.after offset (result.observations.take index) writers)
  exact ⟨reference, value, source, actualSelection,
    scan_at success prefixRun selected executed actual⟩

theorem scan_bounds {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {writers : PublishedHistory.Writers} {result : Result} {event : Event}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (success : scan state actions profile offset writers = .ok result)
    (member : event ∈ result.events) :
    offset ≤ event.position ∧ event.position < offset + actions.length := by
  obtain ⟨index, actual⟩ := scan_sound valid sequenced success member
  have position := actual.position
  have bound := actual.bound
  omega

theorem scan_events_ordered {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {writers : PublishedHistory.Writers} {result : Result}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (success : scan state actions profile offset writers = .ok result) :
    result.events.Pairwise (fun first second => first.position < second.position) := by
  induction actions generalizing state result offset writers with
  | nil =>
      have same : (⟨state, [], []⟩ : Result) = result := Except.ok.inj success
      subst result
      exact .nil
  | cons action rest ih =>
      obtain ⟨first, tail, stepped, following, same⟩ := scan_cons_ok success
      have nextValid := step_wellFormed valid stepped
      have nextSequenced := step_sequenced sequenced stepped
      rw [same]
      cases captured : capture state action first.2 profile offset writers with
      | none => simpa only [record, captured] using ih nextValid nextSequenced following
      | some emitted =>
          have position := (capture_sound valid sequenced stepped captured).position
          simp only [record]
          apply List.pairwise_cons.mpr
          constructor
          · intro event member
            have bounds := scan_bounds nextValid nextSequenced following member
            omega
          · exact ih nextValid nextSequenced following

theorem scan_events_nodup {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {writers : PublishedHistory.Writers} {result : Result}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (success : scan state actions profile offset writers = .ok result) : result.events.Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  exact (scan_events_ordered valid sequenced success).imp (fun less same => by
    rw [same] at less
    exact Nat.lt_irrefl _ less)

private theorem positions_nodup {events : List Event}
    (ordered : events.Pairwise (fun first second => first.position < second.position)) :
    (events.map Event.position).Nodup := by
  revert ordered
  induction events with
  | nil => intro ordered; exact .nil
  | cons head tail ih =>
      intro ordered
      obtain ⟨before, orderedTail⟩ := List.pairwise_cons.mp ordered
      change (head.position :: tail.map Event.position).Nodup
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨event, present, same⟩ := List.mem_map.mp member
        exact (Nat.ne_of_lt (before event present)) same.symm
      · exact ih orderedTail

theorem scan_positions_nodup {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {writers : PublishedHistory.Writers} {result : Result}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (success : scan state actions profile offset writers = .ok result) :
    (result.events.map Event.position).Nodup :=
  positions_nodup (scan_events_ordered valid sequenced success)

/-- Successful scan certificate: actual execution, strict original action
order, no duplicate events, and exact coverage by real managed access origins.
This certificate says nothing about a source table, orders or C23 legality. -/
structure Certificate (initial : State) (actions : List Action) (profile : Profile)
    (offset : Nat) (writers : PublishedHistory.Writers) (result : Result) : Prop where
  scheduled : schedule initial actions profile = .ok result.execution
  ordered : result.events.Pairwise (fun first second => first.position < second.position)
  nodup : result.events.Nodup
  positions : (result.events.map Event.position).Nodup
  events : ∀ event, event ∈ result.events ↔
    ∃ index, EventAt profile event index initial actions result.execution offset writers

theorem scan_certificate {state : State} {actions : List Action} {profile : Profile}
    {offset : Nat} {writers : PublishedHistory.Writers} {result : Result}
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (success : scan state actions profile offset writers = .ok result) :
    Certificate state actions profile offset writers result :=
  ⟨scan_scheduled success, scan_events_ordered valid sequenced success,
    scan_events_nodup valid sequenced success, scan_positions_nodup valid sequenced success,
    fun _ => scan_events_iff valid sequenced success⟩

end EDSL.OS.TSO64.C23Projection.AtomicTrace
