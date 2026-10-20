/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.FetchAddCalls64
import EDSL.Concurrency.CallTrace.Invocations
import EDSL.X86.CodeCheck

/-!
Present admission for the SysV integer signature `(uint64_t *cell, uint64_t delta)`.
The image and its entry are parameters, not a frozen compiler corpus or a PC
interpreter. Admission binds the entire supplied image to current executable
memory inside the worker's original code loan. It does not identify an ELF.

This layer certifies entry/resources/arguments of accepted finite histories.
It does not prove body correctness, callee-saved preservation, complete-call
progress, acceptance of every admitted execution, all schedules, source ordering,
physical x86-TSO, Linux, or liveness. SIMD/x87 and other unrepresented feature
state remain environmental limitations. Frozen corpus credit additionally needs exact complete ELF
binding, universal body/argument proofs, and progress/nonvacuity obligations.
The corpus baseline remains 4/40 functions, 8/80 artifacts, zero frozen concurrent.
-/

namespace EDSL.OS.FetchAddABI64
open X86 Concurrency

/-- The complete declared byte list, with entry at its base. No compiler,
instruction sequence, expected intermediate PCs, or desired result is fixed. -/
structure Image where
  base : Word
  bytes : List Byte
  deriving DecidableEq, Repr

variable {Id : Type} {target : Atomics64.CellId64} {cell : Atomics64.Cell}

/-- Full words in RDI/RSI are the `PureCall.Argument.word64` interpretation of
the first two SysV integer arguments. A result-bearing PureCall.Spec is not
needed for these present equalities. RSP names the retained ORIGINAL slot. -/
def Present (image : Image) (cell : Atomics64.Cell) (worker : TSO64.Worker)
    (delta : Word) : Prop :=
  worker.phase = .running ∧ worker.pending = [] ∧ worker.context.rip = image.base ∧
  worker.context.registers .rdi = cell.address ∧ worker.context.registers .rsi = delta ∧
  worker.context.registers .rsp = worker.resources.callerAddress ∧
  0 < image.bytes.length ∧ canonical image.base = true ∧
  Borrowing.Subregion ⟨image.base, image.bytes.length⟩ worker.resources.code.loan.region ∧
  worker.resources.callerAddress.toNat + 8 < 2^64 ∧
  canonical (worker.resources.callerAddress + 8) = true

instance (image : Image) (cell : Atomics64.Cell) (worker : TSO64.Worker) (delta : Word) :
    Decidable (Present image cell worker delta) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Represented scalar SysV entry obligations, psABI section 3.2.1/3.2.2:
https://gitlab.com/x86-psABIs/x86-64-ABI/blob/master/x86-64-ABI/low-level-sys-info.tex
DF is RFLAGS bit 10 (Intel SDM volume 1, section 3.4.3.2). Its required clear
state on RETURN remains a separate body/preservation obligation. -/
def ScalarEntry (worker : TSO64.Worker) : Prop :=
  ((worker.context.registers .rsp).toNat + 8) % 16 = 0 ∧
  worker.context.flags.getLsbD 10 = false

instance (worker : TSO64.Worker) : Decidable (ScalarEntry worker) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Check actual present bytes and the existing whole-width handle selector.
The original caller loan reads its current return target; only its canonicality
is checked. No future step, successor invariant, arithmetic or output is queried. -/
def workerGate (image : Image) (state : TSO64.State) (target : Atomics64.CellId64)
    (cell : Atomics64.Cell) (worker : TSO64.Worker) (delta : Word) : Bool :=
  decide (Present image cell worker delta) &&
  decide (ScalarEntry worker) &&
  X86.checkCode (TSO64.published state.world) image.base image.bytes &&
  (match TSO64.atomicFor state.world worker.resources cell.address with
    | none => false
    | some (_, handle, actual) => decide (handle.cell = target ∧ actual = cell)) &&
  (match Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
      worker.resources.caller.identifier worker.resources.callerAddress with
    | .error _ => false
    | .ok returnAddress => canonical returnAddress)

/-- The scheduler tid selects the actual context; its resource actor can be a
different number and can be shared by other contexts. ID uniqueness is Protocol
work, so this present-state gate deliberately does not interpret the ID. -/
def gate (image : Image) (before : FetchAddCalls64.CheckedState target cell)
    (_id : Id) (tid : Nat) (delta : Word) : Bool :=
  match before.state.workers[tid]? with
  | none => false
  | some worker => workerGate image before.state target cell worker delta

/-- Semantic present facts. Current leases retain their complete original
descriptors, owner/epoch checks and actor. ValidCell includes whole8 authority,
natural alignment, nonexecutable data and current RW permissions. -/
structure WorkerFacts (image : Image) (state : TSO64.State) (target : Atomics64.CellId64)
    (cell : Atomics64.Cell) (worker : TSO64.Worker) (delta : Word) : Prop where
  present : Present image cell worker delta
  abi : ScalarEntry worker
  code : CodeAt (TSO64.published state.world) image.base image.bytes
  resources : TSO64.ResourcesValid state.world worker.resources
  live : state.world.cells target = some cell
  validCell : Atomics64.ValidCell state.world.legacy.shared cell
  authority : ∃ identifier handle,
    identifier ∈ worker.resources.atomics ∧
    Atomics64.authorize state.world worker.resources.actor identifier = .ok (handle, cell) ∧
    state.world.handles identifier = some handle ∧ handle.actor = worker.resources.actor ∧
    handle.cell = target
  caller : ∃ returnAddress,
    Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
      worker.resources.caller.identifier worker.resources.callerAddress = .ok returnAddress ∧
    readWord (TSO64.published state.world) worker.resources.callerAddress = .ok returnAddress ∧
    readWord (TSO64.localCPU state worker).memory worker.resources.callerAddress = .ok returnAddress ∧
    canonical returnAddress = true

def EntryFacts (image : Image) (before : FetchAddCalls64.CheckedState target cell)
    (tid : Nat) (delta : Word) : Prop :=
  ∃ worker, before.state.workers[tid]? = some worker ∧
    WorkerFacts image before.state target cell worker delta

/-- Derive current original leases and target authority from WF and the checks,
without checking a desired successor or assuming that RET will ever execute. -/
theorem gate_sound {image : Image} {before : FetchAddCalls64.CheckedState target cell}
    {id : Id} {tid : Nat} {delta : Word} (accepted : gate image before id tid delta = true) :
    EntryFacts image before tid delta := by
  cases found : before.state.workers[tid]? with
  | none => simp [gate, found] at accepted
  | some worker =>
    have checked : workerGate image before.state target cell worker delta = true := by
      simpa only [gate, found] using accepted
    obtain ⟨shapeABICodeAtomic, caller⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨shapeABICode, atomic⟩ := Bool.and_eq_true_iff.mp shapeABICodeAtomic
    obtain ⟨shapeABI, code⟩ := Bool.and_eq_true_iff.mp shapeABICode
    obtain ⟨shape, abi⟩ := Bool.and_eq_true_iff.mp shapeABI
    have entry : Present image cell worker delta := of_decide_eq_true shape
    have workerValid := before.valid.2 worker (List.mem_of_getElem? found)
    refine ⟨worker, found, entry, of_decide_eq_true abi, X86.checkCode_sound _ _ _ code, workerValid.1,
      before.live, (before.valid.1.cells _ _ before.live).2, ?_, ?_⟩
    · cases selected : TSO64.atomicFor before.state.world worker.resources cell.address with
      | none => simp [selected] at atomic
      | some triple =>
        obtain ⟨identifier, handle, actual⟩ := triple
        have same : handle.cell = target ∧ actual = cell := by
          simpa only [selected, decide_eq_true_eq] using atomic
        obtain ⟨linked, sameCell⟩ := same
        subst actual
        obtain ⟨member, authorized, _⟩ := TSO64.atomicFor_sound selected
        have current := Atomics64.authorize_ok _ _ _ _ authorized
        exact ⟨identifier, handle, member, authorized, current.1, current.2.1, linked⟩
    · cases loaded : Borrowing.loadWord64 before.state.world.legacy.shared worker.resources.actor
          worker.resources.caller.identifier worker.resources.callerAddress with
      | error fault => simp [loaded] at caller
      | ok returnAddress =>
        have canonicalReturn : canonical returnAddress = true := by simpa only [loaded] using caller
        have actual := (Borrowing.loadWord64_ok _ _ _ _ _ loaded).choose_spec.2.2
        have sharedRead := readWord_of_loadQWord _ _ _ actual
        exact ⟨returnAddress, rfl, sharedRead,
          (TSO64.local_original_caller before.valid workerValid).trans sharedRead, canonicalReturn⟩

abbrev replay (image : Image) (target : Atomics64.CellId64) (cell : Atomics64.Cell) :=
  CallTrace.Invocations.replay (FetchAddCalls64.adapter Id target cell) (gate image)

abbrev Run (image : Image) (target : Atomics64.CellId64) (cell : Atomics64.Cell) :=
  CallTrace.Invocations.Run (FetchAddCalls64.adapter Id target cell) (gate image)

/-- Exactly one gated replay, followed by the existing complete Protocol
checker. The actual scheduler is not run again by this executable checker. -/
def checkComplete [DecidableEq Id] (image : Image)
    (before : FetchAddCalls64.CheckedState target cell) (entries : List (FetchAddCalls64.Entry Id)) : Bool :=
  match replay image target cell before entries with
  | none => false
  | some result => Linearizability.check result.events

theorem checkComplete_sound [DecidableEq Id] {image : Image}
    {before : FetchAddCalls64.CheckedState target cell} {entries : List (FetchAddCalls64.Entry Id)}
    (accepted : checkComplete image before entries = true) :
    ∃ result, replay image target cell before entries = some result ∧
      Linearizability.Protocol result.events := by
  cases replayed : replay image target cell before entries with
  | none => simp [checkComplete, replayed] at accepted
  | some result =>
    exact ⟨result, rfl, Linearizability.check_sound (by simpa [checkComplete, replayed] using accepted)⟩

/-- Strengthen the generic exact indexed witness at its SAME current prestate.
The actual emitted list, offset and whole event decomposition prevent an equal
label elsewhere from replacing the selected occurrence. Prefix acceptance by
the original executable replay is a theorem, not a second runtime replay. -/
def InvocationAt (image : Image) (before : FetchAddCalls64.CheckedState target cell)
    (entries : List (FetchAddCalls64.Entry Id)) (events : List (FetchAddCalls64.Event Id))
    (index : Nat) (id : Id) (tid : Nat) (delta : Word) : Prop :=
  ∃ earlier later current observations priorEvents selected middle headObservations emitted following offset,
    entries = earlier ++ selected :: later ∧
    Run image target cell before earlier observations current priorEvents ∧
    replay image target cell before earlier = some ⟨current, observations, priorEvents⟩ ∧
    FetchAddCalls64.replay target cell before earlier = some ⟨current, observations, priorEvents⟩ ∧
    TSO64.schedule before.state (CallTrace.actions earlier) = .ok (current.state, observations) ∧
    events = priorEvents ++ (emitted ++ following) ∧
    priorEvents.length + offset = index ∧
    CallTrace.Invocations.Boundary (FetchAddCalls64.adapter Id target cell) (gate image)
      current selected middle headObservations emitted ∧
    emitted[offset]? = some (.invoke id tid delta) ∧ EntryFacts image current tid delta

theorem invocation_at {image : Image} {before : FetchAddCalls64.CheckedState target cell}
    {entries : List (FetchAddCalls64.Entry Id)} {events : List (FetchAddCalls64.Event Id)}
    {index : Nat} {id : Id} {tid : Nat} {delta : Word}
    (located : CallTrace.Invocations.InvocationAt (FetchAddCalls64.adapter Id target cell) (gate image)
      before entries events index id tid delta) :
    InvocationAt image before entries events index id tid delta := by
  obtain ⟨earlier, later, current, observations, priorEvents, selected, middle, headObservations,
    emitted, following, offset, same, earlierRun, replayed, eventEq, length, boundary, found, admitted⟩ := located
  have original := CallTrace.Invocations.replay_original (FetchAddCalls64.adapter Id target cell)
    (gate image) replayed
  exact ⟨earlier, later, current, observations, priorEvents, selected, middle, headObservations,
    emitted, following, offset, same, earlierRun, replayed, original,
    FetchAddCalls64.Run.underlying (CallTrace.replay_sound _ original), eventEq, length, boundary,
    found, gate_sound admitted⟩

/-- Proof-only contract for this very accepted replay. Point/response indexed
boundaries feed FetchAddCalls64.point_at/response_at directly, exposing actual
decoded-source/current-old RMW and original-caller RET/full-RAX origins. -/
structure Complete [DecidableEq Id] (image : Image)
    (before : FetchAddCalls64.CheckedState target cell) (entries : List (FetchAddCalls64.Entry Id))
    (prior : Word) (result : FetchAddCalls64.Result Id target cell) (final : Word) : Prop where
  replayed : replay image target cell before entries = some result
  original : FetchAddCalls64.replay target cell before entries = some result
  admittedRun : Run image target cell before entries result.observations result.state result.events
  callsRun : FetchAddCalls64.Run target cell before entries result.observations result.state result.events
  schedule : CallTrace.schedule (FetchAddCalls64.adapter Id target cell) before (CallTrace.actions entries) =
    .ok (result.state, result.observations)
  underlying : TSO64.schedule before.state (CallTrace.actions entries) = .ok (result.state.state, result.observations)
  history : AtomicFetchAddHistory64.History before.state.world (result.observations.map TSO64History.label)
    result.state.state.world
  live : result.state.state.world.cells target = some cell
  observed : FetchAddCalls64.read result.state.state cell = .ok final
  legal : ModuloCounter.LegalHistory prior final result.events
  linearization : Linearizability.Linearization result.events (fun calls => ModuloCounter.Sequential prior calls final)
  intervals : ∀ interval ∈ Linearizability.intervals result.events,
    InvocationAt image before entries result.events interval.invocation
      interval.call.id interval.call.thread interval.call.input ∧
    CallTrace.EventAt (FetchAddCalls64.adapter Id target cell) before entries interval.point (.point interval.call) ∧
    CallTrace.EventAt (FetchAddCalls64.adapter Id target cell) before entries interval.response
      (.respond interval.call.id interval.call.thread interval.call.output)
  final_fold : final = (Linearizability.calls result.events).foldl (fun value call => value + call.input) prior
  total : final.toNat = (prior.toNat + ModuloCounter.inputSum (Linearizability.calls result.events)) % 2^64

/-- Present admission plus the existing operational counter theorem. This is
conditional soundness of the accepted finite trace, not universal body/progress
correctness. Arithmetic comes from the existing OS projection/Run.sequential. -/
theorem checked_complete [DecidableEq Id] {image : Image}
    {before : FetchAddCalls64.CheckedState target cell} {entries : List (FetchAddCalls64.Entry Id)}
    {prior : Word} (initial : FetchAddCalls64.read before.state cell = .ok prior)
    (accepted : checkComplete image before entries = true) :
    ∃ result final, Complete image before entries prior result final := by
  obtain ⟨result, replayed, protocol⟩ := checkComplete_sound accepted
  have original := CallTrace.Invocations.replay_original (FetchAddCalls64.adapter Id target cell)
    (gate image) replayed
  have run := CallTrace.replay_sound _ original
  have admitted := CallTrace.Invocations.replay_sound (FetchAddCalls64.adapter Id target cell)
    (gate image) replayed
  obtain ⟨final, observed, arithmetic⟩ := FetchAddCalls64.Run.sequential run initial
  rw [← Linearizability.calls_eq_points] at arithmetic
  have legal : ModuloCounter.LegalHistory prior final result.events := ⟨protocol, arithmetic⟩
  have scheduled := FetchAddCalls64.Run.underlying run
  refine ⟨result, final, replayed, original, admitted, run,
    CallTrace.Run.schedule (FetchAddCalls64.adapter Id target cell) run, scheduled,
    TSO64History.schedule_history scheduled, result.state.live, observed, legal, legal.linearization,
    ?_, arithmetic.final_fold, arithmetic.total⟩
  intro interval member
  have boundaries := CallTrace.Run.interval_boundaries (FetchAddCalls64.adapter Id target cell) run protocol member
  exact ⟨invocation_at (CallTrace.Invocations.Run.interval_invocation _ _ admitted protocol member),
    boundaries.2.1, boundaries.2.2⟩

/-- The same protocol interval's actual RMW, with its exact earlier schedule,
decoded source register, current old word and installed machine result. -/
theorem Complete.point_at [DecidableEq Id] {image : Image}
    {before : FetchAddCalls64.CheckedState target cell} {entries : List (FetchAddCalls64.Entry Id)}
    {prior final : Word} {result : FetchAddCalls64.Result Id target cell}
    (complete : Complete image before entries prior result final)
    {interval : Linearizability.Interval Id Nat Word Word}
    (member : interval ∈ Linearizability.intervals result.events) :
    ∃ (earlier later : List (FetchAddCalls64.Entry Id)) (current : FetchAddCalls64.CheckedState target cell)
      (observations : List TSO64.Observation) (priorEvents : List (FetchAddCalls64.Event Id))
      (action : TSO64.Action) (mark : FetchAddCalls64.Mark Id)
      (head : FetchAddCalls64.CheckedState target cell × TSO64.Observation),
      entries = earlier ++ .execute action mark :: later ∧
      FetchAddCalls64.Run target cell before earlier observations current priorEvents ∧
      priorEvents.length = interval.point ∧
      TSO64.schedule before.state (CallTrace.actions earlier) = .ok (current.state, observations) ∧
      TSO64.step current.state action = .ok (head.1.state, head.2) ∧
      FetchAddCalls64.RMWOrigin target current.state action (head.1.state, head.2) interval.call :=
  FetchAddCalls64.point_at (complete.intervals interval member).2.1

/-- The response of that very interval is actual RET/full RAX with the current
original caller loan. RET still says nothing about FIFO publication or release. -/
theorem Complete.response_at [DecidableEq Id] {image : Image}
    {before : FetchAddCalls64.CheckedState target cell} {entries : List (FetchAddCalls64.Entry Id)}
    {prior final : Word} {result : FetchAddCalls64.Result Id target cell}
    (complete : Complete image before entries prior result final)
    {interval : Linearizability.Interval Id Nat Word Word}
    (member : interval ∈ Linearizability.intervals result.events) :
    ∃ (earlier later : List (FetchAddCalls64.Entry Id)) (current : FetchAddCalls64.CheckedState target cell)
      (observations : List TSO64.Observation) (priorEvents : List (FetchAddCalls64.Event Id))
      (action : TSO64.Action) (mark : FetchAddCalls64.Mark Id)
      (head : FetchAddCalls64.CheckedState target cell × TSO64.Observation),
      entries = earlier ++ .execute action mark :: later ∧
      FetchAddCalls64.Run target cell before earlier observations current priorEvents ∧
      priorEvents.length = interval.response ∧
      TSO64.schedule before.state (CallTrace.actions earlier) = .ok (current.state, observations) ∧
      TSO64.step current.state action = .ok (head.1.state, head.2) ∧
      FetchAddCalls64.ReturnOrigin current.state action (head.1.state, head.2)
        interval.call.thread interval.call.output :=
  FetchAddCalls64.response_at (complete.intervals interval member).2.2

end EDSL.OS.FetchAddABI64

#audit_edsl
