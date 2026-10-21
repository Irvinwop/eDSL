/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.PlainCallAdmission64
import EDSL.OS.PlainCallFrames64
import EDSL.X86.VCGen.PlainMethods.ABI
import EDSL.X86.VCGen.PlainMethods.Completion
import EDSL.X86.CodeCheck
import tests.TSO64Fixtures
import EDSL.Audit

/-!
Independent, nonempty Plain64 admission with real checked resources. The two
synthetic bodies share a 16-byte RX allocation, but use different complete
four-byte images. Fresh caller slots have SysV entry alignment and are actually
allocated, initialized, protected and read-borrowed. The fixture's old caller
loans remain unused. No frozen ELF or compiler-corpus evidence is claimed.

Incoming queues are created by the production checked enqueue operation:
reader ordinary data, writer managed data, and nonzero counters. These are
explicit incoming boundaries, without invented earlier instruction origins.
Both actual slots have independently bound full64 arguments and logical
occurrences. Only the separate static catalog supplies instruction shapes.

The engine constructs completion from the independent Pre and an actual empty
prefix; publication is a separate drain closure. A concrete execution also
checks full64 read/store behavior across RET and publication. Everything is
within the fixed-resource, sharedCell, scalar-RAM, long-mode/CET-off model with
stable translations/no hidden aliases. Native/source/compiler/kernel, fairness,
open resource lifecycle, complete Claim/Post and frozen-corpus credit remain
separate.
-/

set_option autoImplicit false

namespace EDSL.Tests.PlainCallAdmission64
open X86 OS.TSO64 X86.VCGen.PlainMethods
open Grading.ConcurrentTask

-- Equality for finite observations stays local to this client.
private def exceptDecEq {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error first, .error second =>
      match decEq first second with
      | .isTrue same => .isTrue (congrArg Except.error same)
      | .isFalse different => .isFalse (fun same => different (Except.error.inj same))
  | .ok first, .ok second =>
      match decEq first second with
      | .isTrue same => .isTrue (congrArg Except.ok same)
      | .isFalse different => .isFalse (fun same => different (Except.ok.inj same))
  | .error _, .ok _ => .isFalse (fun same => by cases same)
  | .ok _, .error _ => .isFalse (fun same => by cases same)

-- Stage finite observation decisions at the unchanged depth limit.
private instance : DecidableEq (List Observation) := inferInstance
private instance : DecidableEq (Option Word) := inferInstance
private instance : DecidableEq (Option Nat) := inferInstance
private instance : DecidableEq (Option (List Nat)) := inferInstance
private instance : DecidableEq (Except Error Word) := exceptDecEq
private instance : DecidableEq (Except Fault Word) := exceptDecEq
private instance : DecidableEq (Except OS.Borrowing.ReadFault Word) := exceptDecEq

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

def oldWord : Word := 0x1122334455667788
def storeWord : Word := 0xfedcba9876543210
def incomingWord : Word := 0x99aabbccddeeff00

def setup : Except OS.Atomics64.Fault TSO64.Ready :=
  TSO64.fixture 0xc3078b48 0xc3378948 oldWord

theorem setup_succeeds : setup.toOption.isSome = true := by decide +kernel
def installed : TSO64.Ready := checked setup setup_succeeds

private def installCaller (before : TSO64.Checked) (owner actor : Nat)
    (address continuation : Word) : Except OS.Atomics64.Fault (TSO64.Checked × Nat) := do
  let (allocated, out) ← TSO64.change before (.allocate owner ⟨address, 8⟩ OS.AddressSpace.readWrite)
  let ticket ← TSO64.ticket out
  let (written, _) ← TSO64.change allocated (.store64 owner ticket address continuation)
  let (readOnlyState, _) ← TSO64.change written (.protect owner ticket OS.AddressSpace.readOnly)
  TSO64.borrow readOnlyState owner ticket actor ⟨address, 8⟩

def callerAAttempt : Except OS.Atomics64.Fault (TSO64.Checked × Nat) :=
  installCaller installed.checked 31 11 0x800008 0x7000

theorem callerA_succeeds : callerAAttempt.toOption.isSome = true := by decide +kernel
def callerA : TSO64.Checked × Nat := checked callerAAttempt callerA_succeeds

def callerBAttempt : Except OS.Atomics64.Fault (TSO64.Checked × Nat) :=
  installCaller callerA.1 32 12 0x810008 0x8000

theorem callerB_succeeds : callerBAttempt.toOption.isSome = true := by decide +kernel
def callerB : TSO64.Checked × Nat := checked callerBAttempt callerB_succeeds

def ready : TSO64.Ready :=
  { installed with checked := callerB.1, callerA := callerA.2, callerB := callerB.2 }

def world : World := ready.checked.world

theorem world_valid : OS.Atomics64.WellFormed world := ready.checked.valid

-- Keep concrete resource computations behind their proved interfaces during
-- elaboration. Kernel decision and replay still unfold the same definitions.
attribute [local irreducible] world

def readerContext : Context := TSO64.context 0x800008 131072 0x0123456789abcdef 5
def writerContext : Context :=
  { TSO64.context 0x810008 196608 storeWord 5 with rip := 393224 }

def makeReader : Except Fault Worker :=
  makeWorker world 11 readerContext ready.codeA ready.callerA [ready.dataA] [ready.atomicA]

def makeWriter : Except Fault Worker :=
  makeWorker world 12 writerContext ready.codeB ready.callerB [ready.dataB] [ready.atomicB]

theorem make_reader_succeeds : makeReader.toOption.isSome = true := by decide +kernel
theorem make_writer_succeeds : makeWriter.toOption.isSome = true := by decide +kernel

def attachedReader : Worker := checked makeReader make_reader_succeeds
def attachedWriter : Worker := checked makeWriter make_writer_succeeds

theorem reader_made : makeReader = .ok attachedReader := checked_ok _ _
theorem writer_made : makeWriter = .ok attachedWriter := checked_ok _ _

attribute [local irreducible] attachedReader attachedWriter

private theorem attach_append {workers : List Worker} {actor : Nat}
    {entry : Context} {code caller : Nat} {grants : List OS.Ownership.Ticket}
    {atomics : List OS.Atomics64.HandleId64} {worker : Worker}
    (made : makeWorker world actor entry code caller grants atomics = .ok worker) :
    attach ⟨world, workers⟩ actor entry code caller grants atomics =
      .ok ⟨world, workers ++ [worker]⟩ := by
  simp only [attach, made, ok_bind, pure_ok]

theorem reader_attached :
    attach ⟨world, []⟩ 11 readerContext ready.codeA ready.callerA
      [ready.dataA] [ready.atomicA] = .ok ⟨world, [attachedReader]⟩ :=
  attach_append reader_made

theorem writer_attached :
    attach ⟨world, [attachedReader]⟩ 12 writerContext ready.codeB ready.callerB
      [ready.dataB] [ready.atomicB] = .ok ⟨world, [attachedReader, attachedWriter]⟩ :=
  attach_append writer_made

-- Checked boundary enqueue, not an assumed StoreGate or hand-authorized FIFO.
def readerQueueAttempt : Except Fault Queue.Cursor :=
  Queue.Cursor.enqueue ⟨[], 7⟩ world attachedReader.resources
    ⟨131072, .qword 0x8877665544332211⟩ .sharedCell

def writerQueueAttempt : Except Fault Queue.Cursor :=
  Queue.Cursor.enqueue ⟨[], 11⟩ world attachedWriter.resources
    ⟨65536, .qword incomingWord⟩ .sharedCell

theorem reader_queue_succeeds : readerQueueAttempt.toOption.isSome = true := by decide +kernel
theorem writer_queue_succeeds : writerQueueAttempt.toOption.isSome = true := by decide +kernel

def readerQueue : Queue.Cursor := checked readerQueueAttempt reader_queue_succeeds
def writerQueue : Queue.Cursor := checked writerQueueAttempt writer_queue_succeeds

theorem reader_queue_actual : readerQueueAttempt = .ok readerQueue := checked_ok _ _
theorem writer_queue_actual : writerQueueAttempt = .ok writerQueue := checked_ok _ _

def reader : Worker :=
  { attachedReader with pending := readerQueue.pending, nextStore := readerQueue.nextStore }
def writer : Worker :=
  { attachedWriter with pending := writerQueue.pending, nextStore := writerQueue.nextStore }

def initial : OS.TSO64.State := ⟨world, [reader, writer]⟩

private theorem empty_valid : WellFormed ⟨world, []⟩ .sharedCell := by
  change OS.Atomics64.WellFormed world ∧
    ∀ worker ∈ ([] : List Worker), WorkerValid world worker .sharedCell
  constructor
  · exact world_valid
  intro worker absent
  cases absent

private theorem replace_queue_valid {current : World} {worker : Worker} {cursor : Queue.Cursor}
    (valid : WorkerValid current worker .sharedCell)
    (pending : ∀ entry ∈ cursor.pending, PendingValid current worker.resources entry .sharedCell) :
    WorkerValid current
      { worker with pending := cursor.pending, nextStore := cursor.nextStore } .sharedCell :=
  ⟨valid.1, pending⟩

theorem attached_valid : WellFormed ⟨world, [attachedReader, attachedWriter]⟩ .sharedCell :=
  attach_valid_for .sharedCell
    (attach_valid_for .sharedCell empty_valid reader_attached) writer_attached

theorem initial_valid : WellFormed initial .sharedCell := by
  have first : WorkerValid world reader .sharedCell := by
    apply replace_queue_valid (worker := attachedReader) (cursor := readerQueue)
      (attached_valid.2 attachedReader (by simp))
    exact Queue.Cursor.enqueue_valid ⟨[], 7⟩ world attachedReader.resources
      ⟨131072, .qword 0x8877665544332211⟩ .sharedCell readerQueue
      (by simp) reader_queue_actual
  have second : WorkerValid world writer .sharedCell := by
    apply replace_queue_valid (worker := attachedWriter) (cursor := writerQueue)
      (attached_valid.2 attachedWriter (by simp))
    exact Queue.Cursor.enqueue_valid ⟨[], 11⟩ world attachedWriter.resources
      ⟨65536, .qword incomingWord⟩ .sharedCell writerQueue
      (by simp) writer_queue_actual
  change OS.Atomics64.WellFormed world ∧
    ∀ worker ∈ [reader, writer], WorkerValid world worker .sharedCell
  constructor
  · exact world_valid
  intro worker member
  have alternatives : worker = reader ∨ worker = writer := by
    simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
      using member
  rcases alternatives with rfl | rfl
  · exact first
  · exact second

theorem reader_live : initial.workers[0]? = some reader := rfl
theorem writer_live : initial.workers[1]? = some writer := rfl
theorem initial_length : initial.workers.length = 2 := rfl

def readerSlot : Fin initial.workers.length :=
  ⟨0, by rw [initial_length]; decide⟩
def writerSlot : Fin initial.workers.length :=
  ⟨1, by rw [initial_length]; decide⟩

private theorem reader_context : reader.context = readerContext := by
  change attachedReader.context = readerContext
  exact (makeWorker_valid_for (world := world) (worker := attachedReader)
    (entry := readerContext) .sharedCell reader_made).2.2.2
private theorem writer_context : writer.context = writerContext := by
  change attachedWriter.context = writerContext
  exact (makeWorker_valid_for (world := world) (worker := attachedWriter)
    (entry := writerContext) .sharedCell writer_made).2.2.2

private theorem reader_phase : reader.phase = .running := by
  change attachedReader.phase = .running
  exact (makeWorker_valid_for (world := world) (worker := attachedReader)
    (entry := readerContext) .sharedCell reader_made).2.1

private theorem writer_phase : writer.phase = .running := by
  change attachedWriter.phase = .running
  exact (makeWorker_valid_for (world := world) (worker := attachedWriter)
    (entry := writerContext) .sharedCell writer_made).2.1

def authorityAttempt : Except OS.Atomics64.Fault (OS.Atomics64.Handle × OS.Atomics64.Cell) :=
  OS.Atomics64.authorize world 11 ready.atomicA
theorem authority_succeeds : authorityAttempt.toOption.isSome = true := by decide +kernel
def authority : OS.Atomics64.Handle × OS.Atomics64.Cell := checked authorityAttempt authority_succeeds
theorem authority_actual : authorityAttempt = .ok authority := checked_ok _ _

attribute [local irreducible] authority

def target : OS.Atomics64.CellId64 := authority.1.cell
def cell : OS.Atomics64.Cell := authority.2

def loadImage : Plain64.Image := ⟨393216, [0x48, 0x8b, 0x07, 0xc3]⟩
def storeImage : Plain64.Image := ⟨393224, [0x48, 0x89, 0x37, 0xc3]⟩
def readerInput : Plain64.Input := .loadAcquire loadImage target cell 41
def writerInput : Plain64.Input := .storeRelease storeImage target cell storeWord 93
def catalog : Plain64.Catalog := [readerInput.site, writerInput.site]

def inputs (tid : Fin initial.workers.length) : Plain64.Input :=
  if tid.val = 0 then readerInput else writerInput

-- Argument transport checks independent full-register bindings. In particular
-- the load's unused RSI is arbitrary, whereas a store binds all 64 RSI bits.
private theorem load_arguments {image : Plain64.Image} {object : OS.Atomics64.CellId64}
    {descriptor : OS.Atomics64.Cell} {occurrence : Nat} {worker : Worker}
    (rdi : worker.context.registers .rdi = descriptor.address) :
    Plain64.Arguments (.loadAcquire image object descriptor occurrence) worker := by
  intro index argument bound
  by_cases first : index.val = 0
  · have same : index = 0 := Fin.ext first
    subst index
    have chosen : PureCall.Argument.word64 descriptor.address = argument := Option.some.inj bound
    subst argument
    exact rdi
  · simp [Plain64.Input.argument, first] at bound

private theorem store_arguments {image : Plain64.Image} {object : OS.Atomics64.CellId64}
    {descriptor : OS.Atomics64.Cell} {value : Word} {occurrence : Nat} {worker : Worker}
    (rdi : worker.context.registers .rdi = descriptor.address)
    (rsi : worker.context.registers .rsi = value) :
    Plain64.Arguments (.storeRelease image object descriptor value occurrence) worker := by
  intro index argument bound
  by_cases first : index.val = 0
  · have same : index = 0 := Fin.ext first
    subst index
    have chosen : PureCall.Argument.word64 descriptor.address = argument := Option.some.inj bound
    subst argument
    exact rdi
  · by_cases second : index.val = 1
    · have same : index = 1 := Fin.ext second
      subst index
      have chosen : PureCall.Argument.word64 value = argument := Option.some.inj bound
      subst argument
      exact rsi
    · simp [Plain64.Input.argument, first, second] at bound

theorem reader_scalar : OS.ScalarCall64.Entry reader := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [reader_context] <;> decide +kernel

theorem writer_scalar : OS.ScalarCall64.Entry writer := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [writer_context] <;> decide +kernel

private theorem live_target : world.cells target = some cell := by
  change world.cells authority.1.cell = some authority.2
  exact (OS.Atomics64.authorize_ok world 11 ready.atomicA authority authority_actual).2.2.1

private theorem valid_cell : OS.Atomics64.ValidCell world.legacy.shared cell :=
  (OS.Atomics64.authorize_ok world 11 ready.atomicA authority authority_actual).2.2.2

theorem reader_entry : Plain64.Entry readerInput initial reader := by
  refine ⟨reader_phase, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, reader_scalar, live_target, valid_cell, ?_, ?_⟩
  · rw [reader_context]
    rfl
  · apply load_arguments
    rw [reader_context]
    decide +kernel
  · decide +kernel
  · decide +kernel
  · apply checkCode_sound
    decide +kernel
  · decide +kernel
  · decide +kernel
  · refine ⟨ready.atomicA, authority.1, ?_, rfl⟩
    decide +kernel
  · refine ⟨0x7000, ?_, by decide +kernel⟩
    decide +kernel

theorem writer_entry : Plain64.Entry writerInput initial writer := by
  refine ⟨writer_phase, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, writer_scalar, live_target, valid_cell, ?_, ?_⟩
  · rw [writer_context]
    rfl
  · apply store_arguments
    · rw [writer_context]
      decide +kernel
    · rw [writer_context]
      rfl
  · decide +kernel
  · decide +kernel
  · apply checkCode_sound
    decide +kernel
  · decide +kernel
  · decide +kernel
  · refine ⟨ready.atomicB, ⟨12, target⟩, ?_, rfl⟩
    decide +kernel
  · refine ⟨0x8000, ?_, by decide +kernel⟩
    decide +kernel

private theorem slot_cases (tid : Fin initial.workers.length) : tid.val = 0 ∨ tid.val = 1 := by
  have bound : tid.val < 2 := tid.isLt
  omega

private theorem slot_live (tid : Fin initial.workers.length) :
    initial.workers[tid.val]? = some (if tid.val = 0 then reader else writer) := by
  rcases slot_cases tid with zero | one
  · simp only [zero]
    exact reader_live
  · simp only [one, show (1 : Nat) ≠ 0 by decide, ite_false]
    exact writer_live

private theorem reader_caller_region :
    reader.resources.caller.loan.region = ⟨0x800008, 8⟩ := by
  have resources := (initial_valid.2 reader (List.mem_of_getElem? reader_live)).1
  rw [resources.2.2.1, ← reader_entry.originalRsp, reader_context]
  rfl

private theorem writer_caller_region :
    writer.resources.caller.loan.region = ⟨0x810008, 8⟩ := by
  have resources := (initial_valid.2 writer (List.mem_of_getElem? writer_live)).1
  rw [resources.2.2.1, ← writer_entry.originalRsp, writer_context]
  rfl

private theorem callers_disjoint :
    OS.Ownership.Disjoint reader.resources.caller.loan.region writer.resources.caller.loan.region := by
  rw [reader_caller_region, writer_caller_region]
  decide +kernel

private theorem callers_disjoint_reverse :
    OS.Ownership.Disjoint writer.resources.caller.loan.region reader.resources.caller.loan.region := by
  rw [reader_caller_region, writer_caller_region]
  decide +kernel

theorem independentPre : Plain64.Pre catalog initial inputs := by
  refine ⟨initial_valid, ?_, ?_, ?_, ?_⟩
  · intro tid
    by_cases zero : tid.val = 0 <;> simp [inputs, zero, catalog]
  · intro tid
    rcases slot_cases tid with zero | one
    · refine ⟨reader, ?_, ?_⟩
      · simpa only [zero] using reader_live
      · simpa [inputs, zero] using reader_entry
    · refine ⟨writer, ?_, ?_⟩
      · simpa only [one] using writer_live
      · simpa [inputs, one] using writer_entry
  · intro i j first second different firstLive secondLive
    have firstEq : first = (if i.val = 0 then reader else writer) :=
      Option.some.inj (firstLive.symm.trans (slot_live i))
    have secondEq : second = (if j.val = 0 then reader else writer) :=
      Option.some.inj (secondLive.symm.trans (slot_live j))
    subst first
    subst second
    rcases slot_cases i with iz | io <;> rcases slot_cases j with jz | jo
    · exact False.elim (different (Fin.ext (iz.trans jz.symm)))
    · simpa [iz, jo] using callers_disjoint
    · simpa [io, jz] using callers_disjoint_reverse
    · exact False.elim (different (Fin.ext (io.trans jo.symm)))
  · intro i j caller callerLive
    have callerEq : caller = (if j.val = 0 then reader else writer) :=
      Option.some.inj (callerLive.symm.trans (slot_live j))
    subst caller
    rcases slot_cases i with iz | io <;> rcases slot_cases j with jz | jo
    all_goals simp_all [inputs, reader_caller_region, writer_caller_region] <;> decide +kernel

-- Static checked code is a proof-side argument and never a Pre field.
def separateStaticShapes : OS.PlainCallAdmission64.StaticShapes catalog where
  padding _ := []
  checked := by
    intro site member
    have alternatives : site = readerInput.site ∨ site = writerInput.site := by
      simpa only [catalog, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        using member
    rcases alternatives with rfl | rfl <;> decide +kernel

noncomputable def admitted (tid : Fin initial.workers.length) :
    OS.PlainCallAdmission64.Admitted (inputs tid) initial tid.val :=
  OS.PlainCallAdmission64.admission separateStaticShapes independentPre tid

noncomputable def invocations (tid : Fin initial.workers.length) : Invocation initial tid.val :=
  (admitted tid).invocation

/-- Every actual slot retains its independent request, full descriptor,
logical occurrence, actual incoming FIFO, counter and scalar ABI entry. -/
theorem bridge_retains_input (tid : Fin initial.workers.length) :
    (invocations tid).method.request = (inputs tid).request ∧
    (invocations tid).method.reference.handle.cell = (inputs tid).target ∧
    (invocations tid).method.reference.cell = (inputs tid).cell ∧
    (invocations tid).occurrence = (inputs tid).occurrence ∧
    (invocations tid).method.initialQueue =
      ⟨(invocations tid).initial.pending, (invocations tid).initial.nextStore⟩ ∧
    OS.ScalarCall64.Entry (invocations tid).initial :=
  ⟨(admitted tid).request, (admitted tid).target, (admitted tid).descriptor,
    (admitted tid).occurrence, (admitted tid).initialQueue, (admitted tid).scalar⟩

/-- The bridge preserves actual incoming entries with both authority kinds,
nonzero counters, and logical labels unrelated to machine issue allocation. -/
theorem bridge_incoming :
    (invocations readerSlot).method.initialQueue =
      ⟨[.ordinary ready.dataA ⟨131072, .qword 0x8877665544332211⟩], 8⟩ ∧
    (invocations writerSlot).method.initialQueue =
      ⟨[.managed ⟨ready.atomicB, ⟨12, target⟩, cell⟩ incomingWord 11], 12⟩ ∧
    (invocations readerSlot).method.request = .loadAcquire target ∧
    (invocations writerSlot).method.request = .storeRelease target storeWord ∧
    (invocations readerSlot).occurrence = 41 ∧
    (invocations writerSlot).occurrence = 93 := by
  have first : (invocations readerSlot).initial = reader :=
    (admitted readerSlot).initial_eq reader_live
  have second : (invocations writerSlot).initial = writer :=
    (admitted writerSlot).initial_eq writer_live
  refine ⟨?_, ?_, (admitted readerSlot).request,
    (admitted writerSlot).request, (admitted readerSlot).occurrence,
    (admitted writerSlot).occurrence⟩
  · change (admitted readerSlot).invocation.method.initialQueue = _
    rw [(admitted readerSlot).initialQueue]
    change (⟨(invocations readerSlot).initial.pending,
      (invocations readerSlot).initial.nextStore⟩ : Queue.Cursor) = _
    rw [first]
    decide +kernel
  · change (admitted writerSlot).invocation.method.initialQueue = _
    rw [(admitted writerSlot).initialQueue]
    change (⟨(invocations writerSlot).initial.pending,
      (invocations writerSlot).initial.nextStore⟩ : Queue.Cursor) = _
    rw [second]
    decide +kernel

/-- The entire nonempty mixed cohort completes from independent present facts.
No future cutpoint is constructed by the client. RET frames precede the
separate actual drain closure, which preserves all machine response values. -/
theorem independent_completion (choices : Nat → Nat → Bool) :
    ∃ actions result closed,
      schedule initial actions .sharedCell = .ok result ∧ Returned result.1 ∧
      DrainClosure.drainAll result.1 .sharedCell = .ok closed ∧
      DrainClosure.Certificate result.1 closed .sharedCell ∧ Finished closed.1 ∧
      (∀ tid, OS.TSO64.Return.returnValue (closed.1, .returned tid) =
        OS.TSO64.Return.returnValue (result.1, .returned tid)) ∧
      (∀ tid : Fin initial.workers.length, ∃ final reply,
        result.1.workers[tid.val]? = some final ∧
        BodyPost (invocations tid).method final reply ∧
        OneAccess (invocations tid).method tid.val initial actions result reply ∧
        OS.ScalarCall64.ReturnFrame initial result.1 tid.val (invocations tid).initial final) := by
  obtain ⟨cuts, result, completion, _, _⟩ :=
    cohort_complete_after_prefix invocations (prior := []) (actual := (initial, [])) rfl choices
  obtain ⟨closed, drained, certificate, _, finished, responses⟩ :=
    completion.close independentPre.valid
  refine ⟨_, result, closed, completion.scheduled, completion.returned,
    drained, certificate, finished, responses, ?_⟩
  intro tid
  obtain ⟨_, final, reply, _, live, _, post, _⟩ := completion.completed tid
  obtain ⟨_, actualReply, actualPost, oneAccess, _⟩ :=
    all_completed (invocations tid).current (invocations tid).live (invocations tid).entry
      completion.scheduled live post.phase
  refine ⟨final, actualReply, live, actualPost, oneAccess, ?_⟩
  exact actualPost.return_frame (invocations tid).current (invocations tid).live
    (invocations tid).entry (admitted tid).scalar
    (schedule_wellFormed independentPre.valid completion.scheduled) live

-- Actual execution observations complement constructive completion. These
-- computations call the production scheduler, never an opcode interpreter in
-- the test, and never provide a desired reply or future At to admission.
def loadAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step initial (.issue 0 false) .sharedCell
theorem load_succeeds : loadAttempt.toOption.isSome = true := by decide +kernel
def loaded : OS.TSO64.State × Observation := checked loadAttempt load_succeeds
theorem load_actual : step initial (.issue 0 false) .sharedCell = .ok loaded := checked_ok _ _

def loadReturnAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step loaded.1 (.issue 0 true) .sharedCell
theorem load_return_succeeds : loadReturnAttempt.toOption.isSome = true := by decide +kernel
def loadReturned : OS.TSO64.State × Observation := checked loadReturnAttempt load_return_succeeds
theorem load_return_actual : step loaded.1 (.issue 0 true) .sharedCell = .ok loadReturned :=
  checked_ok _ _

def storeAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step loadReturned.1 (.issue 1 true) .sharedCell
theorem store_succeeds : storeAttempt.toOption.isSome = true := by decide +kernel
def stored : OS.TSO64.State × Observation := checked storeAttempt store_succeeds
theorem store_actual : step loadReturned.1 (.issue 1 true) .sharedCell = .ok stored := checked_ok _ _

def storeReturnAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step stored.1 (.issue 1 false) .sharedCell
theorem store_return_succeeds : storeReturnAttempt.toOption.isSome = true := by decide +kernel
def storeReturned : OS.TSO64.State × Observation := checked storeReturnAttempt store_return_succeeds
theorem store_return_actual : step stored.1 (.issue 1 false) .sharedCell = .ok storeReturned :=
  checked_ok _ _

def actions : List Action := [.issue 0 false, .issue 0 true, .issue 1 true, .issue 1 false]
def result : OS.TSO64.State × List Observation :=
  (storeReturned.1, [loaded.2, loadReturned.2, stored.2, storeReturned.2])

theorem scheduled : schedule initial actions .sharedCell = .ok result := by
  simp only [actions, result, schedule, load_actual, load_return_actual,
    store_actual, store_return_actual, ok_bind, pure_ok]

attribute [local irreducible] result

/-- Full64 data and actual deferred FIFO effects, including the managed
incoming occurrence 11 followed by the method's newly allocated occurrence 12.
Both RETs occur while their own queues still prevent collection. -/
theorem actual_read_and_deferred_store :
    result.2 = [.ordinary 0, .returned 0, .ordinary 1, .returned 1] ∧
    result.1.workers[0]?.map (fun worker => worker.context.registers .rax) = some oldWord ∧
    result.1.workers[0]?.map (fun worker => worker.context.registers .rsp) = some 0x800010 ∧
    result.1.workers[1]?.map (fun worker => worker.context.registers .rsp) = some 0x810010 ∧
    loadQWord (published result.1.world) 65536 = .ok oldWord ∧
    result.1.workers[0]?.map (fun worker => worker.pending.length) = some 1 ∧
    result.1.workers[1]?.map (fun worker => worker.pending.length) = some 2 ∧
    result.1.workers[0]?.map Worker.nextStore = some 8 ∧
    result.1.workers[1]?.map Worker.nextStore = some 13 ∧
    result.1.workers[1]?.map (fun worker => Queue.occurrences worker.pending) = some [11, 12] ∧
    collect result.1 0 = .error .resource ∧ collect result.1 1 = .error .resource := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem result_returned : Returned result.1 := by
  have phases : result.1.workers.map Worker.phase = [.returned, .returned] := by decide +kernel
  intro worker member
  have mapped : worker.phase ∈ result.1.workers.map Worker.phase :=
    List.mem_map.mpr ⟨worker, member, rfl⟩
  rw [phases] at mapped
  simpa using mapped

/-- Body and ABI conclusions for the very same concrete run and both actual
workers, obtained through the independent bridge rather than assumed At's. -/
theorem actual_frames (tid : Fin initial.workers.length) :
    ∃ final reply, result.1.workers[tid.val]? = some final ∧
      BodyPost (invocations tid).method final reply ∧
      OneAccess (invocations tid).method tid.val initial actions result reply ∧
      OS.ScalarCall64.ReturnFrame initial result.1 tid.val (invocations tid).initial final := by
  have bound : tid.val < result.1.workers.length := by
    rw [ScheduleTrace.workers_length scheduled]
    exact tid.isLt
  let final : Worker := result.1.workers[tid.val]
  have live : result.1.workers[tid.val]? = some final := List.getElem?_eq_getElem bound
  have phase := result_returned final (List.mem_of_getElem? live)
  obtain ⟨_, reply, post, oneAccess, _⟩ :=
    all_completed (invocations tid).current (invocations tid).live (invocations tid).entry
      scheduled live phase
  refine ⟨final, reply, live, post, oneAccess, ?_⟩
  exact post.return_frame (invocations tid).current (invocations tid).live
    (invocations tid).entry (admitted tid).scalar
    (schedule_wellFormed independentPre.valid scheduled) live

def closeAttempt : Except Fault (OS.TSO64.State × List Observation) :=
  DrainClosure.drainAll result.1 .sharedCell
theorem close_succeeds : closeAttempt.toOption.isSome = true := by decide +kernel
def closed : OS.TSO64.State × List Observation := checked closeAttempt close_succeeds
theorem close_actual : DrainClosure.drainAll result.1 .sharedCell = .ok closed := checked_ok _ _

attribute [local irreducible] closed

theorem close_certificate : DrainClosure.Certificate result.1 closed .sharedCell := by
  obtain ⟨output, actual, certificate⟩ :=
    DrainClosure.drainAll_complete (schedule_wellFormed independentPre.valid scheduled)
  have same : output = closed := Except.ok.inj (actual.symm.trans close_actual)
  subst output
  exact certificate

/-- The independent full-cell, resource, target-authority and scalar ABI frame
holds after all three real incoming/new FIFO entries have published. -/
theorem closed_frame : Plain64.ReturnFrame initial closed.1 inputs := by
  have executed : schedule initial (actions ++ DrainClosure.actions result.1) .sharedCell =
      .ok (closed.1, result.2 ++ closed.2) :=
    completion_schedule_append scheduled close_certificate.scheduled
  have returned : Returned closed.1 :=
    completion_drain_returned (state := result.1) (result := closed)
      (profile := .sharedCell) close_certificate result_returned
  exact OS.PlainCallFrames64.returned_cohort (before := initial) (inputs := inputs)
    separateStaticShapes independentPre (result := (closed.1, result.2 ++ closed.2))
    executed returned

/-- The ordinary incoming store and both exact managed FIFO entries really
publish. The latest store wins in shared RAM, while the earlier load's saved
full64 return value, original continuations and ABI stack pops are retained. -/
theorem actual_publication :
    loadQWord (published closed.1.world) 65536 = .ok storeWord ∧
    loadQWord (published closed.1.world) 131072 = .ok 0x8877665544332211 ∧
    collect closed.1 0 = .ok oldWord ∧ collect closed.1 1 = .ok 5 ∧
    closed.1.workers[0]?.map (fun worker => worker.context.rip) = some 0x7000 ∧
    closed.1.workers[1]?.map (fun worker => worker.context.rip) = some 0x8000 ∧
    closed.1.workers[0]?.map (fun worker => worker.context.registers .rsp) = some 0x800010 ∧
    closed.1.workers[1]?.map (fun worker => worker.context.registers .rsp) = some 0x810010 ∧
    closed.2.length = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end EDSL.Tests.PlainCallAdmission64

#print axioms EDSL.Tests.PlainCallAdmission64.independentPre
#print axioms EDSL.Tests.PlainCallAdmission64.bridge_retains_input
#print axioms EDSL.Tests.PlainCallAdmission64.bridge_incoming
#print axioms EDSL.Tests.PlainCallAdmission64.independent_completion
#print axioms EDSL.Tests.PlainCallAdmission64.actual_frames
#print axioms EDSL.Tests.PlainCallAdmission64.close_certificate
#print axioms EDSL.Tests.PlainCallAdmission64.closed_frame
#print axioms EDSL.Tests.PlainCallAdmission64.actual_read_and_deferred_store
#print axioms EDSL.Tests.PlainCallAdmission64.actual_publication
#audit_edsl
