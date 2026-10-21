/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.PlainCallOrigins
import EDSL.X86.VCGen.PlainMethods.Batch

namespace EDSL.Tests.PlainCallInterference
open X86 OS.TSO64 X86.VCGen.PlainMethods

/-!
Resource-admitted load witnesses with an actually issued ordinary own FIFO and
an actually issued managed peer FIFO. The checked fixture installs the bytes
MOV [RDX],RSI; MOV RAX,[RDI]; RET; MOV [RDI],RSI; RET. The method starts at
393219, after the ordinary prelude, rather than at the allocation's base.

The interfering schedule loads, publishes the peer's different word, returns,
then publishes the own ordinary head. Access and response are at action indices
0 and 2; a drain is a real action in that interval. Expected words and registers
are literal observations of production execution, not proposed execution inputs.
This file exercises the shared method and indexed machine-call adapters.
The existing sharedCell scalar-RAM, long-mode, CET-off and resource assumptions
apply; these synthetic witnesses make no physical-x86 or source-C23 claim.
-/

-- Stage finite observation equality at the parent's unchanged depth limit.
private instance : DecidableEq PlainMethods.PendingView := inferInstance
private instance : DecidableEq (List PlainMethods.PendingView) := inferInstance
private instance : DecidableEq (List PlainMethods.PendingView × Nat) := inferInstance
private instance : DecidableEq (Option (List PlainMethods.PendingView × Nat)) := inferInstance
private instance : DecidableEq (List PlainMethods.WorkerView) := inferInstance
private instance : DecidableEq (List PlainMethods.DrainView) := inferInstance
private instance : DecidableEq (List (Except Error Word)) := inferInstance
private instance : DecidableEq (List (List (Except Error Word))) := inferInstance
private instance : DecidableEq (List (Option (Nat × Word))) := inferInstance

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

private def found {α : Type} (value : Option α) (present : value.isSome = true) : α :=
  value.get present

private theorem found_ok {α : Type} (value : Option α) (present : value.isSome = true) :
    value = some (found value present) := by
  cases value with
  | none => cases present
  | some value => rfl

def setup : Except OS.Atomics64.Fault TSO64.Ready :=
  TSO64.fixture 0x48c3078b48328948 0x0000000000c33789 0x1122334455667788

theorem setup_succeeds : setup.toOption.isSome = true := by decide +kernel

def ready : TSO64.Ready := checked setup setup_succeeds

theorem setup_world_valid : OS.Atomics64.WellFormed ready.checked.world := ready.checked.valid

def readerContext : Context := TSO64.context 262144 131072 9 5

def peerContext : Context :=
  { TSO64.context 327680 196608 0xfedcba9876543210 5 with rip := 393223 }

def makeReader : Except Fault Worker :=
  makeWorker ready.checked.world 11 readerContext ready.codeA ready.callerA
    [ready.dataA] [ready.atomicA]

def makePeer : Except Fault Worker :=
  makeWorker ready.checked.world 12 peerContext ready.codeB ready.callerB
    [ready.dataB] [ready.atomicB]

theorem make_reader_succeeds : makeReader.toOption.isSome = true := by decide +kernel
theorem make_peer_succeeds : makePeer.toOption.isSome = true := by decide +kernel

def reader : Worker := checked makeReader make_reader_succeeds
def peer : Worker := checked makePeer make_peer_succeeds

theorem reader_made : makeReader = .ok reader := checked_ok makeReader make_reader_succeeds
theorem peer_made : makePeer = .ok peer := checked_ok makePeer make_peer_succeeds

def one : OS.TSO64.State := ⟨ready.checked.world, [reader]⟩
def initial : OS.TSO64.State := ⟨ready.checked.world, [reader, peer]⟩

private theorem attach_append {world : World} {workers : List Worker} {actor : Nat}
    {entry : Context} {code caller : Nat} {grants : List OS.Ownership.Ticket}
    {atomics : List OS.Atomics64.HandleId64} {worker : Worker}
    (made : makeWorker world actor entry code caller grants atomics = .ok worker) :
    attach ⟨world, workers⟩ actor entry code caller grants atomics =
      .ok ⟨world, workers ++ [worker]⟩ := by
  simp only [attach, made, ok_bind, pure_ok]

private theorem empty_valid (world : World) (valid : OS.Atomics64.WellFormed world) :
    WellFormed ⟨world, []⟩ .sharedCell := by
  refine ⟨valid, ?_⟩
  intro worker absent
  cases absent

theorem reader_attached :
    attach ⟨ready.checked.world, []⟩ 11 readerContext ready.codeA ready.callerA
      [ready.dataA] [ready.atomicA] = .ok one :=
  attach_append reader_made

theorem peer_attached :
    attach one 12 peerContext ready.codeB ready.callerB [ready.dataB] [ready.atomicB] =
      .ok initial :=
  attach_append peer_made

theorem initial_valid : WellFormed initial .sharedCell :=
  attach_valid_for .sharedCell
    (attach_valid_for .sharedCell (empty_valid _ setup_world_valid) reader_attached) peer_attached

theorem initial_live : initial.workers[0]? = some reader := rfl

def ownPrefix : Except Fault (OS.TSO64.State × Observation) :=
  step initial (.issue 0 false) .sharedCell

theorem own_prefix_succeeds : ownPrefix.toOption.isSome = true := by decide +kernel
def ownQueued : OS.TSO64.State × Observation := checked ownPrefix own_prefix_succeeds

theorem own_issued : step initial (.issue 0 false) .sharedCell = .ok ownQueued :=
  checked_ok ownPrefix own_prefix_succeeds

def peerPrefix : Except Fault (OS.TSO64.State × Observation) :=
  step ownQueued.1 (.issue 1 true) .sharedCell

theorem peer_prefix_succeeds : peerPrefix.toOption.isSome = true := by decide +kernel
def peerQueued : OS.TSO64.State × Observation := checked peerPrefix peer_prefix_succeeds

theorem peer_issued : step ownQueued.1 (.issue 1 true) .sharedCell = .ok peerQueued :=
  checked_ok peerPrefix peer_prefix_succeeds

def boundary : OS.TSO64.State := peerQueued.1

theorem prefix_scheduled :
    schedule initial [.issue 0 false, .issue 1 true] .sharedCell =
      .ok (boundary, [ownQueued.2, peerQueued.2]) := by
  simp only [schedule, own_issued, peer_issued, ok_bind, pure_ok, boundary]

theorem boundary_valid : WellFormed boundary .sharedCell :=
  step_wellFormed (state := ownQueued.1) (result := peerQueued)
    (step_wellFormed (state := initial) (result := ownQueued) initial_valid own_issued) peer_issued

theorem queued_reader_present : (ownQueued.1.workers[0]?).isSome = true := by decide +kernel

/-- Extract the actual successor, before the peer's issue. The peer frame below
identifies this same worker in the boundary state; no desired worker is supplied. -/
def boundaryReader : Worker := found (ownQueued.1.workers[0]?) queued_reader_present

theorem queued_reader_live : ownQueued.1.workers[0]? = some boundaryReader :=
  found_ok _ queued_reader_present

private theorem peer_live_after {state : OS.TSO64.State} {result : OS.TSO64.State × Observation}
    {tid issuing : Nat} {af : Bool} {worker : Worker}
    (success : step state (.issue issuing af) .sharedCell = .ok result)
    (different : tid ≠ issuing) (live : state.workers[tid]? = some worker) :
    result.1.workers[tid]? = some worker := (step_peer success different).trans live

theorem live : boundary.workers[0]? = some boundaryReader := by
  dsimp only [boundary]
  exact peer_live_after (state := ownQueued.1) (result := peerQueued)
    (tid := 0) (issuing := 1) (af := true) (worker := boundaryReader)
    peer_issued (by decide) queued_reader_live

theorem boundary_resources : boundaryReader.resources = reader.resources :=
  step_resources own_issued initial_live queued_reader_live

theorem boundary_registers : boundaryReader.context.registers = readerContext.registers := by
  funext register
  cases register <;> decide +kernel

theorem boundary_counter : boundaryReader.nextStore = 1 := by decide +kernel

/-- Both entries and the consumed counters are consequences of the two real
prefix issues. In particular the reader is not admitted with an empty FIFO. -/
theorem prefix_created_entries :
    ownQueued.2 = .ordinary 0 ∧ peerQueued.2 = .ordinary 1 ∧
    boundaryReader.pending.map PlainMethods.pendingView = [(0, 131072, .qword 9, none)] ∧
    boundaryReader.nextStore = 1 ∧
    boundary.workers[1]?.map (fun worker =>
      (worker.pending.map PlainMethods.pendingView, worker.nextStore)) =
      some ([(1, 65536, .qword 0xfedcba9876543210, some 0)], 1) := by
  refine ⟨?_, ?_, ?_, boundary_counter, ?_⟩ <;> decide +kernel

/-- The ordinary head supplies its own address, not the managed cell. The
managed read is the old published word, distinct from both queued payloads. -/
theorem boundary_reads :
    loadQWord (localCPU boundary boundaryReader).memory 65536 = .ok 0x1122334455667788 ∧
    StoreBuffer.Mixed.newestQWord (payload boundaryReader.pending) 65536 = none ∧
    loadQWord (published boundary.world) 65536 = .ok 0x1122334455667788 ∧
    loadQWord (localCPU boundary boundaryReader).memory 131072 = .ok 9 ∧
    loadQWord (published boundary.world) 131072 = .ok 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def method : Method where
  bytes := PlainMethods.window .clang .load
  operation := PlainMethods.operation .load
  base := 393219
  entry := readerContext.registers
  entryFlags := readerContext.flags
  resources := reader.resources
  reference := PlainMethodAdmission.reference
  returnAddress := 0x7000
  initialQueue := ⟨boundaryReader.pending, boundaryReader.nextStore⟩
  size := by decide +kernel
  codeNoWrap := by decide +kernel
  originalRsp := by decide +kernel
  returnCanonical := by decide +kernel
  stackNoWrap := by decide +kernel

private theorem initial_current : Current method initial := by
  refine ⟨initial_valid, ?_, ?_, ?_, ?_⟩
  · apply checkCode_sound
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- Checked code/current authority survive the actual prefix. Admission assumes
neither a next-step result nor a returned worker or a future cutpoint. -/
theorem present : Current method boundary :=
  (initial_current.step own_issued).step peer_issued

theorem entry : At method (.preamble 0 []) boundaryReader := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [method]
    exact boundary_resources
  · decide +kernel
  · dsimp only [Method.queueAt, method]
    exact QueueFrame.refl _
  · refine ⟨?_, ?_, boundary_registers, ?_⟩
    · decide +kernel
    · decide +kernel
    · exact (check_sound (bytes := method.bytes) (operation := method.operation)
        (padding := []) (by decide +kernel)).2

theorem admitted_access_enabled (af : Bool) :
    ∃ result, step boundary (.issue 0 af) .sharedCell = .ok result ∧ result.2.retired = 1 :=
  enabled present live entry (by simp only [Point.remaining, List.length_nil]; omega) af

-- Each checked extraction below is from a production step, never a supplied
-- poststate. Separate stages keep elaborator unification away from the fixture.
def loadAttempt (af : Bool) : Except Fault (OS.TSO64.State × Observation) :=
  step boundary (.issue 0 af) .sharedCell

theorem load_succeeds (af : Bool) : (loadAttempt af).toOption.isSome = true := by
  cases af <;> decide +kernel

def loaded (af : Bool) : OS.TSO64.State × Observation := checked (loadAttempt af) (load_succeeds af)

theorem loaded_actual (af : Bool) : step boundary (.issue 0 af) .sharedCell = .ok (loaded af) :=
  checked_ok (loadAttempt af) (load_succeeds af)

def peerPublicationAttempt (af : Bool) : Except Fault (OS.TSO64.State × Observation) :=
  step (loaded af).1 (.drain 1) .sharedCell

theorem peer_publication_succeeds (af : Bool) :
    (peerPublicationAttempt af).toOption.isSome = true := by
  cases af <;> decide +kernel

def peerPublished (af : Bool) : OS.TSO64.State × Observation :=
  checked (peerPublicationAttempt af) (peer_publication_succeeds af)

theorem peer_published_actual (af : Bool) :
    step (loaded af).1 (.drain 1) .sharedCell = .ok (peerPublished af) :=
  checked_ok (peerPublicationAttempt af) (peer_publication_succeeds af)

def returnAttempt (af retAF : Bool) : Except Fault (OS.TSO64.State × Observation) :=
  step (peerPublished af).1 (.issue 0 retAF) .sharedCell

theorem return_succeeds (af retAF : Bool) : (returnAttempt af retAF).toOption.isSome = true := by
  cases af <;> cases retAF <;> decide +kernel

def returned (af retAF : Bool) : OS.TSO64.State × Observation :=
  checked (returnAttempt af retAF) (return_succeeds af retAF)

theorem returned_actual (af retAF : Bool) :
    step (peerPublished af).1 (.issue 0 retAF) .sharedCell = .ok (returned af retAF) :=
  checked_ok (returnAttempt af retAF) (return_succeeds af retAF)

def ownPublicationAttempt (af retAF : Bool) : Except Fault (OS.TSO64.State × Observation) :=
  step (returned af retAF).1 (.drain 0) .sharedCell

theorem own_publication_succeeds (af retAF : Bool) :
    (ownPublicationAttempt af retAF).toOption.isSome = true := by
  cases af <;> cases retAF <;> decide +kernel

def closed (af retAF : Bool) : OS.TSO64.State × Observation :=
  checked (ownPublicationAttempt af retAF) (own_publication_succeeds af retAF)

theorem closed_actual (af retAF : Bool) :
    step (returned af retAF).1 (.drain 0) .sharedCell = .ok (closed af retAF) :=
  checked_ok (ownPublicationAttempt af retAF) (own_publication_succeeds af retAF)

def actions (af retAF : Bool) : List Action :=
  [.issue 0 af, .drain 1, .issue 0 retAF, .drain 0]

def result (af retAF : Bool) : OS.TSO64.State × List Observation :=
  ((closed af retAF).1,
    [(loaded af).2, (peerPublished af).2, (returned af retAF).2, (closed af retAF).2])

theorem scheduled (af retAF : Bool) :
    schedule boundary (actions af retAF) .sharedCell = .ok (result af retAF) := by
  simp only [actions, result, schedule, loaded_actual, peer_published_actual,
    returned_actual, closed_actual, ok_bind, pure_ok]

theorem final_reader_present (af retAF : Bool) :
    ((result af retAF).1.workers[0]?).isSome = true := by
  cases af <;> cases retAF <;> decide +kernel

def finalReader (af retAF : Bool) : Worker :=
  found ((result af retAF).1.workers[0]?) (final_reader_present af retAF)

theorem final_live (af retAF : Bool) : (result af retAF).1.workers[0]? = some (finalReader af retAF) :=
  found_ok _ (final_reader_present af retAF)

theorem final_returned (af retAF : Bool) : (finalReader af retAF).phase = .returned := by
  cases af <;> cases retAF <;> decide +kernel

private theorem body_node {bytes : List Byte} {operation : Operation}
    (shape : Shape bytes operation 0 []) :
    X86.VCGen.AtomicMethods.Node bytes 0 (.ordinary operation.instruction) := by
  cases shape with
  | body access _ _ => exact access

/-- Recognize the access from the actual checked decoder, independently of the
reply chosen by the progress annotation. Index zero has an empty real prefix. -/
private theorem dispatched_at_entry (af : Bool) (plan : List Action)
    (output : OS.TSO64.State × List Observation) (head : plan[0]? = some (.issue 0 af)) :
    DispatchedAt 0 boundary plan output 0 := by
  refine ⟨boundary, .issue 0 af, loaded af, rfl, head, loaded_actual af, ?_⟩
  refine ⟨af, boundaryReader, method.operation.instruction, rfl, live, ?_, True.intro⟩
  exact (present.decode_node live entry.resources (body_node entry.location.2.2.2)
    entry.location.2.1).1

/-- Recover the literal reply from its real access prestate/local read, rather
than from a final RAX or an expected Operation.registers calculation. -/
private theorem empty_prefix_state {state before : OS.TSO64.State} {plan : List Action}
    {observations : List Observation}
    (prefixRun : schedule state (plan.take 0) .sharedCell = .ok (before, observations.take 0)) :
    before = state := (congrArg Prod.fst (Except.ok.inj prefixRun)).symm

private theorem entry_reply {plan : List Action} {output : OS.TSO64.State × List Observation}
    {reply : method.operation.Reply} (access : AccessAt method 0 boundary plan output 0 reply) :
    reply = (0x1122334455667788 : Word) := by
  obtain ⟨before, _, _, prefixRun, _, _, _, origin⟩ := access
  have beforeEq : before = boundary := empty_prefix_state (state := boundary) prefixRun
  subst before
  obtain ⟨_, worker, _, workerLive, _, _, _, _, _, _, _, _, _, value⟩ := origin.evidence
  have same : worker = boundaryReader := Option.some.inj (workerLive.symm.trans live)
  subst worker
  have read : loadQWord (localCPU boundary boundaryReader).memory 65536 = .ok reply := value.1
  exact Except.ok.inj (read.symm.trans boundary_reads.1)

private theorem reply_rax (value : Word) : method.responded value .rax = value :=
  X86.VCGen.AtomicMethods.written_same _ _ _

private theorem body_counter {worker : Worker} {reply : method.operation.Reply}
    (post : BodyPost method worker reply) : worker.nextStore = 1 := by
  have counter := post.queue.counter
  dsimp only [Method.queueAfter, method, PlainMethods.operation] at counter
  exact counter.trans boundary_counter

/-- The generic engine constructs a completion for every pair of caller AF
choices, from the admitted nonempty FIFO. Its actual access, body contract and
literal response are then recovered through all_completed, not assumed. -/
theorem admitted_completion (choices : Nat → Bool) :
    ∃ output final,
      schedule boundary [.issue 0 (choices 0), .issue 0 (choices 1)] .sharedCell = .ok output ∧
      output.1.workers[0]? = some final ∧ BodyPost method final (0x1122334455667788 : Word) ∧
      OneAccess method 0 boundary [.issue 0 (choices 0), .issue 0 (choices 1)] output
        (0x1122334455667788 : Word) ∧
      AccessAt method 0 boundary [.issue 0 (choices 0), .issue 0 (choices 1)] output 0
        (0x1122334455667788 : Word) ∧
      final.nextStore = 1 ∧
      OS.TSO64.Return.returnValue (output.1, .returned 0) = some (0, 0x1122334455667788) := by
  obtain ⟨plan, output, final, _, planEq, _, _, success, finalLive, located⟩ :=
    complete present live entry choices
  have exactPlan : plan = [.issue 0 (choices 0), .issue 0 (choices 1)] := by
    simpa only [Point.remaining, List.length_nil, List.range_succ, List.range_zero,
      List.map_append, List.map_nil, List.map_cons, List.nil_append,
      List.singleton_append] using planEq
  subst plan
  obtain ⟨_, reply, post, oneAccess, _, response⟩ :=
    all_completed present live entry success finalLive located.location.1
  have access := oneAccess.at (dispatched_at_entry (choices 0) _ output rfl)
  have literal := entry_reply access
  subst reply
  exact ⟨output, final, success, finalLive, post, oneAccess, access,
    body_counter post,
    response.trans (congrArg some (congrArg (fun value : Word => (0, value)) (reply_rax _)))⟩

/-- All four AF schedules include actual peer publication between the MOV and
RET, then the own head drain. The generic family provides the full body/FIFO
contract and unique access at original action zero, with a literal retained
reply and return RAX even though shared RAM has changed before the response. -/
theorem interfering_completion (af retAF : Bool) :
    Current method (result af retAF).1 ∧
    BodyPost method (finalReader af retAF) (0x1122334455667788 : Word) ∧
    OneAccess method 0 boundary (actions af retAF) (result af retAF) (0x1122334455667788 : Word) ∧
    AccessAt method 0 boundary (actions af retAF) (result af retAF) 0 (0x1122334455667788 : Word) ∧
    (∀ index, DispatchedAt 0 boundary (actions af retAF) (result af retAF) index → index = 0) ∧
    X86.VCGen.AtomicMethods.ownIssues 0 (actions af retAF) = 2 ∧
    (finalReader af retAF).nextStore = 1 ∧
    OS.TSO64.Return.returnValue ((result af retAF).1, .returned 0) =
      some (0, 0x1122334455667788) := by
  obtain ⟨current, reply, post, oneAccess, count, response⟩ :=
    all_completed present live entry (scheduled af retAF) (final_live af retAF) (final_returned af retAF)
  have dispatched := dispatched_at_entry af (actions af retAF) (result af retAF) rfl
  have access := oneAccess.at dispatched
  have literal := entry_reply access
  subst reply
  refine ⟨current, post, oneAccess, access, ?_, count, body_counter post,
    response.trans (congrArg some (congrArg (fun value : Word => (0, value)) (reply_rax _)))⟩
  intro index atIndex
  obtain ⟨position, _, unique⟩ := oneAccess
  exact (unique index atIndex).trans (unique 0 dispatched).symm

structure Summary where
  words : List (List (Except Error Word))
  boundaryWorkers : List PlainMethods.WorkerView
  returnedWorkers : List PlainMethods.WorkerView
  finalWorkers : List PlainMethods.WorkerView
  savedRaxAfterPeer : Option Word
  responses : List (Option (Nat × Word))
  returnFrame : Bool
  resourcesKept : Bool
  collectAtReturn : Except Fault Word
  collectAfterDrain : Except Fault Word
  drains : List PlainMethods.DrainView
  kinds : List (Nat × Nat)
  retired : List Nat
  deriving DecidableEq

def summarize (af retAF : Bool) : Summary where
  words := [boundary, (loaded af).1, (peerPublished af).1, (returned af retAF).1,
    (closed af retAF).1].map PlainMethods.worldWords
  boundaryWorkers := boundary.workers.map PlainMethods.workerView
  returnedWorkers := (returned af retAF).1.workers.map PlainMethods.workerView
  finalWorkers := (closed af retAF).1.workers.map PlainMethods.workerView
  savedRaxAfterPeer := (peerPublished af).1.workers[0]?.map fun worker => worker.context.registers .rax
  responses := [OS.TSO64.Return.returnValue (loaded af), OS.TSO64.Return.returnValue (peerPublished af),
    OS.TSO64.Return.returnValue (returned af retAF), OS.TSO64.Return.returnValue (closed af retAF)]
  returnFrame := PlainMethods.retainedAcrossRet (peerPublished af).1 (returned af retAF).1
  resourcesKept := PlainMethods.authorityKept initial (closed af retAF).1
  collectAtReturn := collect (returned af retAF).1 0
  collectAfterDrain := collect (closed af retAF).1 0
  drains := (result af retAF).2.filterMap TSO64DrainClosure.observationSummary
  kinds := (result af retAF).2.map PlainMethods.eventKind
  retired := (result af retAF).2.map Observation.retired

-- Independently specified GPR observations. These are not execution inputs.
def readerEntryRegisters : List Word :=
  [5, 131076, 131072, 0x8877665544332211, 262144, 0x8877665544332211, 9, 65536,
    0x8877665544332211, 0x8877665544332211, 0x8877665544332211, 0x8877665544332211,
    0x8877665544332211, 0x8877665544332211, 0x8877665544332211, 0x8877665544332211]

def peerRunningRegisters : List Word :=
  [5, 196612, 196608, 0x8877665544332211, 327680, 0x8877665544332211,
    0xfedcba9876543210, 65536,
    0x8877665544332211, 0x8877665544332211, 0x8877665544332211, 0x8877665544332211,
    0x8877665544332211, 0x8877665544332211, 0x8877665544332211, 0x8877665544332211]

def expected : Summary where
  words := [
    [.ok 0, .ok 0, .ok 0x1122334455667788, .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000],
    [.ok 0, .ok 0, .ok 0x1122334455667788, .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000],
    [.ok 0, .ok 0, .ok 0xfedcba9876543210, .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000],
    [.ok 0, .ok 0, .ok 0xfedcba9876543210, .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000],
    [.ok 9, .ok 0, .ok 0xfedcba9876543210, .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000]]
  boundaryWorkers := [
    ⟨readerEntryRegisters, 393219, 0x200202, .running, [(0, 131072, .qword 9, none)], 1⟩,
    ⟨peerRunningRegisters, 393226, 0x200202, .running,
      [(1, 65536, .qword 0xfedcba9876543210, some 0)], 1⟩]
  returnedWorkers := [
    ⟨PlainMethods.acquireReaderRegisters, 0x7000, 0x200202, .returned,
      [(0, 131072, .qword 9, none)], 1⟩,
    ⟨peerRunningRegisters, 393226, 0x200202, .running, [], 1⟩]
  finalWorkers := [
    ⟨PlainMethods.acquireReaderRegisters, 0x7000, 0x200202, .returned, [], 1⟩,
    ⟨peerRunningRegisters, 393226, 0x200202, .running, [], 1⟩]
  savedRaxAfterPeer := some 0x1122334455667788
  responses := [none, none, some (0, 0x1122334455667788), none]
  returnFrame := true
  resourcesKept := true
  collectAtReturn := .error .resource
  collectAfterDrain := .ok 0x1122334455667788
  drains := [(1, 1, 65536, .qword 0xfedcba9876543210, some 0), (0, 0, 131072, .qword 9, none)]
  kinds := [(0, 0), (2, 1), (1, 0), (2, 0)]
  retired := [1, 0, 1, 0]

/-- Independent observable regression requirements: the load retains old RAX
across peer publication and RET; only the final own drain publishes 9. Both
allocation counters stay 1, the peer remains running, caller/neighbor words and
all other GPRs survive, and collection requires the outstanding own publication.
The response is at action 2, after the peer drain at 1, not at own-issue index 1. -/
theorem literal_interference_observations (af retAF : Bool) : summarize af retAF = expected := by
  cases af <;> cases retAF <;> decide +kernel

/-- The response at original action 2 has a production RET/resource origin.
Its value is independently checked above and differs from the then-current RAM. -/
theorem response_origin (af retAF : Bool) :
    (actions af retAF)[2]? = some (.issue 0 retAF) ∧
    (result af retAF).2[2]? = some (.returned 0) ∧
    OS.TSO64.Return.ReturnOrigin (peerPublished af).1 (.issue 0 retAF)
      (returned af retAF) 0 0x1122334455667788 .sharedCell := by
  have response : OS.TSO64.Return.returnValue (returned af retAF) =
      some (0, 0x1122334455667788) := by
    cases af <;> cases retAF <;> decide +kernel
  have observed : (returned af retAF).2 = .returned 0 := by
    cases af <;> cases retAF <;> decide +kernel
  refine ⟨rfl, ?_, OS.TSO64.Return.returnValue_sound
    (step_wellFormed (step_wellFormed present.valid (loaded_actual af)) (peer_published_actual af))
      (returned_actual af retAF) response⟩
  change some (returned af retAF).2 = some (.returned 0)
  exact congrArg some observed

/-- The generic completed-call adapter retains action 2 as the actual RET,
despite the intervening peer publication. Its access reply remains the old
word; the then-current shared word has already changed. -/
theorem matched_call (af retAF : Bool) :
    ∃ completed : CompletedCall method 0 boundary (actions af retAF) (result af retAF),
      completed.performed = 0 ∧ completed.returned = 2 ∧
      completed.reply = (0x1122334455667788 : Word) ∧
      ResponseAt method 0 boundary (actions af retAF) (result af retAF) 2
        (0x1122334455667788 : Word) := by
  obtain ⟨completed⟩ := completed_call present live entry (scheduled af retAF)
    (final_live af retAF) (final_returned af retAF)
  have performed : completed.performed = 0 :=
    (completed.performed_unique (dispatched_at_entry af _ _ rfl)).symm
  have returned : completed.returned = 2 :=
    (completed.responseUnique 2 (response_origin af retAF).2.1).symm
  have access : AccessAt method 0 boundary (actions af retAF) (result af retAF) 0
      completed.reply := by simpa only [performed] using completed.access
  have reply := entry_reply access
  refine ⟨completed, performed, returned, reply, ?_⟩
  simpa only [returned, reply] using completed.response

end EDSL.Tests.PlainCallInterference

#print axioms EDSL.Tests.PlainCallInterference.present
#print axioms EDSL.Tests.PlainCallInterference.entry
#print axioms EDSL.Tests.PlainCallInterference.admitted_access_enabled
#print axioms EDSL.Tests.PlainCallInterference.admitted_completion
#print axioms EDSL.Tests.PlainCallInterference.interfering_completion
#print axioms EDSL.Tests.PlainCallInterference.literal_interference_observations
#print axioms EDSL.Tests.PlainCallInterference.response_origin
#print axioms EDSL.Tests.PlainCallInterference.matched_call
#audit_edsl
