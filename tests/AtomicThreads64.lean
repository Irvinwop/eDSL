/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicThreads64.Trace
import EDSL.Audit

namespace EDSL.Tests.AtomicThreads64
open X86 OS.AddressSpace
open OS.AtomicThreads64
abbrev AState := OS.Atomics64.State
abbrev TState := OS.AtomicThreads64.State
abbrev TFault := OS.AtomicThreads64.Fault

/-- Owned loader: exact five bytes, two private caller slots, full64 data and
an adjacent qword in the same allocation. Literal oracles below are independent
of the implementation's OR, byte store and context-update definitions. -/
def seed (old : Word) : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0xf0, readExecute⟩
    | 4097 => some ⟨0x48, readExecute⟩
    | 4098 => some ⟨0x09, readExecute⟩
    | 4099 => some ⟨0x37, readExecute⟩
    | 4100 => some ⟨0xc3, readExecute⟩
    | 32769 => some ⟨0x20, readOnly⟩
    | 32785 => some ⟨0x30, readOnly⟩
    | 32768 | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 |
      32784 | 32786 | 32787 | 32788 | 32789 | 32790 | 32791 => some ⟨0, readOnly⟩
    | 65536 => some ⟨old.extractLsb' 0 8, readWrite⟩
    | 65537 => some ⟨old.extractLsb' 8 8, readWrite⟩
    | 65538 => some ⟨old.extractLsb' 16 8, readWrite⟩
    | 65539 => some ⟨old.extractLsb' 24 8, readWrite⟩
    | 65540 => some ⟨old.extractLsb' 32 8, readWrite⟩
    | 65541 => some ⟨old.extractLsb' 40 8, readWrite⟩
    | 65542 => some ⟨old.extractLsb' 48 8, readWrite⟩
    | 65543 => some ⟨old.extractLsb' 56 8, readWrite⟩
    | 65544 => some ⟨0xef, readWrite⟩
    | 65545 => some ⟨0xcd, readWrite⟩
    | 65546 => some ⟨0xab, readWrite⟩
    | 65547 => some ⟨0x89, readWrite⟩
    | 65548 => some ⟨0x67, readWrite⟩
    | 65549 => some ⟨0x45, readWrite⟩
    | 65550 => some ⟨0x23, readWrite⟩
    | 65551 => some ⟨0x01, readWrite⟩
    | _ => none

def entry (stack mask : Word) : Context where
  registers register := if register = .rdi then 65536 else if register = .rsp then stack
    else if register = .rsi then mask else 0xdeadbeef76543210
  rip := 4096
  flags := 0xed7

def withTicket (state : AState) (operation : OS.Ownership.Mutation) :
    Except TFault (AState × OS.Ownership.Ticket) := do
  let (after, ticket) ← (OS.Atomics64.mutate state operation).mapError OS.AtomicThreads64.Fault.atomic
  match ticket with
  | none => throw .unexpectedStep
  | some ticket => pure (after, ticket)

/-- Registration precedes managed creation; the managed history has no raw
registration/loan-close action. -/
def setup (old a b : Word) : Except TFault (TState × Start × Start × OS.Ownership.Ticket) := do
  let initial := OS.Atomics64.empty (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty (seed old))))
  let (data, dataTicket) ← withTicket initial (.adopt 0 ⟨65536, 16⟩)
  let (code, codeTicket) ← withTicket data (.adopt 0 ⟨4096, 5⟩)
  let (one, stackA) ← withTicket code (.adopt 0 ⟨32768, 8⟩)
  let (both, stackB) ← withTicket one (.adopt 0 ⟨32784, 8⟩)
  let (registered, cell) ← (OS.Atomics64.enroll both 0 dataTicket 65536).mapError OS.AtomicThreads64.Fault.atomic
  pure (empty registered, ⟨entry 32768 a, cell, codeTicket, stackA⟩,
    ⟨entry 32784 b, cell, codeTicket, stackB⟩, dataTicket)

def failureIs {α : Type} (operation : Except TFault α) (expected : TFault) : Bool :=
  match operation with
  | .error actual => decide (actual = expected)
  | .ok _ => false

def completedContext (state : TState) (identifier : Nat) : Except TFault Context := do
  let some worker := state.workers identifier | throw .missingThread
  match worker.phase with
  | .completed _ context => pure context
  | _ => throw .notCompleted

structure ContextView where
  gprs : List Word
  rip : Word
  flagsWithoutAF : Word
  af : Bool
  deriving DecidableEq, Repr

def view (context : Context) : ContextView :=
  ⟨[.rax,.rbx,.rcx,.rdx,.rsi,.rdi,.rbp,.rsp,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15].map context.registers,
    context.rip, context.flags &&& ~~~(0x10 : Word), context.flags.getLsbD 4⟩

structure Observed where
  a : ContextView
  b : ContextView
  word : Option Word
  bytes : List (Option Byte)
  guard : Option Word
  labels : List Observation
  afterAJoin : Option Word
  deriving DecidableEq, Repr

/-- Uses real spawn/dispatch/RET/join. In ABAB/ABBA, B writes between A's
RMW and RET, so restoring an isolated A snapshot loses the upper bit. -/
def twoWorkers (selections : List Selection) : Except TFault Observed := do
  let (initial, a, b, _) ← setup 0x0edcba9876543210 1 0x8000000000000000
  let (one, aid) ← spawn initial 0 a
  let (both, bid) ← spawn one 0 b
  let (done, labels) ← schedule both selections
  let (first, actx) ← join done 0 aid
  let afterAJoin := (loadQWord (toMemory first.shared.legacy.shared.resources.space) 65536).toOption
  let (last, bctx) ← join first 0 bid
  let memory := toMemory last.shared.legacy.shared.resources.space
  pure ⟨view actx, view bctx, (loadQWord memory 65536).toOption,
    [65536,65537,65538,65539,65540,65541,65542,65543].map memory.read,
    (loadQWord memory 65544).toOption, labels, afterAJoin⟩

-- All sixteen registers are observed after the real return and join. RAX
-- retains its high half, RSP advances once, and the two caller targets differ.
def aContext (flags : Word) (af : Bool) : ContextView :=
  ⟨[0xdeadbeef76543210,0xdeadbeef76543210,0xdeadbeef76543210,0xdeadbeef76543210,
    1,65536,0xdeadbeef76543210,32776,0xdeadbeef76543210,0xdeadbeef76543210,
    0xdeadbeef76543210,0xdeadbeef76543210,0xdeadbeef76543210,0xdeadbeef76543210,
    0xdeadbeef76543210,0xdeadbeef76543210],8192,flags,af⟩

def bContext (flags : Word) (af : Bool) : ContextView :=
  ⟨[0xdeadbeef76543210,0xdeadbeef76543210,0xdeadbeef76543210,0xdeadbeef76543210,
    0x8000000000000000,65536,0xdeadbeef76543210,32792,0xdeadbeef76543210,0xdeadbeef76543210,
    0xdeadbeef76543210,0xdeadbeef76543210,0xdeadbeef76543210,0xdeadbeef76543210,
    0xdeadbeef76543210,0xdeadbeef76543210],12288,flags,af⟩

def aFirst : OS.Atomics64.Event := ⟨1,⟨0⟩,⟨0⟩,⟨.bor,1,⟨65536,0x0edcba9876543210,0x0edcba9876543211⟩⟩⟩
def bSecond : OS.Atomics64.Event := ⟨2,⟨1⟩,⟨0⟩,⟨.bor,0x8000000000000000,
  ⟨65536,0x0edcba9876543211,0x8edcba9876543211⟩⟩⟩
def bFirst : OS.Atomics64.Event := ⟨2,⟨1⟩,⟨0⟩,⟨.bor,0x8000000000000000,
  ⟨65536,0x0edcba9876543210,0x8edcba9876543210⟩⟩⟩
def aSecond : OS.Atomics64.Event := ⟨1,⟨0⟩,⟨0⟩,⟨.bor,1,⟨65536,0x8edcba9876543210,0x8edcba9876543211⟩⟩⟩

def expected (a b : ContextView) (labels : List Observation) : Observed :=
  ⟨a,b,some 0x8edcba9876543211,
    [some 0x11,some 0x32,some 0x54,some 0x76,some 0x98,some 0xba,some 0xdc,some 0x8e],
    some 0x0123456789abcdef,labels,some 0x8edcba9876543211⟩

-- Six legal interleavings, every AF combination for every selected instruction.
example (a b c d : Bool) : twoWorkers [(0,a),(0,b),(1,c),(1,d)] =
    .ok (expected (aContext 0x606 a) (bContext 0x686 c)
      [((0,a),some aFirst),((0,b),none),((1,c),some bSecond),((1,d),none)]) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
example (a b c d : Bool) : twoWorkers [(0,a),(1,b),(0,c),(1,d)] =
    .ok (expected (aContext 0x606 a) (bContext 0x686 b)
      [((0,a),some aFirst),((1,b),some bSecond),((0,c),none),((1,d),none)]) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
example (a b c d : Bool) : twoWorkers [(0,a),(1,b),(1,c),(0,d)] =
    .ok (expected (aContext 0x606 a) (bContext 0x686 b)
      [((0,a),some aFirst),((1,b),some bSecond),((1,c),none),((0,d),none)]) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
example (a b c d : Bool) : twoWorkers [(1,a),(0,b),(0,c),(1,d)] =
    .ok (expected (aContext 0x686 b) (bContext 0x682 a)
      [((1,a),some bFirst),((0,b),some aSecond),((0,c),none),((1,d),none)]) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
example (a b c d : Bool) : twoWorkers [(1,a),(0,b),(1,c),(0,d)] =
    .ok (expected (aContext 0x686 b) (bContext 0x682 a)
      [((1,a),some bFirst),((0,b),some aSecond),((1,c),none),((0,d),none)]) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
example (a b c d : Bool) : twoWorkers [(1,a),(1,b),(0,c),(0,d)] =
    .ok (expected (aContext 0x686 c) (bContext 0x682 a)
      [((1,a),some bFirst),((1,b),none),((0,c),some aSecond),((0,d),none)]) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- A peer RMW occurs after A's RMW and before A's RET. Join A occurs
while B is still returning. Both RET and join must retain B's current word. -/
def peerBetween : Except TFault (List (Option Word) × List Bool) := do
  let (initial, a, b, dataTicket) ← setup 0x0edcba9876543210 1 0x8000000000000000
  let (one, aid) ← spawn initial 0 a
  let (both, bid) ← spawn one 0 b
  let (written, _) ← schedule both [(aid,false),(bid,true)]
  let (returnedA, _) ← dispatch written aid true
  let atRet := (loadQWord (toMemory returnedA.shared.legacy.shared.resources.space) 65536).toOption
  let busyBefore := failureIs (retire returnedA 0 a.cell) (.atomic .liveHandles)
  let (joinedA, _) ← join returnedA 0 aid
  let atJoin := (loadQWord (toMemory joinedA.shared.legacy.shared.resources.space) 65536).toOption
  let blocked := failureIs (mutate joinedA (.store64 0 dataTicket 65544 0)) (.atomic .reserved)
  let earlyB := failureIs (join joinedA 0 bid) .notCompleted
  let (returnedB, _) ← dispatch joinedA bid false
  let busyCompleted := failureIs (retire returnedB 0 a.cell) (.atomic .liveHandles)
  let (joinedB, _) ← join returnedB 0 bid
  let persistent := failureIs (mutate joinedB (.store64 0 dataTicket 65544 0)) (.atomic .reserved)
  let readDenied := match OS.Atomics64.readBorrow joinedB.shared 0 dataTicket 7 ⟨65544,8⟩ with
    | .error .reserved => true | _ => false
  let retired ← retire joinedB 0 a.cell
  let (changed, _) ← mutate retired (.store64 0 dataTicket 65544 0x8070605040302010)
  pure ([atRet,atJoin,(loadQWord (toMemory changed.shared.legacy.shared.resources.space) 65544).toOption],
    [busyBefore,blocked,earlyB,busyCompleted,persistent,readDenied])

example : peerBetween = .ok
    ([some 0x8edcba9876543211,some 0x8edcba9876543211,some 0x8070605040302010],
     [true,true,true,true,true,true]) := by rfl

/-- Repeated/overlapping masks retain their actual no-change RMW, and RET
still emits none. The old word includes high bits before either worker runs. -/
def duplicateMasks : Except TFault (List Observation × Option Word) := do
  let (initial, a, b, _) ← setup 0x0100000100000000 0x8000000000000080 0x8000000000000080
  let (one, _) ← spawn initial 0 a
  let (both, _) ← spawn one 0 b
  let (done, labels) ← schedule both [(0,false),(1,true),(1,false),(0,true)]
  let (oneJoined, _) ← join done 0 0
  let (joined, _) ← join oneJoined 0 1
  pure (labels,(loadQWord (toMemory joined.shared.legacy.shared.resources.space) 65536).toOption)

example : duplicateMasks = .ok
    ([((0,false),some ⟨1,⟨0⟩,⟨0⟩,⟨.bor,0x8000000000000080,
      ⟨65536,0x0100000100000000,0x8100000100000080⟩⟩⟩),
      ((1,true),some ⟨2,⟨1⟩,⟨0⟩,⟨.bor,0x8000000000000080,
      ⟨65536,0x8100000100000080,0x8100000100000080⟩⟩⟩),((1,false),none),((0,true),none)],
      some 0x8100000100000080) := by rfl

def lifecycle : Except TFault (List Bool × Nat × List Observation) := do
  let (initial, a, _, _) ← setup 0 0 1
  let failed := failureIs (spawn initial 0 a false) .creationFailed
  let wrongRoot := failureIs (spawn initial 3 a) .wrongParent
  let badCell := failureIs (spawn initial 0 {a with cell := ⟨99⟩}) (.atomic .missingCell)
  -- This fails after the internal code-loan acquisition. Retrying the valid
  -- checked transaction must still receive the original fresh identities.
  let badStack := failureIs (spawn initial 0 {a with stackTicket := ⟨99,0⟩})
    (.atomic (.legacy (.authority (.ownership .missingAllocation))))
  let (started, id) ← spawn initial 0 a
  let early := failureIs (join started 0 id) .notCompleted
  let (appliedState, _) ← dispatch started id true
  let earlyRet := failureIs (join appliedState 0 id) .notCompleted
  let wrongParent := failureIs (join appliedState 8 id) .wrongParent
  let (done, retLabel) ← dispatch appliedState id false
  let noRetEvent := retLabel.isNone
  let repeated := failureIs (dispatch done id true) .alreadyCompleted
  let (joined, _) ← join done 0 id
  let repeatedJoin := failureIs (join joined 0 id) .missingThread
  let (again, fresh) ← spawn joined 0 a
  let staleDispatch := failureIs (dispatch again id false) .missingThread
  let (finished, labels) ← schedule again [(fresh,false),(fresh,true)]
  let (_, _) ← join finished 0 fresh
  pure ([failed,wrongRoot,badCell,badStack,early,earlyRet,wrongParent,noRetEvent,repeated,repeatedJoin,staleDispatch],
    fresh,labels)

example : lifecycle = .ok
    ([true,true,true,true,true,true,true,true,true,true,true],1,
      [((1,false),some ⟨2,⟨1⟩,⟨0⟩,⟨.bor,0,⟨65536,0,0⟩⟩⟩),((1,true),none)]) := by rfl

/-- Current code/stack loans and allocation-wide atomic reservation are
checked by actual environment operations, including unrelated allocation use. -/
def resourceGates : Except TFault (List Bool × Option Word) := do
  let (initial, a, _, dataTicket) ← setup 0x0edcba9876543210 1 0
  let (started, id) ← spawn initial 0 a
  let code := failureIs (mutate started (.protect 0 a.codeTicket readOnly))
    (.atomic (.legacy (.authority .borrowed)))
  let stack := failureIs (mutate started (.release 0 a.stackTicket))
    (.atomic (.legacy (.authority .borrowed)))
  let data := failureIs (mutate started (.store 0 dataTicket 65544 0)) (.atomic .reserved)
  let data64 := failureIs (mutate started (.store64 0 dataTicket 65544 0)) (.atomic .reserved)
  let transfer := failureIs (mutate started (.transfer 0 dataTicket 9)) (.atomic .reserved)
  let (allocated, result) ← mutate started (.allocate 0 ⟨131072,8⟩ readWrite)
  let some ticket := result | throw .unexpectedStep
  let (changed, _) ← mutate allocated (.store64 0 ticket 131072 0xfedcba9876543210)
  let (done, _) ← schedule changed [(id,false),(id,true)]
  let (joined, _) ← join done 0 id
  pure ([code,stack,data,data64,transfer],
    (loadQWord (toMemory joined.shared.legacy.shared.resources.space) 131072).toOption)

example : resourceGates = .ok ([true,true,true,true,true],some 0xfedcba9876543210) := by rfl

-- Symbolic nonvacuity: actual checked adoption, registration and spawn, for
-- arbitrary full64 initial word and mask, establish CURRENT live authority.
def dataWorld (old : Word) : OS.Ownership.World :=
  OS.Ownership.install (OS.Ownership.empty (seed old)) (seed old) 0 ⟨65536,16⟩
def codeWorld (old : Word) : OS.Ownership.World :=
  OS.Ownership.install (dataWorld old) (seed old) 0 ⟨4096,5⟩
def stackWorld (old : Word) : OS.Ownership.World :=
  OS.Ownership.install (codeWorld old) (seed old) 0 ⟨32768,8⟩
def fullWorld (old : Word) : OS.Ownership.World :=
  OS.Ownership.install (stackWorld old) (seed old) 0 ⟨32784,8⟩

theorem data_adopted (old : Word) :
    OS.Ownership.adopt (OS.Ownership.empty (seed old)) 0 ⟨65536,16⟩ =
      .ok (dataWorld old,⟨0,0⟩) :=
  OS.Ownership.adopt_success _ _ _ (OS.Ownership.empty_wellFormed _) (by decide) (by rfl) (by rfl)
theorem data_valid (old : Word) : OS.Ownership.WellFormed (dataWorld old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (OS.Ownership.empty_wellFormed _) (data_adopted old)).1

theorem code_adopted (old : Word) :
    OS.Ownership.adopt (dataWorld old) 0 ⟨4096,5⟩ = .ok (codeWorld old,⟨1,0⟩) :=
  OS.Ownership.adopt_success _ _ _ (data_valid old) (by decide) (by rfl) (by rfl)
theorem code_valid (old : Word) : OS.Ownership.WellFormed (codeWorld old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (data_valid old) (code_adopted old)).1

theorem stack_adopted (old : Word) :
    OS.Ownership.adopt (codeWorld old) 0 ⟨32768,8⟩ = .ok (stackWorld old,⟨2,0⟩) :=
  OS.Ownership.adopt_success _ _ _ (code_valid old) (by decide) (by rfl) (by rfl)
theorem stack_valid (old : Word) : OS.Ownership.WellFormed (stackWorld old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (code_valid old) (stack_adopted old)).1

theorem full_adopted (old : Word) :
    OS.Ownership.adopt (stackWorld old) 0 ⟨32784,8⟩ = .ok (fullWorld old,⟨3,0⟩) :=
  OS.Ownership.adopt_success _ _ _ (stack_valid old) (by decide) (by rfl) (by rfl)
theorem full_valid (old : Word) : OS.Ownership.WellFormed (fullWorld old) :=
  (OS.Ownership.adopt_wellFormed _ _ _ _ (stack_valid old) (full_adopted old)).1

def raw (old : Word) : AState :=
  OS.Atomics64.empty (OS.Atomics.empty (OS.Borrowing.empty (fullWorld old)))
def registered (old : Word) : AState :=
  OS.Atomics64.installCell (raw old) ⟨0,⟨0,0⟩,65536⟩
theorem enrolled (old : Word) : OS.Atomics64.enroll (raw old) 0 ⟨0,0⟩ 65536 =
    .ok (registered old,⟨0⟩) := by rfl

theorem raw_valid (old : Word) : OS.Atomics64.WellFormed (raw old) :=
  OS.Atomics64.empty_wellFormed _ (OS.Atomics.empty_wellFormed _ (OS.Borrowing.empty_wellFormed _ (full_valid old)))
theorem registered_valid (old : Word) : OS.Atomics64.WellFormed (registered old) :=
  (OS.Atomics64.enroll_wellFormed _ _ _ _ _ (raw_valid old) (enrolled old)).1

def symbolicInitial (old : Word) : TState := empty (registered old)
def symbolicStart (mask : Word) : Start := ⟨entry 32768 mask,⟨0⟩,⟨1,0⟩,⟨2,0⟩⟩
def codeShared (old : Word) : AState :=
  { registered old with legacy := { (registered old).legacy with
    shared := OS.Borrowing.installLoan (registered old).legacy.shared ⟨⟨1,0⟩,0,1,⟨4096,5⟩⟩ } }
def stackShared (old : Word) : AState :=
  { codeShared old with legacy := { (codeShared old).legacy with
    shared := OS.Borrowing.installLoan (codeShared old).legacy.shared ⟨⟨2,0⟩,0,1,⟨32768,8⟩⟩ } }
def workerShared (old : Word) : AState := OS.Atomics64.installHandle (stackShared old) ⟨1,⟨0⟩⟩
def symbolicWorker (mask : Word) : Worker :=
  ⟨0,entry 32768 mask,⟨0⟩,8192,⟨0⟩,0,1,.applying (entry 32768 mask)⟩
def born (old mask : Word) : TState :=
  install (symbolicInitial old) (workerShared old) (symbolicWorker mask)

theorem created (old mask : Word) : spawn (symbolicInitial old) 0 (symbolicStart mask) =
    .ok (born old mask,0) := by rfl

theorem born_valid (old mask : Word) : WellFormed (born old mask) :=
  spawn_wellFormed _ _ _ _ _ (empty_wellFormed _ (registered_valid old)) (created old mask)

theorem symbolic_read (old mask : Word) :
    loadQWord (toMemory (born old mask).shared.legacy.shared.resources.space) 65536 = .ok old := by
  change Except.ok (joinQWord (old.extractLsb' 0 8) (old.extractLsb' 8 8)
    (old.extractLsb' 16 8) (old.extractLsb' 24 8) (old.extractLsb' 32 8)
    (old.extractLsb' 40 8) (old.extractLsb' 48 8) (old.extractLsb' 56 8)) = .ok old
  rw [qword_join_extracts]

/-- Arbitrary old/mask/AF choices run two actual instructions, retain full64
current-before history, return the exact private frame and preserve WF at join. -/
theorem all_words_execute (old mask : Word) (af retAF : Bool) :
    ∃ final labels joined value,
      schedule (born old mask) [(0,af),(0,retAF)] = .ok (final,labels) ∧
      join final 0 0 = .ok joined ∧ WellFormed joined.1 ∧
      loadQWord (toMemory joined.1.shared.legacy.shared.resources.space) 65536 = .ok value ∧
      (∀ index, Logical64.HasBit value index ↔ Logical64.HasBit old index ∨
        ∃ event ∈ events labels, Logical64.HasBit event.logical.mask index) ∧
      joined.2.registers .rsp = 32776 ∧
      ∀ register, register ≠ .rsp → joined.2.registers register = (entry 32768 mask).registers register := by
  have valid := born_valid old mask
  have live : (born old mask).workers 0 = some (symbolicWorker mask) := by rfl
  obtain ⟨final, labels, joined, scheduled, collected, finalValid⟩ :=
    two_dispatches_join _ _ _ af retAF valid live ⟨_,rfl⟩
  have allOn : AllOn (born old mask) ⟨0⟩ := by
    intro identifier worker found
    by_cases same : identifier = 0
    · subst identifier
      simp [born, install] at found
      cases found
      rfl
    · simp [born,install,symbolicInitial,OS.AtomicThreads64.empty,same] at found
  obtain ⟨value, read, bits⟩ := schedule_membership _ _ _ ⟨0⟩ ⟨0,⟨0,0⟩,65536⟩ old valid
    (by rfl) allOn (symbolic_read old mask) scheduled
  have frame := joined_private_frame (schedule_history _ _ _ scheduled) valid 0
    (symbolicWorker mask) live 0 joined collected
  refine ⟨final, labels, joined, value, scheduled, collected, finalValid, ?_, bits, ?_, frame.2⟩
  · rw [(join_resources _ _ _ _ collected).1]
    exact read
  · exact frame.1

-- An omitted initial bit and every actual emitted mask cannot appear later.
-- This is a natural-number membership consequence, not a copied byte-update
-- expression or a fixture assertion.
example (old mask : Word) (af retAF : Bool) (index : Fin 64)
    (initialAbsent : ¬ Logical64.HasBit old index) :
    ∃ final labels joined value,
      schedule (born old mask) [(0,af),(0,retAF)] = .ok (final,labels) ∧
      join final 0 0 = .ok joined ∧
      loadQWord (toMemory joined.1.shared.legacy.shared.resources.space) 65536 = .ok value ∧
      ((∀ event ∈ events labels, ¬ Logical64.HasBit event.logical.mask index) → ¬ Logical64.HasBit value index) := by
  obtain ⟨final,labels,joined,value,scheduled,collected,_,read,bits,_,_⟩ := all_words_execute old mask af retAF
  refine ⟨final,labels,joined,value,scheduled,collected,read,?_⟩
  intro masks bit
  rcases (bits index).mp bit with oldBit | ⟨event,member,eventBit⟩
  · exact initialAbsent oldBit
  · exact masks event member eventBit

-- Managed join permanently revokes the thread, handle and both loan IDs,
-- even when later histories contain new workers and ordinary allocations.
example {before after : TState} {middle : TState × Context} {labels : List (Option OS.Atomics64.Event)}
    (parent identifier : Nat) (valid : WellFormed before)
    (joined : join before parent identifier = .ok middle) (history : History middle.1 labels after) :
    dispatch after identifier true = .error .missingThread ∧
      ∃ worker, before.workers identifier = some worker ∧
        OS.Atomics64.logicalDiscard after.shared (principal identifier) worker.handle 0 = .error .missingHandle ∧
        OS.Borrowing.authorize after.shared.legacy.shared (principal identifier) worker.codeLoan = .error .missingLoan ∧
        OS.Borrowing.authorize after.shared.legacy.shared (principal identifier) worker.stackLoan = .error .missingLoan := by
  obtain ⟨worker,live,handle,code,stack⟩ := joined_resources_for_history parent identifier valid joined history
  exact ⟨(joined_for_history parent identifier valid joined history).dispatch_denied true,
    worker,live,handle.logicalDiscard_denied _ _,code.unauthorized _,stack.unauthorized _⟩

def secondCode (old : Word) : AState :=
  { workerShared old with legacy := { (workerShared old).legacy with
    shared := OS.Borrowing.installLoan (workerShared old).legacy.shared ⟨⟨1,0⟩,0,2,⟨4096,5⟩⟩ } }
def secondStack (old : Word) : AState :=
  { secondCode old with legacy := { (secondCode old).legacy with
    shared := OS.Borrowing.installLoan (secondCode old).legacy.shared ⟨⟨3,0⟩,0,2,⟨32784,8⟩⟩ } }
def secondShared (old : Word) : AState := OS.Atomics64.installHandle (secondStack old) ⟨2,⟨0⟩⟩
def secondWorker (mask : Word) : Worker :=
  ⟨0,entry 32784 mask,⟨0⟩,12288,⟨1⟩,2,3,.applying (entry 32784 mask)⟩
def bornTwo (old a b : Word) : TState := install (born old a) (secondShared old) (secondWorker b)

theorem second_created (old a b : Word) :
    spawn (born old a) 0 ⟨entry 32784 b,⟨0⟩,⟨1,0⟩,⟨3,0⟩⟩ = .ok (bornTwo old a b,1) := by rfl

theorem both_valid (old a b : Word) : WellFormed (bornTwo old a b) :=
  spawn_wellFormed _ _ _ _ _ (born_valid old a) (second_created old a b)

theorem both_allOn (old a b : Word) : AllOn (bornTwo old a b) ⟨0⟩ := by
  intro identifier worker found
  by_cases second : identifier = 1
  · subst identifier
    simp [bornTwo, install, born] at found
    cases found
    rfl
  · by_cases first : identifier = 0
    · subst identifier
      simp [bornTwo, install, born, symbolicInitial, OS.AtomicThreads64.empty] at found
      cases found
      rfl
    · simp [bornTwo,install,born,symbolicInitial,OS.AtomicThreads64.empty,first,second] at found

/-- A nonvacuous two-actor instance of arbitrary finite interleavings. Masks
and initial full64 RAM are completely arbitrary, including overlap/duplicates.
The only schedule assumptions are current identities and remaining counts. -/
theorem arbitrary_two_interleavings (old a b : Word) (selections : List Selection)
    (actors : ∀ selection ∈ selections, selection.1 = 0 ∨ selection.1 = 1)
    (aCount : selectedCount selections 0 ≤ 2) (bCount : selectedCount selections 1 ≤ 2) :
    ∃ after observations value,
      schedule (bornTwo old a b) selections = .ok (after,observations) ∧ WellFormed after ∧
      InstructionTrace (bornTwo old a b) observations after ∧
      loadQWord (toMemory after.shared.legacy.shared.resources.space) 65536 = .ok value ∧
      ∀ index, Logical64.HasBit value index ↔ Logical64.HasBit old index ∨
        ∃ event ∈ events observations, Logical64.HasBit event.logical.mask index := by
  have legal : Admissible (bornTwo old a b) selections := by
    intro identifier positive
    by_cases first : identifier = 0
    · subst identifier
      exact ⟨symbolicWorker a, by rfl, aCount⟩
    · by_cases second : identifier = 1
      · subst identifier
        exact ⟨secondWorker b, by rfl, bCount⟩
      · have absent : identifier ∉ selections.map Prod.fst := by
          intro member
          obtain ⟨selection,atSelection,same⟩ := List.mem_map.mp member
          rcases actors selection atSelection with zero | one
          · exact first (same.symm.trans zero)
          · exact second (same.symm.trans one)
        have countZero : selectedCount selections identifier = 0 := List.count_eq_zero.mpr absent
        omega
  exact schedule_enabled_membership _ _ ⟨0⟩ ⟨0,⟨0,0⟩,65536⟩ old
    (both_valid old a b) (by rfl) (both_allOn old a b) legal (symbolic_read old a)

end EDSL.Tests.AtomicThreads64

#audit_edsl
