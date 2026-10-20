/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicSetThreads64.Scheduling
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.AtomicSetThreads64
open X86 OS.AddressSpace OS.AtomicSetThreads64

abbrev Shared := OS.Atomics64.State
abbrev TState := OS.AtomicSetThreads64.State
abbrev TFault := OS.AtomicThreads64.Fault

/-- Owned code in three independently loaned windows, three caller slots, a
full64 target and a neighboring sentinel. These are loader bytes, not workers
or assertions that the checked lifecycle succeeds. -/
def seed (a b c : List Byte) (old : Word) : Space where
  cells address :=
    let n := address.toNat
    if 4096 ≤ n ∧ n < 4144 then
      let bytes := if n < 4112 then a else if n < 4128 then b else c
      let offset := if n < 4112 then n - 4096 else if n < 4128 then n - 4112 else n - 4128
      some ⟨bytes[offset]?.getD 0x90, readExecute⟩
    else if 32768 ≤ n ∧ n < 32776 then
      some ⟨(8192 : Word).extractLsb' (8 * (n - 32768)) 8, readOnly⟩
    else if 32784 ≤ n ∧ n < 32792 then
      some ⟨(12288 : Word).extractLsb' (8 * (n - 32784)) 8, readOnly⟩
    else if 32800 ≤ n ∧ n < 32808 then
      some ⟨(16384 : Word).extractLsb' (8 * (n - 32800)) 8, readOnly⟩
    else if 65536 ≤ n ∧ n < 65544 then
      some ⟨old.extractLsb' (8 * (n - 65536)) 8, readWrite⟩
    else if 65544 ≤ n ∧ n < 65552 then
      some ⟨(0x0123456789abcdef : Word).extractLsb' (8 * (n - 65544)) 8, readWrite⟩
    else none

def entry (pc stack mask : Word) : Context where
  registers register := if register = .rdi then 65536 else if register = .rsp then stack
    else if register = .rsi then mask else 0xdeadbeef76543210
  rip := pc
  flags := 0xed7

def withTicket (shared : Shared) (operation : OS.Ownership.Mutation) :
    Except TFault (Shared × OS.Ownership.Ticket) := do
  let (after, ticket) ← (OS.Atomics64.mutate shared operation).mapError OS.AtomicThreads64.Fault.atomic
  let some ticket := ticket | throw .unexpectedStep
  return (after, ticket)

def setup (a b c : List Byte) (old ma mb mc : Word) :
    Except TFault (TState × Start × Start × Start × OS.Ownership.Ticket) := do
  let initial := OS.Atomics64.empty
    (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty (seed a b c old))))
  let (data, dataTicket) ← withTicket initial (.adopt 0 ⟨65536, 16⟩)
  let (code, codeTicket) ← withTicket data (.adopt 0 ⟨4096, 48⟩)
  let (one, stackA) ← withTicket code (.adopt 0 ⟨32768, 8⟩)
  let (two, stackB) ← withTicket one (.adopt 0 ⟨32784, 8⟩)
  let (three, stackC) ← withTicket two (.adopt 0 ⟨32800, 8⟩)
  let (registered, cell) ← (OS.Atomics64.enroll three 0 dataTicket 65536).mapError OS.AtomicThreads64.Fault.atomic
  return (empty registered,
    ⟨entry 4096 32768 ma, a, cell, codeTicket, stackA⟩,
    ⟨entry 4112 32784 mb, b, cell, codeTicket, stackB⟩,
    ⟨entry 4128 32800 mc, c, cell, codeTicket, stackC⟩, dataTicket)

-- The harness invokes the production scheduler and retains every position. Its oracle
-- below is a literal current-before/current-after sequence, not a replay of
-- the machine's value fold or an assigned WorkerValid fixture.
def drive (state : TState) (selections : List Selection) :
    Except TFault (TState × List (Option OS.Atomics64.Event)) := do
  let result ← schedule state selections
  return (result.1, result.2.map Prod.snd)

structure View where
  registers : List Word
  rip : Word
  flags : Word
  deriving DecidableEq, Repr

def view (context : Context) : View :=
  ⟨[.rax,.rbx,.rcx,.rdx,.rsi,.rdi,.rbp,.rsp,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15].map
    context.registers, context.rip, context.flags⟩

structure Observed where
  word : Option Word
  bytes : List (Option Byte)
  guard : Option Word
  afterFirstJoin : Option Word
  events : List (Option OS.Atomics64.Event)
  contexts : List View
  deriving DecidableEq, Repr

def currentWord (state : TState) : Option Word :=
  (loadQWord (toMemory state.shared.legacy.shared.resources.space) 65536).toOption

def collectThree (state : TState) (events : List (Option OS.Atomics64.Event)) :
    Except TFault Observed := do
  let (one, a) ← join state 0 0
  let afterFirstJoin := currentWord one
  let (two, b) ← join one 0 1
  let (three, c) ← join two 0 2
  let memory := toMemory three.shared.legacy.shared.resources.space
  return ⟨currentWord three,
    [65536,65537,65538,65539,65540,65541,65542,65543].map memory.read,
    (loadQWord memory 65544).toOption, afterFirstJoin, events, [view a,view b,view c]⟩

def noncommuting (order : List (Nat × Bool)) : Except TFault Observed := do
  let (initial, a, b, c, _) ← setup
    [0xf0,0x48,0x21,0x37,0xc3] [0xf0,0x48,0x09,0x37,0xc3]
    [0xf0,0x48,0x31,0x37,0xc3] 0x8000000000000001 0x7fffffffffffffff 0x8000000000000000 1
  let (one, _) ← spawn initial 0 a
  let (two, _) ← spawn one 0 b
  let (three, _) ← spawn two 0 c
  let (done, events) ← drive three order
  collectThree done events

def expectedContext (mask stack target flags : Word) : View :=
  ⟨[0xdeadbeef76543210,0xdeadbeef76543210,0xdeadbeef76543210,0xdeadbeef76543210,
    mask,65536,0xdeadbeef76543210,stack,0xdeadbeef76543210,0xdeadbeef76543210,
    0xdeadbeef76543210,0xdeadbeef76543210,0xdeadbeef76543210,0xdeadbeef76543210,
    0xdeadbeef76543210,0xdeadbeef76543210],target,flags⟩

def event (actor handle : Nat) (op : Sequential.LogicalOp) (mask before after : Word) :
    Option OS.Atomics64.Event :=
  some ⟨actor,⟨handle⟩,⟨0⟩,⟨op,mask,⟨65536,before,after⟩⟩⟩

def expectedABC : Observed :=
  ⟨some 0x8000000000000000,
    [some 0,some 0,some 0,some 0,some 0,some 0,some 0,some 0x80],
    some 0x0123456789abcdef,some 0x8000000000000000,
    [event 1 0 .band 0x7fffffffffffffff 0x8000000000000001 1,
      event 2 1 .bor 0x8000000000000000 1 0x8000000000000001,
      event 3 2 .bxor 1 0x8000000000000001 0x8000000000000000,none,none,none],
    [expectedContext 0x7fffffffffffffff 32776 8192 0x602,
      expectedContext 0x8000000000000000 32792 12288 0x682,
      expectedContext 1 32808 16384 0x686]⟩

def expectedBAC : Observed :=
  ⟨some 0,[some 0,some 0,some 0,some 0,some 0,some 0,some 0,some 0],
    some 0x0123456789abcdef,some 0,
    [event 2 1 .bor 0x8000000000000000 0x8000000000000001 0x8000000000000001,
      event 1 0 .band 0x7fffffffffffffff 0x8000000000000001 1,
      event 3 2 .bxor 1 1 0,none,none,none],
    [expectedContext 0x7fffffffffffffff 32776 8192 0x602,
      expectedContext 0x8000000000000000 32792 12288 0x682,
      expectedContext 1 32808 16384 0x646]⟩

def agreesWith [DecidableEq α] (actual : Except TFault α) (expected : α) : Bool :=
  match actual with
  | .error _ => false
  | .ok observed => decide (observed = expected)

-- Two orderings have different independent full64 answers. Each worker reads
-- current peer RAM, including the unchanged OR event in the second ordering.
#eval do
  unless agreesWith (noncommuting [(0,false),(1,false),(2,false),(0,true),(1,true),(2,true)]) expectedABC do
    throw (IO.userError "AND/OR/XOR schedule lost current full64 data, events, frame or flags")
  unless agreesWith (noncommuting [(1,false),(0,false),(2,false),(0,true),(1,true),(2,true)]) expectedBAC do
    throw (IO.userError "OR/AND/XOR schedule commuted operations or erased unchanged RMW")
  IO.println "mixed full64 checked dispatch/RET/join order and frame checks passed"

def mixedBody (order : List (Nat × Bool)) (peerMask : Word) : Except TFault Observed := do
  let (initial, a, b, c, _) ← setup
    [0xf0,0x48,0x09,0x37,0xf0,0x48,0x31,0x37,0xf0,0x48,0x31,0x37,0xc3]
    [0xf0,0x48,0x09,0x37,0xc3] [0xc3] 0 1 peerMask 0
  let (one, _) ← spawn initial 0 a
  let (two, _) ← spawn one 0 b
  let (three, _) ← spawn two 0 c
  let (done, events) ← drive three order
  collectThree done events

-- A's OR/XOR/XOR implements uninterrupted union. Inserting B's OR between
-- the XORs gives zero. No ordering of two abstract union calls gives zero.
-- This tests actual managed events, not an asserted compound-call theorem.
def expectedMixedPeer : Observed :=
  ⟨some 0,[some 0,some 0,some 0,some 0,some 0,some 0,some 0,some 0],
    some 0x0123456789abcdef,some 0,
    [event 1 0 .bor 1 0 1,event 1 0 .bxor 1 1 0,event 2 1 .bor 1 0 1,
      event 1 0 .bxor 1 1 0,none,none,none],
    [expectedContext 1 32776 8192 0x646,
      expectedContext 1 32792 12288 0x602,
      expectedContext 0 32808 16384 0xed7]⟩

def expectedPeerAfterReturn : Observed :=
  ⟨some 3,[some 3,some 0,some 0,some 0,some 0,some 0,some 0,some 0],
    some 0x0123456789abcdef,some 3,
    [event 1 0 .bor 1 0 1,event 1 0 .bxor 1 1 0,event 1 0 .bxor 1 0 1,
      none,event 2 1 .bor 2 1 3,none,none],
    [expectedContext 1 32776 8192 0x602,
      expectedContext 2 32792 12288 0x606,
      expectedContext 0 32808 16384 0xed7]⟩

#eval do
  unless agreesWith (mixedBody [(0,false),(0,false),(1,false),(0,false),(0,true),(1,true),(2,false)] 1)
      expectedMixedPeer do
    throw (IO.userError "peer between XORs was erased or compound-call union assumed")
  unless agreesWith (mixedBody [(0,false),(0,false),(0,false),(0,true),(1,false),(1,true),(2,false)] 2)
      expectedPeerAfterReturn do
    throw (IO.userError "join restored completed-worker RAM or RET changed flags")
  IO.println "mixed body interference, RET-only worker and current join RAM checks passed"

def failureIs {α : Type} (operation : Except TFault α) (expected : TFault) : Bool :=
  match operation with
  | .error actual => decide (actual = expected)
  | .ok _ => false

/-- The second borrow fails after the first was acquired internally. The retry
then executes with original fresh thread/handle/loan identities. Code and stack
remain pinned through completion; the whole allocation remains reserved after
join until explicit retirement. -/
def lifecycle : Except TFault (List Bool × List (Option OS.Atomics64.Event) × Option Word) := do
  let (initial, a, _, _, dataTicket) ← setup
    [0xf0,0x48,0x31,0x37,0xc3] [0xc3] [0xc3] 0x8000000000000001 1 0 0
  let unavailable := failureIs (spawn initial 0 a false) .creationFailed
  let wrongParent := failureIs (spawn initial 5 a) .wrongParent
  let badSecondBorrow := failureIs (spawn initial 0 { a with stackTicket := ⟨99,0⟩ })
    (.atomic (.legacy (.authority (.ownership .missingAllocation))))
  let (started, identifier) ← spawn initial 0 a
  let some worker := started.workers identifier | throw .missingThread
  let identities := identifier == 0 && worker.handle.index == 0 && worker.codeLoan == 0 && worker.stackLoan == 1
  let early := failureIs (join started 0 identifier) .notCompleted
  let (updated, first) ← dispatch started identifier false
  let (done, last) ← dispatch updated identifier true
  let repeated := failureIs (dispatch done identifier false) .alreadyCompleted
  let codePinned := failureIs (mutate done (.protect 0 a.codeTicket readOnly))
    (.atomic (.legacy (.authority .borrowed)))
  let stackPinned := failureIs (mutate done (.release 0 a.stackTicket))
    (.atomic (.legacy (.authority .borrowed)))
  let handlePinned := failureIs (retire done 0 a.cell) (.atomic .liveHandles)
  let (joined, _) ← join done 0 identifier
  let stale := failureIs (dispatch joined identifier false) .missingThread
  let reserved := failureIs (mutate joined (.store64 0 dataTicket 65544 0)) (.atomic .reserved)
  let retired ← retire joined 0 a.cell
  let (changed, _) ← mutate retired (.store64 0 dataTicket 65544 0xfedcba9876543210)
  return ([unavailable,wrongParent,badSecondBorrow,identities,early,repeated,
    codePinned,stackPinned,handlePinned,stale,reserved], [first,last],
    (loadQWord (toMemory changed.shared.legacy.shared.resources.space) 65544).toOption)

#eval do
  unless agreesWith lifecycle
      ([true,true,true,true,true,true,true,true,true,true,true],
       [event 1 0 .bxor 1 0x8000000000000001 0x8000000000000000,none],
       some 0xfedcba9876543210) do
    throw (IO.userError "transactional creation, pinned completion or explicit retirement regressed")
  IO.println "checked lifecycle failure, authority and retirement checks passed"

/-- B writes before A's RET, remains unfinished when A is collected, and
successfully writes again after collection. Closing A must not revoke B or
restore A's captured value. A shared code allocation remains pinned by B. -/
def joinWithPeerRunning :
    Except TFault (List Bool × Option Word × Option Word × List (Option OS.Atomics64.Event)) := do
  let (initial, a, b, _, _) ← setup
    [0xf0,0x48,0x21,0x37,0xc3]
    [0xf0,0x48,0x31,0x37,0xf0,0x48,0x31,0x37,0xc3] [0xc3]
    0x8000000000000001 0x7fffffffffffffff 0x8000000000000000 0
  let (one, _) ← spawn initial 0 a
  let (two, _) ← spawn one 0 b
  let (afterA, ea) ← dispatch two 0 false
  let (afterB, eb) ← dispatch afterA 1 false
  let (returnedA, ra) ← dispatch afterB 0 true
  let (joinedA, _) ← join returnedA 0 0
  let atJoin := currentWord joinedA
  let some peer := joinedA.workers 1 | throw .missingThread
  let running := decide (peer.phase = .running)
  let closed := match OS.Atomics64.logicalUpdate .bor joinedA.shared 1 ⟨0⟩ 1 with
    | .error .missingHandle => true
    | _ => false
  let peerPinsCode := failureIs (mutate joinedA (.protect 0 a.codeTicket readOnly))
    (.atomic (.legacy (.authority .borrowed)))
  let (updatedB, eb2) ← dispatch joinedA 1 false
  let (returnedB, rb) ← dispatch updatedB 1 true
  let (joinedB, _) ← join returnedB 0 1
  let (unprotected, _) ← mutate joinedB (.protect 0 a.codeTicket readOnly)
  return ([running,closed,peerPinsCode],atJoin,currentWord unprotected,[ea,eb,ra,eb2,rb])

#eval do
  unless agreesWith joinWithPeerRunning
      ([true,true,true],some 0x8000000000000001,some 1,
        [event 1 0 .band 0x7fffffffffffffff 0x8000000000000001 1,
          event 2 1 .bxor 0x8000000000000000 1 0x8000000000000001,none,
          event 2 1 .bxor 0x8000000000000000 0x8000000000000001 1,none]) do
    throw (IO.userError "join lost peer RAM, revoked peer authority or released peer code")
  IO.println "join during unfinished peer execution retains current RAM and peer authority"

end EDSL.Tests.AtomicSetThreads64

#audit_edsl
