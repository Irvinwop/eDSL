/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO.CounterCheck
import EDSL.Audit

namespace EDSL.Tests.TSOCounter
open X86 OS OS.TSO

/- Synthetic model fixture, not certification of a compiled corpus artifact.
   Each worker buffers a disjoint publication, then executes four decoded
   32-bit LOCK XADD operations. LOOP uses RCX and returns to MOV EAX, 1. -/
def bytes : List Byte :=
  [0xb8, 1, 0, 0, 0, 0x89, 0x06, 0xb8, 1, 0, 0, 0,
   0xf0, 0x0f, 0xc1, 0x07, 0xe2, 0xf5, 0xc3]

def memory (old : BitVec 32) : X86.Memory where
  read address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4115 then bytes[address.toNat - 4096]?
    else if address.toNat = 32769 ∨ address.toNat = 36865 then some 0x20
    else if (32768 ≤ address.toNat ∧ address.toNat < 32776) ∨
        (36864 ≤ address.toNat ∧ address.toNat < 36872) then some 0
    else if address.toNat = 65536 then some (old.extractLsb' 0 8)
    else if address.toNat = 65537 then some (old.extractLsb' 8 8)
    else if address.toNat = 65538 then some (old.extractLsb' 16 8)
    else if address.toNat = 65539 then some (old.extractLsb' 24 8)
    else if 65540 ≤ address.toNat ∧ address.toNat < 65552 then some 0xa5
    else none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4115)
  writable address := decide (65536 ≤ address.toNat ∧ address.toNat < 65548)

def context (publication stack : Word) : Threads.Context where
  registers register := if register = .rdi then 65536
    else if register = .rsi then publication else if register = .rsp then stack
    else if register = .rcx then 4 else 0xfeedface89abcdef
  rip := 4096
  flags := 0x8d7

def initial (old : BitVec 32) : OS.TSO.State :=
  ⟨memory old, [⟨context 65540 32768, false, []⟩, ⟨context 65544 36864, false, []⟩]⟩

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

def startActions : List Action := [.issue 0, .issue 1, .issue 0, .issue 1, .issue 0, .issue 1]

def paused : OS.TSO.State × List Observation := checked (schedule (initial 0) startActions) (by rfl)

theorem paused_schedule : schedule (initial 0) startActions = .ok paused := checked_ok _ _

-- Both stores retired into their own queues; physical RAM still has the
-- nonzero publication sentinel. The counter has not yet been touched.
example : loadDWord paused.1.memory 65536 = .ok 0 ∧
    loadDWord paused.1.memory 65540 = .ok 0xa5a5a5a5 ∧
    loadDWord paused.1.memory 65544 = .ok 0xa5a5a5a5 ∧
    paused.1.workers.map (fun worker =>
      (worker.context.rip, worker.buffer.map (fun store => (store.address, store.value)))) =
      [(4108, [(65540, 1)]), (4108, [(65544, 1)])] := ⟨rfl, rfl, rfl, rfl⟩

-- Blocking leaves the entire state intact, emits no atomic event, and does
-- not retire an instruction. Repeated attempts cannot bypass the local FIFO.
example : schedule paused.1 [.issue 0, .issue 1, .issue 0] =
    .ok (paused.1, [.blocked 0, .blocked 1, .blocked 0]) := by rfl

def localBarrierActions : List Action :=
  startActions ++ [.issue 0, .issue 1, .drain 0, .issue 0, .issue 1, .drain 1]

def localBarrier : OS.TSO.State × List Observation :=
  checked (schedule (initial 0) localBarrierActions) (by rfl)

-- The peer still has a pending write when worker zero's XADD succeeds.
def peerPending : OS.TSO.State × List Observation :=
  checked (schedule paused.1 [.drain 0, .issue 0, .issue 1]) (by rfl)

example : peerPending.2 =
      [.drained 0 ⟨65540, 1⟩, .retired 0 (some ⟨65536, 0, 1⟩), .blocked 1] ∧
    loadDWord peerPending.1.memory 65536 = .ok 1 ∧
    loadDWord peerPending.1.memory 65540 = .ok 1 ∧
    loadDWord peerPending.1.memory 65544 = .ok 0xa5a5a5a5 ∧
    peerPending.1.workers.map (fun worker => worker.buffer.length) = [0, 1] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def round (identifier : Nat) : List Action := [.issue identifier, .issue identifier, .issue identifier]

-- Each round starts immediately after the worker's preceding XADD:
-- LOOP; MOV EAX, 1; LOCK XADD. The final LOOP falls through to RET.
def finish : List Action := [.issue 0, .issue 1, .issue 0, .issue 1]

def alternating : List Action := localBarrierActions ++ [.issue 1] ++
  round 0 ++ round 1 ++ round 0 ++ round 1 ++ round 0 ++ round 1 ++ finish

def clustered : List Action := localBarrierActions ++ [.issue 1] ++
  round 1 ++ round 0 ++ round 0 ++ round 1 ++ round 1 ++ round 0 ++ finish

def alternatingRun : OS.TSO.State × List Observation :=
  checked (schedule (initial 0) alternating) (by rfl)

def clusteredRun : OS.TSO.State × List Observation :=
  checked (schedule (initial 0) clustered) (by rfl)

def wraparoundRun : OS.TSO.State × List Observation :=
  checked (schedule (initial 0xfffffffc) alternating) (by rfl)

theorem alternating_schedule : schedule (initial 0) alternating = .ok alternatingRun := checked_ok _ _
theorem clustered_schedule : schedule (initial 0) clustered = .ok clusteredRun := checked_ok _ _
theorem wraparound_schedule : schedule (initial 0xfffffffc) alternating = .ok wraparoundRun := checked_ok _ _

-- Independent finite-request outcomes: eight increments, with every returned
-- old value in global retirement order. Thread ownership changes with the
-- schedule; no worker gets the same old value as another worker.
theorem alternating_events : atomicEvents alternatingRun.2 =
    [(0, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 2⟩), (0, ⟨65536, 2, 3⟩), (1, ⟨65536, 3, 4⟩),
     (0, ⟨65536, 4, 5⟩), (1, ⟨65536, 5, 6⟩), (0, ⟨65536, 6, 7⟩), (1, ⟨65536, 7, 8⟩)] := by rfl

theorem clustered_events : atomicEvents clusteredRun.2 =
    [(0, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 2⟩), (1, ⟨65536, 2, 3⟩), (0, ⟨65536, 3, 4⟩),
     (0, ⟨65536, 4, 5⟩), (1, ⟨65536, 5, 6⟩), (1, ⟨65536, 6, 7⟩), (0, ⟨65536, 7, 8⟩)] := by rfl

theorem wraparound_events : atomicEvents wraparoundRun.2 =
    [(0, ⟨65536, 0xfffffffc, 0xfffffffd⟩), (1, ⟨65536, 0xfffffffd, 0xfffffffe⟩),
     (0, ⟨65536, 0xfffffffe, 0xffffffff⟩), (1, ⟨65536, 0xffffffff, 0⟩),
     (0, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 2⟩), (0, ⟨65536, 2, 3⟩), (1, ⟨65536, 3, 4⟩)] := by rfl

-- RAM, real per-worker RAX, RCX exhaustion, separate saved return stacks,
-- FIFO publication and a byte sentinel beyond all three dwords are checked.
theorem alternating_outcome : loadDWord alternatingRun.1.memory 65536 = .ok 8 ∧
    loadDWord alternatingRun.1.memory 65540 = .ok 1 ∧
    loadDWord alternatingRun.1.memory 65544 = .ok 1 ∧
    loadDWord alternatingRun.1.memory 65548 = .ok 0xa5a5a5a5 ∧
    alternatingRun.1.workers.map (fun worker =>
      (worker.context.registers .rax, worker.context.registers .rcx,
       worker.context.registers .rsp, worker.context.rip, worker.returned, worker.buffer.length)) =
      [(6, 0, 32776, 8192, true, 0), (7, 0, 36872, 8192, true, 0)] := ⟨rfl, rfl, rfl, rfl, rfl⟩

example : loadDWord clusteredRun.1.memory 65536 = .ok 8 ∧
    clusteredRun.1.workers.map (fun worker => worker.context.registers .rax) = [7, 6] ∧
    loadDWord wraparoundRun.1.memory 65536 = .ok 4 ∧
    wraparoundRun.1.workers.map (fun worker => worker.context.registers .rax) = [2, 3] :=
  ⟨rfl, rfl, rfl, rfl⟩

example : retiredCount alternatingRun.2 = 30 ∧ alternatingRun.2.length = 35 ∧
    alternatingRun.2.filterMap (fun observation => match observation with
      | .blocked identifier => some identifier | _ => none) = [0, 1, 1] := ⟨rfl, rfl, rfl⟩

private theorem event_injective (address : Word) :
    ∀ left right : Counter.Operation,
      left.event address = right.event address → left = right := by
  rintro ⟨leftThread, leftDelta, leftResult⟩ ⟨rightThread, rightDelta, rightResult⟩ same
  have threadEq : leftThread = rightThread := congrArg Prod.fst same
  have resultEq : leftResult = rightResult := congrArg (fun entry => entry.2.before) same
  have sumEq : leftResult + leftDelta = rightResult + rightDelta :=
    congrArg (fun entry => entry.2.after) same
  have deltaEq : leftDelta = rightDelta := by
    rw [resultEq] at sumEq
    exact (BitVec.add_right_inj rightResult).mp sumEq
  cases threadEq
  cases deltaEq
  cases resultEq
  rfl

-- Identify the independently supplied history only after obtaining real
-- decoded origins from schedule_linearization. Event injectivity does not
-- define or guess those origins; their deltas come from actual pre-step RAX.
private theorem exact_linearization {address : Word} {before : OS.TSO.State}
    {actions : List Action} {result : OS.TSO.State × List Observation}
    {old : BitVec 32} {operations : List Counter.Operation}
    (read : loadDWord before.memory address = .ok old)
    (checked : Counter.checkSchedule address before actions = true)
    (success : schedule before actions = .ok result)
    (expected : operations.map (Counter.Operation.event address) = Counter.eventsAt address result.2) :
    loadDWord result.1.memory address = .ok (old + Counter.totalDelta operations) ∧
    Counter.Sequential old operations (old + Counter.totalDelta operations) ∧
    Counter.MachineHistory address before actions result.2 result.1 operations := by
  obtain ⟨observed, final, actual, scheduled, ram, sequential, history, events, total⟩ :=
    Counter.checked_linearization read checked
  have sameResult : observed = result := Except.ok.inj (scheduled.symm.trans success)
  subst observed
  have identified : actual = operations :=
    (List.map_inj_right (event_injective address)).mp (events.trans expected.symm)
  subst actual
  rw [total] at ram sequential
  exact ⟨ram, sequential, history⟩

-- Eight independently requested additions of one, with expected old words.
def alternatingOperations : List Counter.Operation :=
  [⟨0, 1, 0⟩, ⟨1, 1, 1⟩, ⟨0, 1, 2⟩, ⟨1, 1, 3⟩,
   ⟨0, 1, 4⟩, ⟨1, 1, 5⟩, ⟨0, 1, 6⟩, ⟨1, 1, 7⟩]

def clusteredOperations : List Counter.Operation :=
  [⟨0, 1, 0⟩, ⟨1, 1, 1⟩, ⟨1, 1, 2⟩, ⟨0, 1, 3⟩,
   ⟨0, 1, 4⟩, ⟨1, 1, 5⟩, ⟨1, 1, 6⟩, ⟨0, 1, 7⟩]

def wraparoundOperations : List Counter.Operation :=
  [⟨0, 1, 0xfffffffc⟩, ⟨1, 1, 0xfffffffd⟩, ⟨0, 1, 0xfffffffe⟩, ⟨1, 1, 0xffffffff⟩,
   ⟨0, 1, 0⟩, ⟨1, 1, 1⟩, ⟨0, 1, 2⟩, ⟨1, 1, 3⟩]

theorem alternating_checked : Counter.checkSchedule 65536 (initial 0) alternating = true := by rfl

theorem clustered_checked : Counter.checkSchedule 65536 (initial 0) clustered = true := by rfl

theorem wraparound_checked : Counter.checkSchedule 65536 (initial 0xfffffffc) alternating = true := by rfl

theorem alternating_linearization :
    Counter.Sequential 0 alternatingOperations 8 ∧
    Counter.MachineHistory 65536 (initial 0) alternating alternatingRun.2 alternatingRun.1
      alternatingOperations ∧ loadDWord alternatingRun.1.memory 65536 = .ok 8 := by
  have lifted := exact_linearization (old := 0) (by rfl) alternating_checked alternating_schedule
    (show alternatingOperations.map (Counter.Operation.event 65536) =
      Counter.eventsAt 65536 alternatingRun.2 from rfl)
  exact ⟨lifted.2.1, lifted.2.2, lifted.1⟩

theorem clustered_linearization :
    Counter.Sequential 0 clusteredOperations 8 ∧
    Counter.MachineHistory 65536 (initial 0) clustered clusteredRun.2 clusteredRun.1
      clusteredOperations ∧ loadDWord clusteredRun.1.memory 65536 = .ok 8 := by
  have lifted := exact_linearization (old := 0) (by rfl) clustered_checked clustered_schedule
    (show clusteredOperations.map (Counter.Operation.event 65536) =
      Counter.eventsAt 65536 clusteredRun.2 from rfl)
  exact ⟨lifted.2.1, lifted.2.2, lifted.1⟩

theorem wraparound_linearization :
    Counter.Sequential 0xfffffffc wraparoundOperations 4 ∧
    Counter.MachineHistory 65536 (initial 0xfffffffc) alternating wraparoundRun.2 wraparoundRun.1
      wraparoundOperations ∧ loadDWord wraparoundRun.1.memory 65536 = .ok 4 := by
  have lifted := exact_linearization (old := 0xfffffffc) (by rfl) wraparound_checked wraparound_schedule
    (show wraparoundOperations.map (Counter.Operation.event 65536) =
      Counter.eventsAt 65536 wraparoundRun.2 from rfl)
  exact ⟨lifted.2.1, lifted.2.2, lifted.1⟩

-- An ordinary store may retire into a local FIFO even when it targets the
-- counter. Its later publication must be excluded by the counter policy.
def interfering : OS.TSO.State :=
  { initial 0 with workers := [⟨context 65536 32768, false, []⟩] }

def interferingRun : OS.TSO.State × List Observation :=
  checked (schedule interfering [.issue 0, .issue 0, .drain 0]) (by rfl)

example : Counter.checkSchedule 65536 interfering [.issue 0, .issue 0, .drain 0] = false ∧
    loadDWord interferingRun.1.memory 65536 = .ok 1 ∧ atomicEvents interferingRun.2 = [] :=
  ⟨rfl, rfl, rfl⟩

-- The theorem accepts arbitrary entry states, not only empty-buffer states.
-- An externally supplied unaligned FIFO head overlaps three counter bytes.
-- Actual drain succeeds, so checking starting-address inequality would admit
-- this counter mutation. This is not claimed reachable from the fixture.
def partiallyOverlapping : OS.TSO.State :=
  { initial 0 with workers := [⟨context 65540 32768, false, [⟨65537, 1⟩]⟩] }

def partialRun : OS.TSO.State × List Observation :=
  checked (schedule partiallyOverlapping [.drain 0]) (by rfl)

example : Counter.checkSchedule 65536 partiallyOverlapping [.drain 0] = false ∧
    loadDWord partialRun.1.memory 65536 = .ok 256 := ⟨rfl, rfl⟩

-- XCHG at zero with source one has the same first event as fetch-add one.
-- The counter certificate must still reject its actual decoded instruction.
def exchangeInitial : OS.TSO.State :=
  { initial 0 with
    memory := { memory 0 with
      read := fun address =>
        if address = 4096 then some 0x87 else if address = 4097 then some 0x07
        else (memory 0).read address }
    workers := [⟨{ context 65540 32768 with
      registers := fun register =>
        if register = .rax then 1 else (context 65540 32768).registers register }, false, []⟩] }

def exchangeRun : OS.TSO.State × List Observation :=
  checked (schedule exchangeInitial [.issue 0]) (by rfl)

example : Counter.checkSchedule 65536 exchangeInitial [.issue 0] = false ∧
    atomicEvents exchangeRun.2 = [(0, ⟨65536, 0, 1⟩)] := ⟨rfl, rfl⟩

def malformed : OS.TSO.State :=
  { initial 0 with memory := { memory 0 with
      read := fun address => if address = 4096 then some 0xff else (memory 0).read address } }

example : schedule malformed [.issue 0] = .error (.machine (.unsupportedOpcode 0xff)) ∧
    Counter.checkSchedule 65536 malformed [.issue 0] = false := ⟨rfl, rfl⟩

-- The instruction decodes, but its store lacks permission on its last byte.
-- Successful policy classification alone cannot certify actual scheduling.
def denied : OS.TSO.State :=
  { initial 0 with memory := { memory 0 with
      writable := fun address => decide (address ≠ 65543) && (memory 0).writable address } }

example : schedule denied [.issue 0, .issue 0] = .error (.machine (.writeDenied 65540)) ∧
    Counter.checkSchedule 65536 denied [.issue 0, .issue 0] = false := ⟨rfl, rfl⟩

end EDSL.Tests.TSOCounter

#audit_edsl
