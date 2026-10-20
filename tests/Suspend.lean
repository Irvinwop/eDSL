/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Suspend
import EDSL.Audit

namespace EDSL.Tests.Suspend
open X86 OS
open Examples.Suspend

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

abbrev replacement : BitVec 32 := 0x11223344
abbrev raw : Word := 0xfedcba9876543210
abbrev flags : Word := 0x0123456789abcdef
abbrev rcx : Word := 0x0badf00d12345678
abbrev r11 : Word := 0x8877665544332211

def afterReturn := returned replacement raw flags rcx r11

def registerOrder : List Register :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
    .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

def callerView (state : OS.Suspend.State) :
    Option (List Word × Word × Word × Bool × Nat) :=
  state.machine.workers[0]?.map fun worker =>
    (registerOrder.map worker.context.registers, worker.context.rip,
      worker.context.flags, worker.returned, worker.buffer.length)

def peerView (state : OS.Suspend.State) :
    Option (Word × Word × Word × Word × Word × Word × Bool × Nat) :=
  state.machine.workers[1]?.map fun worker =>
    (worker.context.registers .rax, worker.context.registers .rdi,
      worker.context.registers .r12, worker.context.registers .rsp,
      worker.context.rip, worker.context.flags, worker.returned, worker.buffer.length)

def requestView (state : OS.Suspend.State) :
    Option (Nat × Nat × Word × BitVec 32 × List Word × Word × Word × Word ×
      Option (BitVec 32)) :=
  (state.pending 0).map fun saved =>
    (saved.identifier, saved.worker, saved.request.user.registers .rax,
      saved.request.number,
      [.first, .second, .third, .fourth, .fifth, .sixth].map saved.request.argument,
      saved.request.user.rip, saved.request.continuation, saved.request.user.flags,
      (loadDWord saved.request.user.memory 65536).toOption)

-- The request comes from actual execution of 0F 05, including a dispatch
-- number outside the modeled service subsets and all six full-width arguments.
example : (OS.Suspend.schedule (initial replacement) [.issue 0, .issue 1]).map
    (fun result => requestView result.1) = .ok (some
    (0, 0, 0xdeadbeef76543210, 0x76543210,
      [65536, 0x0123456789abcdef, 0x23456789abcdef01, 0x3456789abcdef0123,
        0x456789abcdef01234, 0x56789abcdef012345],
      4096, 4098, 0x8d7, some 0x98badcfe)) := by
  rw [peerPrefix_ok]
  rfl

-- Resumption chooses the continuation and the supplied full-width return
-- fields. Every other register is independently enumerated from the ABI
-- contract; the subsequent actual RET changes only RSP and RIP.
example : (OS.Suspend.resume (exchanged replacement).1 0 0 raw flags rcx r11).map callerView = .ok (some
    ([0xfedcba9876543210, 0x0badf00d12345678, 0x23456789abcdef01,
      0x6789abcdef0123456, 32768, 0x789abcdef01234567, 0x0123456789abcdef,
      65536, 0x456789abcdef01234, 0x56789abcdef012345, 0x3456789abcdef0123,
      0x8877665544332211, 0x89abcdef01234567, 0x9abcdef012345678,
      0xabcdef0123456789, 0xbcdef0123456789a], 4098, 0x0123456789abcdef,
      false, 0)) := by
  rw [resumed_ok]
  rfl

example : (OS.Suspend.schedule (initial replacement) (completionActions raw flags rcx r11)).map
    (fun result => callerView result.1) = .ok (some
    ([0xfedcba9876543210, 0x0badf00d12345678, 0x23456789abcdef01,
      0x6789abcdef0123456, 32776, 0x789abcdef01234567, 0x0123456789abcdef,
      65536, 0x456789abcdef01234, 0x56789abcdef012345, 0x3456789abcdef0123,
      0x8877665544332211, 0x89abcdef01234567, 0x9abcdef012345678,
      0xabcdef0123456789, 0xbcdef0123456789a], 12288, 0x0123456789abcdef,
      true, 0)) := by
  rw [completion_ok]
  rfl

-- The peer's changed data and post-XCHG private context must survive both
-- resumption and the caller's RET. Restoring the request's memory fails here.
example : (OS.Suspend.schedule (initial replacement) (completionActions raw flags rcx r11)).map
    (fun result => ((loadDWord result.1.machine.memory 65536).toOption,
      peerView result.1, [65535, 65536, 65537, 65538, 65539, 65540].map result.1.machine.memory.read)) =
      .ok (some 0x11223344,
        some (0x98badcfe, 65536, 0xcafef00d13579bdf, 32800, 8194, 0x246, false, 0),
        [some 0x5a, some 0x44, some 0x33, some 0x22, some 0x11, some 0xa5]) := by
  rw [completion_ok]
  rfl

def parked : OS.Suspend.State × OS.Suspend.Observation :=
  checked (OS.Suspend.issue (exchanged replacement).1 0) (by rfl)

-- Repeated selections cannot execute the stub again or run its RET while
-- pending. Only actual entry counts as a retired SYSCALL.
def actions : List OS.Suspend.Action :=
  [.issue 0, .issue 0, .issue 1, .issue 0,
    .resume 0 0 raw flags rcx r11, .issue 0, .issue 1]

def complete : OS.Suspend.State × List OS.Suspend.Observation :=
  checked (OS.Suspend.schedule (initial replacement) actions) (by rfl)

example : complete.2 =
    [.entered 0 0, .parked 0 0, .machine (.retired 1 (some ⟨65536, 0x98badcfe, 0x11223344⟩)),
      .parked 0 0, .resumed 0 0 0xfedcba9876543210,
      .machine (.retired 0 none), .machine (.retired 1 none)] ∧
    OS.Suspend.retiredCount complete.2 = 4 ∧
    OS.Suspend.atomicEvents complete.2 = [(1, ⟨65536, 0x98badcfe, 0x11223344⟩)] ∧
    complete.1.nextCall = 1 := ⟨rfl, rfl, rfl, rfl⟩

-- The generic theorem frames the whole state, avoiding function-valued
-- Worker comparison by kernel normalization.
example : parked.1 = (exchanged replacement).1 :=
  (OS.Suspend.issue_parked_effect
    (show OS.Suspend.issue (exchanged replacement).1 0 = .ok (parked.1, .parked 0 0) from
      checked_ok _ (by rfl))).1

-- A peer queues two different stores to the same word, then returns. The
-- caller's empty FIFO allows entry and completion while this peer FIFO stays
-- pending. Actual drain order distinguishes FIFO preservation from reversal.
def fifoBytes : List Byte := [0x89, 0x37, 0xbe, 0x88, 0x77, 0x66, 0x55, 0x89, 0x37, 0xc3]

def fifoInitial : OS.Suspend.State :=
  OS.Suspend.initial ⟨memory callerBytes fifoBytes,
    [⟨callerContext, false, []⟩,
      ⟨{ peerContext 0 with registers := fun register =>
          if register = .rsi then 0xabcdef0011223344 else (peerContext 0).registers register },
        false, []⟩]⟩

def fifoQueued : OS.Suspend.State × List OS.Suspend.Observation :=
  checked (OS.Suspend.schedule fifoInitial [.issue 1, .issue 1, .issue 1, .issue 1]) (by rfl)

def fifoEntered : OS.Suspend.State × OS.Suspend.Observation :=
  checked (OS.Suspend.issue fifoQueued.1 0) (by rfl)

def fifoResumed : OS.Suspend.State :=
  checked (OS.Suspend.resume fifoEntered.1 0 0 raw flags rcx r11) (by rfl)

example : fifoResumed.machine.memory = fifoEntered.1.machine.memory ∧
    fifoResumed.machine.workers[1]? = fifoEntered.1.machine.workers[1]? :=
  ⟨OS.Suspend.resume_memory (checked_ok _ _), OS.Suspend.resume_peer (by decide) (checked_ok _ _)⟩

def fifoView (state : OS.Suspend.State) : Option (BitVec 32) ×
    Option (Word × Word × Word × Bool × List X86.StoreBuffer.Store) :=
  ((loadDWord state.machine.memory 65536).toOption,
    state.machine.workers[1]?.map fun worker =>
      (worker.context.registers .rsp, worker.context.rip, worker.context.flags,
        worker.returned, worker.buffer))

example : fifoView fifoResumed = (some 0x98badcfe,
    some (32808, 16384, 0x246, true, [⟨65536, 0x11223344⟩, ⟨65536, 0x55667788⟩])) := by rfl

def drainAfter : OS.Suspend.State × List OS.Suspend.Observation :=
  checked (OS.Suspend.schedule fifoResumed [.drain 1, .drain 1, .issue 0]) (by rfl)

def drainBefore : OS.Suspend.State × OS.Suspend.Observation :=
  checked (OS.Suspend.drain fifoEntered.1 1) (by rfl)

def resumeAfterDrain : OS.Suspend.State :=
  checked (OS.Suspend.resume drainBefore.1 0 0 raw flags rcx r11) (by rfl)

example : resumeAfterDrain.machine.memory = drainBefore.1.machine.memory ∧
    resumeAfterDrain.machine.workers[1]? = drainBefore.1.machine.workers[1]? :=
  ⟨OS.Suspend.resume_memory (checked_ok _ _), OS.Suspend.resume_peer (by decide) (checked_ok _ _)⟩

def remainingDrain : OS.Suspend.State × List OS.Suspend.Observation :=
  checked (OS.Suspend.schedule resumeAfterDrain [.issue 0, .drain 1]) (by rfl)

example : fifoView resumeAfterDrain = (some 0x11223344,
    some (32808, 16384, 0x246, true, [⟨65536, 0x55667788⟩])) ∧
    fifoView drainAfter.1 = (some 0x55667788, some (32808, 16384, 0x246, true, [])) ∧
    fifoView remainingDrain.1 = (some 0x55667788, some (32808, 16384, 0x246, true, [])) ∧
    OS.Suspend.retiredCount drainAfter.2 = 1 ∧
    OS.Suspend.retiredCount remainingDrain.2 = 1 := ⟨rfl, rfl, rfl, rfl, rfl⟩

-- A real store by the caller cannot be silently flushed at SYSCALL. The
-- explicit drain publishes it without retiring or advancing the instruction.
def ownStoreInitial : OS.Suspend.State :=
  { initial replacement with machine :=
      ⟨memory [0x89, 0x37, 0x0f, 0x05, 0xc3] exchangeBytes,
        (initial replacement).machine.workers⟩ }

def ownQueued : OS.Suspend.State × OS.Suspend.Observation :=
  checked (OS.Suspend.issue ownStoreInitial 0) (by rfl)

example : OS.Suspend.issue ownQueued.1 0 = .error .pendingStores := by rfl

def ownDrained : OS.Suspend.State × OS.Suspend.Observation :=
  checked (OS.Suspend.drain ownQueued.1 0) (by rfl)

def ownEntered : OS.Suspend.State × OS.Suspend.Observation :=
  checked (OS.Suspend.issue ownDrained.1 0) (by rfl)

example : (loadDWord ownQueued.1.machine.memory 65536).toOption = some 0x98badcfe ∧
    (loadDWord ownDrained.1.machine.memory 65536).toOption = some 0x89abcdef ∧
    ownEntered.2 = .entered 0 0 ∧
    (ownEntered.1.pending 0).map (fun saved => (saved.request.user.rip, saved.request.continuation)) =
      some (4098, 4100) ∧
    OS.Suspend.retiredCount [ownQueued.2, ownDrained.2, ownEntered.2] = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Faults originate from fetching the second syscall byte, before request
-- capture. Both mapped-but-nonexecutable and absent bytes stay architectural.
def badSecondByte (unmapped : Bool) : OS.Suspend.State :=
  let state := initial replacement
  { state with machine := { state.machine with memory := { state.machine.memory with
      read := fun address => if unmapped && address == 4097 then none
        else state.machine.memory.read address
      executable := fun address => if !unmapped && address == 4097 then false
        else state.machine.memory.executable address } } }

example : OS.Suspend.issue (badSecondByte true) 0 =
    .error (.underlying (.machine (.inaccessibleInstruction 4097))) := by rfl
example : OS.Suspend.issue (badSecondByte false) 0 =
    .error (.underlying (.machine (.inaccessibleInstruction 4097))) := by rfl

-- Completion consumes the pending invocation. The same ID is rejected even
-- before RET; returned and nonexistent workers retain their underlying errors.
example : OS.Suspend.resume (initial replacement) 0 0 raw flags rcx r11 = .error .noPending := by rfl
example : OS.Suspend.resume (exchanged replacement).1 0 1 raw flags rcx r11 = .error .staleCall := by rfl
example : OS.Suspend.resume (resumed replacement raw flags rcx r11) 0 0 raw flags rcx r11 =
    .error .noPending := by rfl
example : OS.Suspend.resume afterReturn.1 0 0 raw flags rcx r11 =
    .error (.underlying .alreadyReturned) := by rfl
example : OS.Suspend.issue afterReturn.1 0 = .error (.underlying .alreadyReturned) := by rfl
example : OS.Suspend.issue (initial replacement) 2 = .error (.underlying .missingThread) := by rfl
example : OS.Suspend.resume (exchanged replacement).1 2 0 raw flags rcx r11 =
    .error (.underlying .missingThread) := by rfl

-- A second actual SYSCALL receives a fresh invocation. A delayed completion
-- for the consumed first invocation cannot complete the newer request.
def twiceInitial : OS.Suspend.State :=
  { initial replacement with machine :=
      { (initial replacement).machine with
        memory := memory [0x0f, 0x05, 0x0f, 0x05, 0xc3] exchangeBytes } }

def twiceEntered : OS.Suspend.State × List OS.Suspend.Observation :=
  checked (OS.Suspend.schedule twiceInitial
    [.issue 0, .resume 0 0 raw flags rcx r11, .issue 0]) (by rfl)

example : twiceEntered.2 = [.entered 0 0, .resumed 0 0 0xfedcba9876543210, .entered 0 1] ∧
    twiceEntered.1.nextCall = 2 ∧
    OS.Suspend.resume twiceEntered.1 0 0 raw flags rcx r11 = .error .staleCall := ⟨rfl, rfl, rfl⟩

-- Raw states are public: malformed ownership or a caller FIFO are explicit
-- errors even if supplied directly, rather than produced by a valid trace.
def wrongOwner : OS.Suspend.State :=
  { (entered replacement).1 with pending := fun query =>
      ((entered replacement).1.pending query).map fun saved => { saved with worker := 1 } }

def pendingWithQueue : OS.Suspend.State :=
  { (entered replacement).1 with machine :=
      { (entered replacement).1.machine with workers :=
        [⟨callerContext, false, [⟨65536, 0x11223344⟩]⟩, ⟨peerContext replacement, false, []⟩] } }

example : OS.Suspend.resume wrongOwner 0 0 raw flags rcx r11 = .error .wrongWorker := by rfl
example : OS.Suspend.resume pendingWithQueue 0 0 raw flags rcx r11 = .error .pendingStores := by rfl

end EDSL.Tests.Suspend

#audit_edsl
