/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.History
import EDSL.OS.Futex.Runtime
import EDSL.Audit

namespace EDSL.Tests.FutexService
open X86 OS AddressSpace Futex

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Owned SYSCALL/RET and XCHG/RET clients. All service tests begin by actual
instruction decoding and syscall capture, with matching physical/resource RAM. -/
def space : Space where
  cells address :=
    if address.toNat = 4096 then some ⟨0x0f, readExecute⟩
    else if address.toNat = 4097 then some ⟨0x05, readExecute⟩
    else if address.toNat = 4098 then some ⟨0xc3, readExecute⟩
    else if address.toNat = 8192 then some ⟨0x87, readExecute⟩
    else if address.toNat = 8193 then some ⟨0x07, readExecute⟩
    else if address.toNat = 8194 then some ⟨0xc3, readExecute⟩
    else if 32768 ≤ address.toNat ∧ address.toNat < 32800 then
      some ⟨if address.toNat % 8 = 1 then 0x30 else 0, readOnly⟩
    else if 65536 ≤ address.toNat ∧ address.toNat < 65540 then some ⟨0, readWrite⟩
    else none

def context (worker : Nat) : Threads.Context where
  registers register :=
    if register = .rax then (if worker = 3 then 1 else 202)
    else if register = .rdi then 65536
    else if register = .rsi then (if worker = 2 then 129 else 128)
    else if register = .rdx then (if worker = 2 then 1 else 0)
    else if register = .rsp then 32768 + BitVec.ofNat 64 (8 * worker)
    else if register = .rbx then 0xabcdef0123456789
    else 0
  rip := if worker = 3 then 8192 else 4096
  flags := 0x246

def config : Config := ⟨0, 90, ⟨4096, 2^47⟩⟩

def profile : Physical.Profile :=
  ⟨config, fun _ => none, fun worker => if worker = 3 then some ⟨90, 0⟩ else none⟩

def initial : Except Atomics.Fault Futex.State := do
  let seed := Atomics.empty (Borrowing.empty (Ownership.empty space))
  let (adopted, ticket) ← Atomics.mutate seed (.adopt 7 ⟨65536, 4⟩)
  let some ticket := ticket | throw .missingHandle
  let (pinned, keeper) ← Atomics.issue adopted 7 ticket 90 65536
  return ⟨Suspend.initial ⟨toMemory pinned.shared.resources.space,
    (List.range 4).map fun worker => ⟨context worker, false, []⟩⟩,
    pinned, some ⟨7, ticket, 90, 65536, keeper⟩, fun _ => none, []⟩

def run (actions : List Runtime.Action) : Except Physical.Fault (Futex.State × List Runtime.Observation) := do
  let state ← initial.mapError Physical.Fault.resources
  Runtime.schedule profile state actions

def workerView (state : Futex.State) (worker : Nat) : Option (Word × Word × Word × Word × Word × Bool) :=
  state.suspended.machine.workers[worker]?.map fun selected =>
    (selected.context.registers .rax, selected.context.registers .rsp,
      selected.context.registers .rbx, selected.context.rip, selected.context.flags, selected.returned)

def readyRaw (state : Futex.State) (invocation : Nat) : Option Word := do
  let call ← state.calls invocation
  match call.phase with
  | .ready outcome _ => some outcome.raw
  | _ => none

-- Delayed comparison observes a real peer XCHG after entry; full -11, current
-- RAM, peer progress and all ABI-preserved sentinels survive resume and RET.
example : (run [.issue 0, .issue 3, .service (.compare 0),
    .service (.resume 0 0x1122334455667788 0x8877665544332211 0x123456789abcdef0), .issue 0]).map
      (fun result => (workerView result.1 0,
        (loadDWord result.1.suspended.machine.memory 65536).toOption,
        workerView result.1 3, result.1.queue, readyRaw result.1 0)) =
    .ok (some (0xfffffffffffffff5, 32776, 0xabcdef0123456789, 12288, 0x1122334455667788, true),
      some 1, some (0, 32792, 0xabcdef0123456789, 8194, 0x246, false), [], none) := by rfl

def twoWaiters (selected : Nat) : List Runtime.Action :=
  [.issue 0, .service (.compare 0), .issue 1, .service (.compare 1),
    .issue 2, .service (.wake 2 (some selected))]

-- Either queued ID may be chosen, independent of insertion order. Exactly
-- one waiter is ready, the other's pending call survives, and WAKE returns 1.
example : (run (twoWaiters 1)).map (fun result =>
    (readyRaw result.1 0, readyRaw result.1 1, readyRaw result.1 2, result.1.queue,
      (loadDWord result.1.suspended.machine.memory 65536).toOption)) =
    .ok (none, some 0, some 1, [0], some 0) := by rfl

example : (run (twoWaiters 0)).map (fun result =>
    (readyRaw result.1 0, readyRaw result.1 1, readyRaw result.1 2, result.1.queue)) =
    .ok (some 0, none, some 1, [1]) := by rfl

-- Retry cannot reuse its first equal observation after publication. It keeps
-- the invocation, reads again, returns EAGAIN and consumes the old pin once.
example : (run [.issue 0, .service (.compare 0), .service (.retry 0), .issue 3,
    .service (.compare 0), .service (.resume 0 0 0 0), .issue 0]).map
    (fun result => (workerView result.1 0, result.1.suspended.nextCall,
      result.1.queue, (Atomics.authorize result.1.authority 90 1).toOption.isNone)) =
    .ok (some (0xfffffffffffffff5, 32776, 0xabcdef0123456789, 12288, 0, true), 1, [], true) := by rfl

-- Empty wake has no credit: a later equal WAIT remains queued and repeated
-- selections park it rather than manufacturing a ready result.
example : (run [.issue 2, .service (.wake 0 none), .service (.resume 0 0 0 0), .issue 2,
    .issue 0, .service (.compare 1), .issue 0, .issue 0]).map
    (fun result => (workerView result.1 2, readyRaw result.1 1, result.1.queue,
      (loadDWord result.1.suspended.machine.memory 65536).toOption)) =
    .ok (some (0, 32792, 0xabcdef0123456789, 12288, 0, true), none, [1], some 0) := by rfl

-- Spurious success permits the predicate to remain false; it does not write
-- the word and does not require a prior WAKE call.
example : (run [.issue 0, .service (.compare 0), .service (.spurious 0),
    .service (.resume 0 0 0 0), .issue 0]).map
    (fun result => (workerView result.1 0,
      (loadDWord result.1.suspended.machine.memory 65536).toOption)) =
    .ok (some (0, 32776, 0xabcdef0123456789, 12288, 0, true), some 0) := by rfl

-- Consuming one invocation cannot clear the other waiting call or reuse the
-- consumed service identity for a second completion.
example : run (twoWaiters 1 ++ [.service (.resume 1 0 0 0), .service (.resume 1 0 0 0)]) =
    .error (.service .missingCall) := by rfl


/-- Invalid full-register ABI requests still execute the real SYSCALL; the
service adapter rejects them atomically rather than truncating their fields. -/
def invalidCapture (register : Register) (value : Word) : Except Physical.Fault (Futex.State × Suspend.Observation) := do
  let state ← initial.mapError Physical.Fault.resources
  let some worker := state.suspended.machine.workers[0]? | throw .missingAtomic
  let changed := { worker.context with registers := fun query =>
    if query = register then value else worker.context.registers query }
  let machine := TSO.install state.suspended.machine 0 state.suspended.machine.memory changed false []
  Physical.issue profile { state with suspended := {state.suspended with machine := machine} } 0

example : invalidCapture .rax 0x1000000ca = .error (.service .unsupportedABI) := by rfl
example : invalidCapture .rdx 0x100000000 = .error (.service .unsupportedABI) := by rfl
example : invalidCapture .rsi 0 = .error (.service .unsupportedABI) := by rfl
example : invalidCapture .r10 1 = .error (.service .unsupportedABI) := by rfl
example : invalidCapture .rdi 65540 = .error (.service .unsupportedABI) := by rfl

end EDSL.Tests.FutexService

#audit_edsl
