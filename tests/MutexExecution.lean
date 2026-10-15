/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.MutexExecution
import EDSL.Audit

namespace EDSL.Tests.MutexExecution
open X86 OS OS.AddressSpace OS.MutexReplay Examples.MutexWorkers

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

-- The whole payload remains symbolic. Checked construction establishes code,
-- return-stack and loan readiness; forward execution constructs a completing
-- architectural schedule without a future-success or endpoint-check premise.
example (old : BitVec 32) :
    ∃ selections result, MachineThreads.schedule (erase (admitted old)) selections = .ok result ∧
      MachineThreads.Finished result.1 ∧ busyCount result.2 = 0 ∧ selections.length = 26 ∧
      loadDWord result.1.memory 131072 = .ok (old + 4) := admitted_machine_completion old

-- Every existing unreturned choice is enabled in the instruction-only
-- machine. In particular, this does not filter executions through replay.
example (old : BitVec 32) (identifier : Nat) (worker : MachineThreads.Worker)
    (live : (erase (admitted old)).workers[identifier]? = some worker)
    (unreturned : worker.returned = false) :
    ∃ result, MachineThreads.dispatch (erase (admitted old)) identifier = .ok result :=
  machine_dispatch_enabled _ _ _ _ (admitted_valid old).1 (admitted_executionReady old) live unreturned

def rawInitial : MachineThreads.State := erase (admitted 0xfffffffe)

-- These instructions include an actual busy XCHG while the first worker has
-- stored an odd intermediate payload. Expected outputs use the independent
-- +2 request, machine calling convention and adjacent-byte frame contracts.
def rawRun : MachineThreads.State × List (Nat × AtomicEvent) :=
  checked (MachineThreads.schedule rawInitial contended) (by rfl)

theorem raw_schedule : MachineThreads.schedule rawInitial contended = .ok rawRun := checked_ok _ _

def observe (result : MachineThreads.State × List (Nat × AtomicEvent)) :
    Option (BitVec 32) × Option (BitVec 32) × Option (BitVec 32) ×
      List (Word × Word × Word × Bool) × List (Nat × AtomicEvent) :=
  ((loadDWord result.1.memory 131072).toOption,
   (loadDWord result.1.memory 131076).toOption,
   (loadDWord result.1.memory 65536).toOption,
   result.1.workers.map (fun worker =>
     (worker.context.registers .rax, worker.context.registers .rsp, worker.context.rip, worker.returned)),
   result.2)

-- A wrong store width, lost update, missing busy event, nonzero return, wrong
-- stack advance, or completion before actual RET changes this observation.
example : observe rawRun = (some 2, some 0xa5b6c7d8, some 0,
    [(0, 32776, 8192, true), (0, 32776, 8192, true)],
    [(0, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 1⟩), (0, ⟨65536, 1, 0⟩),
     (1, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 0⟩)]) := by rfl

theorem raw_finished : MachineThreads.Finished rawRun.1 := by
  intro worker member
  have allReturned : rawRun.1.workers.all (fun current => current.returned) = true := by rfl
  exact List.all_eq_true.mp allReturned worker member

-- The +4 conclusion also follows from universal architectural coverage.
-- Completion observes only actual RET markers, rather than payload values.
example : loadDWord rawRun.1.memory 131072 = .ok 2 :=
  admitted_machine_total 0xfffffffe contended rawRun raw_schedule raw_finished

-- Pause after the peer's failed XCHG, before its CMP/JNE retry. Finishing
-- the holder first must account for that pending retry; the two potentials
-- require 21 more instructions; the holder and a fresh peer would need 19.
def paused : MutexReplay.State × List (Nat × AtomicEvent) :=
  checked (schedule (admitted 0xfffffffe) (List.replicate 7 0 ++ List.replicate 2 1)) (by rfl)

theorem paused_schedule :
    schedule (admitted 0xfffffffe) (List.replicate 7 0 ++ List.replicate 2 1) = .ok paused := checked_ok _ _

example : ∃ selections result, schedule paused.1 selections = .ok result ∧
    Finished result.1 ∧ busyCount result.2 = 0 ∧ selections.length = 21 := by
  obtain ⟨selections, result, success, finished, noBusy, steps, _⟩ :=
    admitted_prefix_completion _ _ _ paused_schedule
  exact ⟨selections, result, success, finished, noBusy, by
    calc selections.length = potentialSum paused.1 := steps
         _ = 21 := by rfl⟩

-- The same paused state is reached by the instruction-only scheduler. It
-- retains the odd intermediate payload and the failed atomic acquisition;
-- those observations do not become new premises of its eventual +4 contract.
def rawPaused : MachineThreads.State × List (Nat × AtomicEvent) :=
  checked (MachineThreads.schedule rawInitial (List.replicate 7 0 ++ List.replicate 2 1)) (by rfl)

theorem raw_paused_schedule :
    MachineThreads.schedule rawInitial (List.replicate 7 0 ++ List.replicate 2 1) = .ok rawPaused := checked_ok _ _

example : loadDWord rawPaused.1.memory 131072 = .ok 0xffffffff ∧
    rawPaused.2 = [(0, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 1⟩)] := ⟨rfl, rfl⟩

example : ∃ selections result, MachineThreads.schedule rawPaused.1 selections = .ok result ∧
    MachineThreads.Finished result.1 ∧ busyCount result.2 = 0 ∧ selections.length ≤ 30 ∧
    loadDWord result.1.memory 131072 = .ok 2 :=
  admitted_machine_prefix_completion _ _ _ raw_paused_schedule

-- Selection errors are explicit and do not run an instruction. Returning
-- workers stop at their RET even though the caller target is unmapped.
example : MachineThreads.dispatch rawInitial 2 = .error .missingThread := by rfl
example : MachineThreads.dispatch rawRun.1 0 = .error .alreadyReturned := by rfl

def beforeRet : MachineThreads.State × List (Nat × AtomicEvent) :=
  checked (MachineThreads.schedule rawInitial (List.replicate 12 0)) (by rfl)

-- The bare machine has no expected-code or stack-admission gate. Its next
-- real fetch/read must detect corruption at the precise architectural byte.
def denyRet : MachineThreads.State :=
  { beforeRet.1 with memory := { beforeRet.1.memory with
      executable := fun address => if address = 4194340 then false else beforeRet.1.memory.executable address } }

def denyReturnByte : MachineThreads.State :=
  { beforeRet.1 with memory := { beforeRet.1.memory with
      read := fun address => if address = 32775 then none else beforeRet.1.memory.read address } }

example : MachineThreads.dispatch denyRet 0 =
    .error (.machine (.inaccessibleInstruction 4194340)) := by rfl

example : MachineThreads.dispatch denyReturnByte 0 =
    .error (.machine (.inaccessibleStack 32775)) := by rfl

end EDSL.Tests.MutexExecution

#audit_edsl
