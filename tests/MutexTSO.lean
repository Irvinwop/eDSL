/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.MutexTSO
import EDSL.OS.MutexTSO.Publication
import EDSL.Audit

namespace EDSL.Tests.MutexTSO
open X86 OS OS.AddressSpace Examples.MutexWorkers

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

-- Payload bits are symbolic throughout actual checked OS admission. This
-- includes executable/stack loans and the stricter buffered data profile.
example (old : BitVec 32) :
    OS.MutexTSO.Admission (configuration unrestricted) (admitted old) old :=
  admitted_tso_admission old

def issues (identifier count : Nat) : List TSO.Action := List.replicate count (.issue identifier)
def drains (identifier count : Nat) : List TSO.Action := List.replicate count (.drain identifier)

-- Forward completion constructs both issues and publication for every word.
example (old : BitVec 32) :
    ∃ actions result, TSO.schedule (tsoInitial old) actions = .ok result ∧
      TSO.Finished result.1 ∧ MutexReplay.busyCount (TSO.atomicEvents result.2) = 0 ∧
      OS.MutexTSO.blockedCount result.2 = 0 ∧ TSO.retiredCount result.2 = 26 ∧
      OS.MutexTSO.drainCount result.2 = 4 ∧ actions.length = 30 ∧
      loadDWord result.1.memory 131072 = .ok (old + 4) := admitted_tso_action_completion old

-- Pause immediately after the peer's failed XCHG. The holder has two queued
-- writes; physical RAM still contains the original word, and the complete
-- logical witness has already accounted for both retired stores.
def pausedActions : List TSO.Action := issues 0 10 ++ issues 1 2

def paused : TSO.State × List TSO.Observation :=
  checked (TSO.schedule (tsoInitial 0xfffffffe) pausedActions) (by rfl)

theorem paused_schedule : TSO.schedule (tsoInitial 0xfffffffe) pausedActions = .ok paused :=
  checked_ok _ _

example : ∃ logical,
    OS.MutexTSO.Rel (configuration unrestricted) paused.1 logical ∧
    loadDWord (OS.MutexTSO.logicalMemory logical) 131072 = .ok 0 ∧
    loadDWord paused.1.memory 131072 = .ok 0xfffffffe ∧
    TSO.atomicEvents paused.2 = [(0, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 1⟩)] := by
  obtain ⟨logical, _, related⟩ := admitted_tso_prefix _ _ _ paused_schedule
  refine ⟨logical, related, ?_, rfl, rfl⟩
  rw [related.memory]
  rfl

-- A holder with two pending stores and a peer paused after failure needs no
-- future-success or fairness premise to finish the original requests.
example : ∃ actions result, TSO.schedule paused.1 actions = .ok result ∧
    TSO.Finished result.1 ∧ MutexReplay.busyCount (TSO.atomicEvents result.2) = 0 ∧
    OS.MutexTSO.blockedCount result.2 = 0 ∧ TSO.retiredCount result.2 ≤ 30 ∧
    loadDWord result.1.memory 131072 = .ok 2 :=
  admitted_tso_prefix_completion _ _ _ paused_schedule

-- Publishing the FIFO must retain the same entire logical OS witness,
-- including resources, credits, guards and both complete worker contexts.
def published : TSO.State × List TSO.Observation :=
  checked (TSO.schedule paused.1 (drains 0 2)) (by rfl)

theorem published_schedule : TSO.schedule paused.1 (drains 0 2) = .ok published := checked_ok _ _

example : ∃ logical,
    OS.MutexTSO.Rel (configuration unrestricted) paused.1 logical ∧
    OS.MutexTSO.Rel (configuration unrestricted) published.1 logical ∧
    published.1.workers.map OS.MutexTSO.architecture =
      paused.1.workers.map OS.MutexTSO.architecture ∧
    OS.MutexTSO.logicalMemory logical = published.1.memory := by
  obtain ⟨logical, _, related⟩ := admitted_tso_prefix _ _ _ paused_schedule
  have only : OS.MutexTSO.DrainOnly (drains 0 2) := by
    intro action member
    exact ⟨0, List.eq_of_mem_replicate member⟩
  obtain ⟨afterRel, _, _, _⟩ := OS.MutexTSO.drain_schedule_stutters related only published_schedule
  have empty : TSO.Quiescent published.1 := by
    have allEmpty : published.1.workers.all (fun worker => worker.buffer.isEmpty) = true := by rfl
    intro worker member
    have isEmpty := List.all_eq_true.mp allEmpty worker member
    cases buffer : worker.buffer with
    | nil => rfl
    | cons head tail => simp [buffer] at isEmpty
  exact ⟨logical, related, afterRel, afterRel.contexts.trans related.contexts.symm,
    (afterRel.quiescent_memory empty).symm⟩

-- The peer's CMP/JNZ retry is paused across the holder's release. A failed
-- exchange keeps its own result even after global lock RAM becomes free;
-- the conditional branch must still return to the acquisition entry.
def releasedActions : List TSO.Action := pausedActions ++
  issues 0 1 ++ drains 0 1 ++ issues 0 1 ++ drains 0 1 ++ issues 0 3

def released : TSO.State × List TSO.Observation :=
  checked (TSO.schedule (tsoInitial 0xfffffffe) releasedActions) (by rfl)

def retried : TSO.State × List TSO.Observation :=
  checked (TSO.schedule released.1 (issues 1 2)) (by rfl)

example : (loadDWord released.1.memory 65536).toOption = some 0 ∧
    released.1.workers[1]?.map (fun worker => (worker.context.rip, worker.context.registers .rax)) =
      some (4194311, 1) ∧
    retried.1.workers[1]?.map (fun worker => (worker.context.rip, worker.context.registers .rax)) =
      some (4194304, 1) := ⟨rfl, rfl, rfl⟩

def contendedActions : List TSO.Action := releasedActions ++ issues 1 12 ++ drains 1 2 ++ issues 1 3

def contendedRun : TSO.State × List TSO.Observation :=
  checked (TSO.schedule (tsoInitial 0xfffffffe) contendedActions) (by rfl)

theorem contended_schedule :
    TSO.schedule (tsoInitial 0xfffffffe) contendedActions = .ok contendedRun := checked_ok _ _

theorem contended_returned : TSO.Returned contendedRun.1 := by
  intro worker member
  have allReturned : contendedRun.1.workers.all (fun current => current.returned) = true := by rfl
  exact List.all_eq_true.mp allReturned worker member

-- Independent requests require +4 modulo 2^32. The sentinel detects stores
-- wider than the dword contract; RET checks the complete calling convention.
example : (loadDWord contendedRun.1.memory 131072).toOption = some 2 ∧
    (loadDWord contendedRun.1.memory 131076).toOption = some 0xa5b6c7d8 ∧
    (loadDWord contendedRun.1.memory 65536).toOption = some 0 ∧
    contendedRun.1.workers.map (fun worker =>
      (worker.context.registers .rax, worker.context.registers .rsp, worker.context.rip, worker.returned)) =
      [(0, 32776, 8192, true), (0, 32776, 8192, true)] ∧
    TSO.atomicEvents contendedRun.2 =
      [(0, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 1⟩), (0, ⟨65536, 1, 0⟩),
       (1, ⟨65536, 0, 1⟩), (1, ⟨65536, 1, 0⟩)] := ⟨rfl, rfl, rfl, rfl, rfl⟩

-- These endpoints also follow by lifting the actual physical run, without a
-- replay-success assumption, a quiescence premise, or an endpoint check.
example : loadDWord contendedRun.1.memory 131072 = .ok 2 :=
  admitted_tso_total _ _ _ contended_schedule contended_returned

example : TSO.Quiescent contendedRun.1 ∧ TSO.retiredCount contendedRun.2 = 30 := by
  have facts := OS.MutexTSO.completed_observations
    (admitted_tso_admission 0xfffffffe) contended_schedule contended_returned
  exact ⟨facts.quiescent, by simpa only [(admitted_valid (0xfffffffe : BitVec 32)).2.2,
    show MutexReplay.busyCount (TSO.atomicEvents contendedRun.2) = 1 from rfl] using facts.retired⟩

-- Count actual drain observations and both release stalls separately from
-- the thirty retired instructions, including the one real busy retry.
example : OS.MutexTSO.drainCount contendedRun.2 = 4 ∧ contendedActions.length = 36 := by
  have drained := OS.MutexTSO.completed_drains (admitted_tso_admission 0xfffffffe)
    contended_schedule contended_returned
  have counted := OS.MutexTSO.completed_action_count (admitted_tso_admission 0xfffffffe)
    contended_schedule contended_returned
  refine ⟨?_, ?_⟩
  · simpa only [(admitted_valid (0xfffffffe : BitVec 32)).2.2] using drained
  · simpa only [(admitted_valid (0xfffffffe : BitVec 32)).2.2,
      show MutexReplay.busyCount (TSO.atomicEvents contendedRun.2) = 1 from rfl,
      show OS.MutexTSO.blockedCount contendedRun.2 = 2 from rfl] using counted

-- Collection has to succeed and revoke exactly the admitted cohort's real
-- loans. Its complete memory projection, including unrelated bytes and
-- permissions, equals physical RAM after actual returns.
example : ∃ logical collected,
    OS.MutexTSO.Rel (configuration unrestricted) contendedRun.1 logical ∧
    MutexReplay.collect logical = .ok collected ∧
    MutexReplay.CollectedOutcome (admitted 0xfffffffe) (configuration unrestricted) 0xfffffffe collected ∧
    toMemory collected.1.shared.resources.space = contendedRun.1.memory ∧
    ∀ loanId, collected.1.shared.loans loanId =
      if loanId ∈ MutexReplay.cohortLoanIds (admitted 0xfffffffe).workers then none
      else (admitted 0xfffffffe).shared.shared.loans loanId := by
  obtain ⟨logical, collected, _, related, joined, outcome, memory, loans⟩ :=
    OS.MutexTSO.completed_collection_exists (admitted_tso_admission 0xfffffffe)
      contended_schedule contended_returned
  exact ⟨logical, collected, related, joined, outcome, memory, loans⟩

-- Worker zero is stopped just before RET; worker one then acquires the lock
-- and retires both stores. RET must preserve the complete peer context and
-- read the original stack despite the peer's two pending payload writes.
def peerPendingActions : List TSO.Action :=
  issues 0 10 ++ drains 0 2 ++ issues 0 2 ++ issues 1 10

def peerPending : TSO.State × List TSO.Observation :=
  checked (TSO.schedule (tsoInitial 0xfffffffe) peerPendingActions) (by rfl)

theorem peer_pending_schedule :
    TSO.schedule (tsoInitial 0xfffffffe) peerPendingActions = .ok peerPending := checked_ok _ _

def peerReturn : TSO.State × List TSO.Observation :=
  checked (TSO.schedule (tsoInitial 0xfffffffe) (peerPendingActions ++ [.issue 0])) (by rfl)

theorem peer_return_schedule :
    TSO.schedule (tsoInitial 0xfffffffe) (peerPendingActions ++ [.issue 0]) = .ok peerReturn :=
  checked_ok _ _

example : ∃ after, OS.MutexTSO.Rel (configuration unrestricted) peerReturn.1 after := by
  obtain ⟨after, _, related⟩ := admitted_tso_prefix _ _ _ peer_return_schedule
  exact ⟨after, related⟩

example : peerReturn.1.workers.map (fun worker =>
      (worker.returned, worker.buffer.length, worker.context.registers .rsp, worker.context.rip,
        worker.context.registers .rbx)) =
      [(true, 0, 32776, 8192, 0xfeedface89abcdef),
       (false, 2, 32768, 4194333, 0xfeedface89abcdef)] := by rfl

-- TSO fetches shared executable bytes and reads the saved stack even while
-- another worker buffers. Denying the last byte must produce the precise
-- architectural failure rather than succeeding through an overlay shortcut.
def denyReturnByte : TSO.State :=
  { peerPending.1 with memory := { peerPending.1.memory with
      read := fun address => if address = 32775 then none else peerPending.1.memory.read address } }

def denyRet : TSO.State :=
  { peerPending.1 with memory := { peerPending.1.memory with
      executable := fun address => if address = 4194340 then false else peerPending.1.memory.executable address } }

example : TSO.issue denyReturnByte 0 = .error (.machine (.inaccessibleStack 32775)) := by rfl
example : TSO.issue denyRet 0 = .error (.machine (.inaccessibleInstruction 4194340)) := by rfl

end EDSL.Tests.MutexTSO

#audit_edsl
