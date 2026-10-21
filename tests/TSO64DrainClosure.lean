/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.DrainClosure
import tests.TSO64StoreTrace
import tests.TSO64Denials
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.TSO64DrainClosure
open X86 OS.TSO64

deriving instance DecidableEq for Except

-- Stage equality instances for nested observations at the existing depth limit.
private instance : DecidableEq (Nat × Nat × Word × StoreBuffer.Mixed.Value × Option Nat) :=
  inferInstance
private instance : DecidableEq (List OS.Ownership.Ticket) := inferInstance
private instance : DecidableEq (List OS.Atomics64.HandleId64) := inferInstance
private instance : DecidableEq
    (Nat × Lease × Lease × Word × List OS.Ownership.Ticket × List OS.Atomics64.HandleId64) :=
  inferInstance
private instance : DecidableEq (Word × Word × Word × Phase × Nat × Nat) := inferInstance
private instance : DecidableEq
    (List Word × Word × Word ×
      (Nat × Lease × Lease × Word × List OS.Ownership.Ticket × List OS.Atomics64.HandleId64) ×
      Phase × Nat) := inferInstance

structure Run where
  before : OS.TSO64.State
  after : OS.TSO64.State
  observations : List Observation

def observationSummary (observation : Observation) :
    Option (Nat × Nat × Word × StoreBuffer.Mixed.Value × Option Nat) :=
  match observation with
  | .drained tid (.ordinary _ store) => some (tid, 0, store.address, store.value, none)
  | .drained tid (.managed reference value occurrence) =>
      some (tid, 1, reference.cell.address, .qword value, some occurrence)
  | _ => none

def workerSummary (worker : Worker) : Word × Word × Word × Phase × Nat × Nat :=
  (worker.context.registers .rax, worker.context.rip, worker.context.flags,
    worker.phase, worker.nextStore, worker.pending.length)

/-- Compare all sixteen registers, RIP/flags, every resource field, phase and
occurrence counter. Finite observations let the kernel check the closed run
without deeply unfolding functional contexts in elaborator unification. -/
def workerFrame (worker : Worker) :
    List Word × Word × Word ×
      (Nat × Lease × Lease × Word × List OS.Ownership.Ticket × List OS.Atomics64.HandleId64) ×
      Phase × Nat :=
  ([.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
      .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15].map worker.context.registers,
    worker.context.rip, worker.context.flags,
    (worker.resources.actor, worker.resources.code, worker.resources.caller,
      worker.resources.callerAddress, worker.resources.grants, worker.resources.atomics),
    worker.phase, worker.nextStore)

structure Summary where
  plan : List Action
  pendingBefore : Nat
  observations : List (Option (Nat × Nat × Word × StoreBuffer.Mixed.Value × Option Nat))
  retired : List Nat
  pendingAfter : Nat
  beforeWords : List (Except Error Word)
  afterWords : List (Except Error Word)
  workers : List (Word × Word × Word × Phase × Nat × Nat)
  deriving DecidableEq

def summarize (run : Run) : Summary where
  plan := DrainClosure.actions run.before
  pendingBefore := DrainClosure.totalPending run.before
  observations := run.observations.map observationSummary
  retired := run.observations.map Observation.retired
  pendingAfter := DrainClosure.totalPending run.after
  beforeWords := [131072, 196608, 65536, 65544].map
    (loadQWord (published run.before.world))
  afterWords := [131072, 196608, 65536, 65544].map
    (loadQWord (published run.after.world))
  workers := run.after.workers.map workerSummary

/-- Actual MOV [RDX],RAX; MOV [RDI],RSI; RET. RET occurs while both ordinary
and managed stores are queued. The peer is still running with an empty FIFO. -/
def mixedPrefix : Except Fault OS.TSO64.State := do
  let initial ← TSO64StoreTrace.mixedStart
  let result ← schedule initial [.issue 0 false, .issue 0 true, .issue 0 false] .sharedCell
  pure result.1

def mixedClosure : Except Fault Run := do
  let before ← mixedPrefix
  let result ← DrainClosure.drainAll before .sharedCell
  pure ⟨before, result.1, result.2⟩

/-- Both actual FIFO entries publish, in order, after return. Ordinary and
managed bytes change, the neighboring word and peer-owned memory stay fixed,
and draining retires no instructions or resets occurrence counters. -/
theorem mixed_fifo_publishes_both_authority_kinds_after_return :
    mixedClosure.map summarize = .ok {
      plan := [.drain 0, .drain 0]
      pendingBefore := 2
      observations := [some (0, 0, 131072, .qword 5, none),
        some (0, 1, 65536, .qword 7, some 1)]
      retired := [0, 0]
      pendingAfter := 0
      beforeWords := [.ok 0, .ok 0, .ok 0, .ok 0xabcdef0123456789]
      afterWords := [.ok 5, .ok 0, .ok 7, .ok 0xabcdef0123456789]
      workers := [(5, 0x7000, 0x200202, .returned, 2, 0),
        (5, 393216, 0x200202, .running, 0, 0)]
    } := by decide +kernel

/-- This checks the complete finite context/resource frame, including every register,
for the returned publisher and its running peer. -/
theorem mixed_closure_preserves_complete_worker_frames :
    mixedClosure.map (fun run => run.after.workers.map workerFrame) =
      mixedClosure.map (fun run => run.before.workers.map workerFrame) := by decide +kernel

/-- Actual ordinary stores to disjoint owned allocations, then both RETs.
Neither thread has a managed pending entry, so either policy can drain it. -/
def ordinaryPrefix : Except Fault OS.TSO64.State := do
  let ready ← (TSO64.fixture 0x00000000c3328948 0 19).mapError Fault.os
  let initial ← TSO64.start ready 7 9 0
  let result ← schedule initial [.issue 0 false, .issue 1 false,
    .issue 0 false, .issue 1 false] .ownedOnly
  pure result.1

def ordinaryClosure (profile : Profile) : Except Fault Run := do
  let before ← ordinaryPrefix
  let result ← DrainClosure.drainAll before profile
  pure ⟨before, result.1, result.2⟩

theorem ordinary_fifos_drain_all_threads_under_the_default_profile :
    (ordinaryClosure .ownedOnly).map summarize = .ok {
      plan := [.drain 0, .drain 1]
      pendingBefore := 2
      observations := [some (0, 0, 131072, .qword 7, none),
        some (1, 0, 196608, .qword 9, none)]
      retired := [0, 0]
      pendingAfter := 0
      beforeWords := [.ok 0, .ok 0, .ok 19, .ok 0xabcdef0123456789]
      afterWords := [.ok 7, .ok 9, .ok 19, .ok 0xabcdef0123456789]
      workers := [(0, 0x7000, 0x200202, .returned, 1, 0),
        (0, 0x8000, 0x200202, .returned, 1, 0)]
    } := by decide +kernel

theorem shared_profile_preserves_the_same_ordinary_execution :
    (ordinaryClosure .sharedCell).map summarize =
      (ordinaryClosure .ownedOnly).map summarize := by decide +kernel

theorem both_profiles_preserve_complete_ordinary_worker_frames (profile : Profile) :
    (ordinaryClosure profile).map (fun run => run.after.workers.map workerFrame) =
      (ordinaryClosure profile).map (fun run => run.before.workers.map workerFrame) := by
  cases profile <;> decide +kernel

/-- A synthetic invalid current boundary changes the retained ordinary grant's
epoch after actual issue. Draining cannot treat the buffered payload as present
authority or report a successful shortened observation list. -/
def staleOrdinaryClosure (profile : Profile) : Except Fault Nat := do
  let before ← ordinaryPrefix
  let broken := { before with world := TSO64.stale before.world 1 }
  let result ← DrainClosure.drainAll broken profile
  pure result.2.length

theorem current_ordinary_authority_fault_is_preserved_under_both_profiles :
    staleOrdinaryClosure .ownedOnly = .error .resource ∧
      staleOrdinaryClosure .sharedCell = .error .resource := by
  constructor <;> decide +kernel

/-- Here the valid ordinary head publishes before the stale managed entry is
reached. Exact fault propagation must still reject the entire closure result. -/
def staleManagedClosure : Except Fault Nat := do
  let before ← mixedPrefix
  let broken := { before with world := TSO64.stale before.world 0 }
  let result ← DrainClosure.drainAll broken .sharedCell
  pure result.2.length

theorem later_invalid_managed_authority_is_not_swallowed_after_a_valid_drain :
    staleManagedClosure = .error .resource := by decide +kernel

def defaultMixedClosure : Except Fault Nat := do
  let before ← mixedPrefix
  let result ← DrainClosure.drainAll before .ownedOnly
  pure result.2.length

theorem default_profile_does_not_silently_publish_a_managed_pending_entry :
    defaultMixedClosure = .error .resource := by decide +kernel

end EDSL.Tests.TSO64DrainClosure

#print axioms EDSL.OS.TSO64.DrainClosure.drainAll_complete
#print axioms EDSL.OS.TSO64.DrainClosure.drainAll_after_prefix
#print axioms EDSL.Tests.TSO64DrainClosure.mixed_fifo_publishes_both_authority_kinds_after_return
#print axioms EDSL.Tests.TSO64DrainClosure.mixed_closure_preserves_complete_worker_frames
#audit_edsl
