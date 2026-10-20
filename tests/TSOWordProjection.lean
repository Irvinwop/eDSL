/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures
import EDSL.OS.TSO64.WordProjection
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.TSOWordProjection
open X86 OS.TSO64

structure Checked where
  state : OS.TSO64.State
  valid : WellFormed state .sharedCell

/-- Preserve real resource validity during fixture setup. -/
def attachChecked (before : Checked) (actor : Nat) (context : Context)
    (code caller : Nat) (grants : List OS.Ownership.Ticket)
    (atomics : List OS.Atomics64.HandleId64) : Except Fault Checked :=
  match success : attach before.state actor context code caller grants atomics with
  | .error fault => .error fault
  | .ok after => .ok ⟨after, attach_valid_for .sharedCell before.valid success⟩

/-- Enroll a second disjoint word through the real checked resource API. -/
def enrollAt (before : TSO64.Checked) (ticket : OS.Ownership.Ticket) (address : Word) :
    Except TSO64.OSFault (TSO64.Checked × OS.Atomics64.CellId64) :=
  match success : OS.Atomics64.enroll before.world 7 ticket address with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1,
      (OS.Atomics64.enroll_wellFormed _ _ _ _ _ before.valid success).1⟩, result.2)

/-- Actual bytes: MOV [RDI],RSI; MOV RAX,[RDX]; RET. Each actor writes
one cell then reads the other's; both start with both current handles. -/
def start : Except Fault Checked := do
  let ready ← (TSO64.fixture 0x00c3028b48378948 0 0).mapError Fault.os
  let (allocated, out) ← (TSO64.change ready.checked
    (.allocate 7 ⟨98304, 8⟩ OS.AddressSpace.readWrite)).mapError Fault.os
  let secondTicket ← (TSO64.ticket out).mapError Fault.os
  let (initialized, _) ← (TSO64.change allocated
    (.store64 7 secondTicket 98304 0)).mapError Fault.os
  let (registered, secondCell) ← (enrollAt initialized secondTicket 98304).mapError Fault.os
  let (oneHandle, handleA) ← (TSO64.handle registered secondCell 11).mapError Fault.os
  let (twoHandles, handleB) ← (TSO64.handle oneHandle secondCell 12).mapError Fault.os
  let a := TSO64.context 262144 98304 1 99
  let b := { TSO64.context 327680 65536 1 99 with
    registers := fun register => if register = .rdi then 98304
      else (TSO64.context 327680 65536 1 99).registers register }
  let seed : Checked := ⟨⟨twoHandles.world, []⟩, ⟨twoHandles.valid, by simp⟩⟩
  let one ← attachChecked seed 11 a ready.codeA ready.callerA
    [ready.dataA] [ready.atomicA, handleA]
  attachChecked one 12 b ready.codeB ready.callerB [ready.dataB] [ready.atomicB, handleB]

def actions : List Action :=
  [.issue 0 false, .issue 1 false, .issue 0 false, .issue 1 false,
    .drain 0, .drain 1]

/-- A test adapter applies the same reusable theorem to any successful checked
schedule. The returned labels carry a proof of the actual classified run and
reference path; neither the program nor expected labels enter this adapter. -/
def certifiedRun (before : Checked) (actions : List Action) : Except Fault
    { output : (OS.TSO64.State × List Observation) × List WordProjection.ReferenceLabel //
      WordProjection.ScheduleTrace .sharedCell before.state actions output.1 output.2 ∧
      Concurrency.TSOWord.Path (WordProjection.project before.state) output.2
        (WordProjection.project output.1.1) } :=
  match success : schedule before.state actions .sharedCell with
  | .error fault => .error fault
  | .ok result =>
    match annotated : WordProjection.scheduleLabels before.state actions .sharedCell with
    | .error fault => .error fault
    | .ok labels => .ok ⟨(result, labels),
        WordProjection.schedule_labels_sound before.valid success annotated⟩

def storeBuffering : Except Fault
    (Option Word × Option Word × Except Error Word × Except Error Word × List Nat) := do
  let initial ← start
  let result ← schedule initial.state actions .sharedCell
  pure ((result.1.workers[0]?).map (fun worker => worker.context.registers .rax),
    (result.1.workers[1]?).map (fun worker => worker.context.registers .rax),
    loadQWord (published result.1.world) 65536,
    loadQWord (published result.1.world) 98304, result.2.map Observation.retired)

/-- Store buffering permits both actual reads to return zero before the two
FIFO drains publish one. This distinguishes buffered execution from immediate
publication or sequentially consistent execution of these same instructions. -/
theorem actual_store_buffering : storeBuffering = .ok
    (some 0, some 0, .ok 1, .ok 1, [1, 1, 1, 1, 0, 0]) := by rfl

def storeBufferingLabels : Except Fault (List WordProjection.ReferenceLabel) := do
  let initial ← start
  return (← certifiedRun initial actions).val.2

/-- The exact real litmus has the corresponding classified reference path,
including both zero-valued reads; endpoint equality cannot erase them. -/
theorem actual_store_buffering_reference_labels : storeBufferingLabels = .ok
    [.write 0 ⟨0⟩ 1, .write 1 ⟨1⟩ 1,
      .read 0 ⟨1⟩ 0, .read 1 ⟨0⟩ 0, .tau, .tau] := by rfl

/-- One actor writes RSI then RAX to the same managed cell, then loads it
before either drain. Every source comes from an actual decoded instruction. -/
def newestForwarding : Except Fault
    (Option Word × Except Error Word × List (OS.Atomics64.CellId64 × Word)) := do
  let ready ← (TSO64.fixture 0x8b48078948378948 0x000000000000c307 0).mapError Fault.os
  let initial ← attach ⟨ready.checked.world, []⟩ 11 (TSO64.context 262144 131072 7 9)
    ready.codeA ready.callerA [ready.dataA] [ready.atomicA]
  let result ← schedule initial
    [.issue 0 false, .issue 0 false, .issue 0 false] .sharedCell
  pure ((result.1.workers[0]?).map (fun current => current.context.registers .rax),
    loadQWord (published result.1.world) 65536, WordProjection.buffers result.1 0)

/-- The local MOV returns the newest queued value while published RAM is still
zero; the reference buffer is newest first. Opposite FIFO orientation fails. -/
theorem newest_own_store_is_forwarded : newestForwarding = .ok
    (some 9, .ok 0, [(⟨0⟩, 9), (⟨0⟩, 7)]) := by rfl

def lockedLabels : Except Fault (List WordProjection.ReferenceLabel) := do
  let ready ← (TSO64.fixture 0x0000c307c10f48f0 0 42).mapError Fault.os
  let seed : Checked := ⟨⟨ready.checked.world, []⟩, ⟨ready.checked.valid, by simp⟩⟩
  let initial ← attachChecked seed 11 (TSO64.context 262144 131072 7 9)
    ready.codeA ready.callerA [ready.dataA] [ready.atomicA]
  return (← certifiedRun initial [.issue 0 false]).val.2

/-- Actual LOCK XADD expands to the old-word read and modulo-sum write under
the reference lock, including its publication and unlock. -/
theorem actual_locked_reference_labels : lockedLabels = .ok
    [.lock 0, .read 0 ⟨0⟩ 42, .write 0 ⟨0⟩ 51, .tau, .unlock 0] := by rfl

end EDSL.Tests.TSOWordProjection

#print axioms EDSL.OS.TSO64.WordProjection.managed_read
#print axioms EDSL.OS.TSO64.WordProjection.rmw_path
#print axioms EDSL.OS.TSO64.WordProjection.schedule_labels_sound
#audit_edsl
