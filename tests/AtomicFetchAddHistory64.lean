/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicFetchAddHistory64

namespace EDSL.Tests.AtomicFetchAddHistory64
open X86 OS.AddressSpace OS.Atomics64
open OS.AtomicFetchAddHistory64

abbrev Managed := OS.Atomics64.State
abbrev Fault := OS.Atomics64.Fault

structure Checked where
  state : Managed
  valid : WellFormed state

def seed : Checked :=
  ⟨empty (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty OS.AddressSpace.empty))),
    empty_wellFormed _ (OS.Atomics.empty_wellFormed _
      (OS.Borrowing.empty_wellFormed _ (OS.Ownership.empty_wellFormed _)))⟩

def change (before : Checked) (operation : OS.Ownership.Mutation) :
    Except Fault (Checked × Option OS.Ownership.Ticket) :=
  match success : mutate before.state operation with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1, mutate_wellFormed _ _ _ before.valid success⟩, result.2)

def registerCell (before : Checked) (ticket : OS.Ownership.Ticket) (address : Word) :
    Except Fault (Checked × CellId64) :=
  match success : enroll before.state 7 ticket address with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1, (enroll_wellFormed _ _ _ _ _ before.valid success).1⟩, result.2)

def issueHandle (before : Checked) (cell : CellId64) (actor : Nat) :
    Except Fault (Checked × HandleId64) :=
  match success : issue before.state 7 cell actor with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1, (issue_wellFormed _ _ _ _ _ before.valid success).1⟩, result.2)

def ticketFrom (output : Option OS.Ownership.Ticket) : Except Fault OS.Ownership.Ticket :=
  match output with
  | some ticket => .ok ticket
  | none => .error .missingCell

structure Ready where
  checked : Checked
  ticket : OS.Ownership.Ticket
  target : CellId64
  first : HandleId64
  second : HandleId64
  other : HandleId64
  scratch : OS.Ownership.Ticket

/-- Three disjoint real allocations: a registered target with two actors,
a distinct registered cell, and an ordinary scratch allocation. Registration
reserves a complete allocation, so target's neighbor is protected too. -/
def setup (old : Word) : Except Fault Ready := do
  let (allocated, output) ← change seed (.allocate 7 ⟨65536, 16⟩ readWrite)
  let ticket ← ticketFrom output
  let (neighbor, _) ← change allocated (.store64 7 ticket 65544 0xaabbccddeeff0011)
  let (written, _) ← change neighbor (.store64 7 ticket 65536 old)
  let (registered, target) ← registerCell written ticket 65536
  let (one, first) ← issueHandle registered target 11
  let (two, second) ← issueHandle one target 12
  let (otherAllocated, output) ← change two (.allocate 7 ⟨131072, 8⟩ readWrite)
  let otherTicket ← ticketFrom output
  let (otherWritten, _) ← change otherAllocated (.store64 7 otherTicket 131072 0x12345678ffffffff)
  let (otherRegistered, otherCell) ← registerCell otherWritten otherTicket 131072
  let (otherLive, other) ← issueHandle otherRegistered otherCell 12
  let (last, output) ← change otherLive (.allocate 7 ⟨196608, 8⟩ readWrite)
  let scratch ← ticketFrom output
  return ⟨last, ticket, target, first, second, other, scratch⟩

/-- This executable trace retains its derivation from actual checked operations,
not a supplied list of alleged arithmetic responses. -/
structure Trace (initial : Managed) where
  checked : Checked
  labels : List (Option FetchAddEvent)
  history : OS.AtomicFetchAddHistory64.History initial labels checked.state

def start (ready : Ready) : Trace ready.checked.state :=
  ⟨ready.checked, [], .refl⟩

def add {initial : Managed} (trace : Trace initial) (actor : Nat) (handle : HandleId64)
    (delta : Word) : Except Fault (Trace initial) :=
  match success : fetchAdd trace.checked.state actor handle delta with
  | .error fault => .error fault
  | .ok result => .ok ⟨⟨result.1, fetchAdd_wellFormed _ _ _ _ _ trace.checked.valid success⟩,
      trace.labels ++ [some result.2], trace.history.trans (.next (.fetchAdd success) .refl)⟩

def ordinary {initial : Managed} (trace : Trace initial) (operation : OS.Ownership.Mutation) :
    Except Fault (Trace initial) :=
  match success : mutate trace.checked.state operation with
  | .error fault => .error fault
  | .ok result => .ok ⟨⟨result.1, mutate_wellFormed _ _ _ trace.checked.valid success⟩,
      trace.labels ++ [none], trace.history.trans (.next (.mutate success) .refl)⟩

def pause {initial : Managed} (trace : Trace initial) : Trace initial :=
  ⟨trace.checked, trace.labels ++ [none], trace.history.trans (.next .idle .refl)⟩

def schedule (ready : Ready) (firstDelta secondDelta : Word) :
    Except Fault (Trace ready.checked.state) := do
  let first ← add (start ready) 11 ready.first firstDelta
  let other ← add first 12 ready.other 1
  let written ← ordinary other (.store64 7 ready.scratch 196608 0x9988776655443322)
  let second ← add (pause written) 12 ready.second secondDelta
  add second 11 ready.first 0

/-- The client uses the reusable theorem to certify the actual trace. Final
load existence and counter legality are derived without a future-success or
post-value assumption. Client labels are just the actual handle and actor. -/
theorem certify_trace (ready : Ready) (trace : Trace ready.checked.state)
    (cell : OS.Atomics64.Cell) (live : ready.checked.state.cells ready.target = some cell)
    (prior : Word)
    (observed : loadQWord (toMemory ready.checked.state.legacy.shared.resources.space) cell.address = .ok prior) :
    ∃ final, loadQWord (toMemory trace.checked.state.legacy.shared.resources.space) cell.address = .ok final ∧
      Concurrency.ModuloCounter.eval prior
        (selectedCalls ready.target FetchAddEvent.handle FetchAddEvent.actor trace.labels) = some final := by
  obtain ⟨final, readback, legal⟩ := trace.history.project_exists ready.checked.valid ready.target cell live
    FetchAddEvent.handle FetchAddEvent.actor prior observed
  exact ⟨final, readback, Concurrency.ModuloCounter.eval_complete legal⟩

/-- Literal responses independently distinguish full64 carry, peer-current
reads, cell-ID filtering, zero-event retention and silent ordinary writes. -/
def observations (old firstDelta secondDelta : Word) := do
  let ready ← setup old
  let trace ← schedule ready firstDelta secondDelta
  let memory := toMemory trace.checked.state.legacy.shared.resources.space
  pure (selectedCalls ready.target FetchAddEvent.handle FetchAddEvent.actor trace.labels,
    loadQWord memory 65536, loadQWord memory 65544, loadQWord memory 131072,
    loadQWord memory 196608, trace.labels.length)

example : observations 0xfffffffffffffffe 1 2 = .ok
    ([⟨⟨0⟩,11,1,0xfffffffffffffffe⟩,
      ⟨⟨1⟩,12,2,0xffffffffffffffff⟩,
      ⟨⟨0⟩,11,0,1⟩],
      .ok 1,.ok 0xaabbccddeeff0011,.ok 0x1234567900000000,.ok 0x9988776655443322,6) := by rfl

example : observations 0x12345678ffffffff 1 0x8000000100000000 = .ok
    ([⟨⟨0⟩,11,1,0x12345678ffffffff⟩,
      ⟨⟨1⟩,12,0x8000000100000000,0x1234567900000000⟩,
      ⟨⟨0⟩,11,0,0x9234567a00000000⟩],
      .ok 0x9234567a00000000,.ok 0xaabbccddeeff0011,.ok 0x1234567900000000,.ok 0x9988776655443322,6) := by rfl

/-- Projecting the other cell must retain its own actual old/input pair and
ignore the two target actors, including target's zero delta. -/
def otherProjection := do
  let ready ← setup 0xfffffffffffffffe
  let trace ← schedule ready 1 2
  pure (selectedCalls ⟨1⟩ FetchAddEvent.handle FetchAddEvent.actor trace.labels)

example : otherProjection = .ok [⟨⟨2⟩,12,1,0x12345678ffffffff⟩] := by rfl

def failed {α : Type} (operation : Except Fault α) (expected : Fault) : Bool :=
  match operation with
  | .error actual => decide (actual = expected)
  | .ok _ => false

/-- Checked traces cannot admit direct or neighboring ordinary stores, transfer,
release or protection of the registered target; actor changes are rechecked. -/
def denials := do
  let ready ← setup 0x8000000000000001
  let trace ← schedule ready 0 0
  let state := trace.checked.state
  pure [failed (ordinary trace (.store64 7 ready.ticket 65536 0)) .reserved,
    failed (ordinary trace (.store64 7 ready.ticket 65544 0)) .reserved,
    failed (ordinary trace (.release 7 ready.ticket)) .reserved,
    failed (ordinary trace (.transfer 7 ready.ticket 12)) .reserved,
    failed (ordinary trace (.protect 7 ready.ticket readOnly)) .reserved,
    failed (add trace 12 ready.first 0) .wrongActor,
    failed (add trace 11 ⟨99⟩ 0) .missingHandle,
    failed (retire state 7 ready.target) .liveHandles]

example : denials = .ok (List.replicate 8 true) := by rfl

/-- Closing is outside the persistent trace; a closed handle cannot start a
new arithmetic position even though the registered allocation remains live. -/
def closedDenied := do
  let ready ← setup 0x8000000000000001
  let closed ← close ready.checked.state 11 ready.first
  pure (failed (fetchAdd closed 11 ready.first 0) .missingHandle,
    failed (mutate closed (.store64 7 ready.ticket 65536 0)) .reserved)

example : closedDenied = .ok (true,true) := by rfl

/-- Counter legality rejects a deliberately corrupted full old response; this
is an independent checker against the observed OS history, not a second RMW. -/
def corruptedResponse := do
  let ready ← setup 0x12345678ffffffff
  let trace ← schedule ready 1 2
  let calls := selectedCalls ready.target FetchAddEvent.handle FetchAddEvent.actor trace.labels
  let corrupt := calls.map fun (call : Concurrency.ModuloCounter.Call 64 HandleId64 Nat) => { call with output := BitVec.ofNat 64 call.output.toNat.toUInt32.toNat }
  pure (Concurrency.ModuloCounter.eval 0x12345678ffffffff corrupt)

example : corruptedResponse = .ok none := by rfl

end EDSL.Tests.AtomicFetchAddHistory64

#print axioms EDSL.OS.AtomicFetchAddHistory64.History.sequential
#print axioms EDSL.OS.AtomicFetchAddHistory64.History.project_exists
#print axioms EDSL.OS.AtomicFetchAddHistory64.History.total
#print axioms EDSL.Tests.AtomicFetchAddHistory64.certify_trace
#audit_edsl
