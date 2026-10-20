/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.FetchAddCalls64
import tests.TSO64Fixtures

namespace EDSL.Tests.FetchAddCalls64
open X86 OS.FetchAddCalls64

structure Current where
  state : OS.TSO64.State
  valid : OS.TSO64.WellFormed state

def attach (before : Current) (actor : Nat) (context : OS.TSO64.Context) (code caller : Nat)
    (grants : List OS.Ownership.Ticket) (atomics : List OS.Atomics64.HandleId64) :
    Except OS.TSO64.Fault Current :=
  match success : OS.TSO64.attach before.state actor context code caller grants atomics with
  | .error fault => .error fault
  | .ok after => .ok ⟨after, OS.TSO64.attach_valid before.valid success⟩

def selectTarget (current : Current) : Except OS.TSO64.Fault (Sigma (CheckedState ⟨0⟩)) :=
  match live : current.state.world.cells ⟨0⟩ with
  | none => throw .noAtomicGrant
  | some cell => .ok ⟨cell, ⟨current.state, current.valid, live⟩⟩

def setup (first second old deltaA deltaB : Word) :
    Except OS.TSO64.Fault (Sigma (CheckedState ⟨0⟩)) := do
  let ready ← (TSO64.fixture first second old).mapError OS.TSO64.Fault.os
  let initial : Current := ⟨⟨ready.checked.world, []⟩, ready.checked.valid, by simp⟩
  let one ← attach initial 11 (TSO64.context 262144 131072 deltaA 0)
    ready.codeA ready.callerA [ready.dataA] [ready.atomicA]
  let two ← attach one 12 (TSO64.context 327680 196608 deltaB 0)
    ready.codeB ready.callerB [ready.dataB] [ready.atomicB]
  selectTarget two

def view {cell} (result : Result Nat ⟨0⟩ cell) :=
  (result.events, result.observations.map OS.TSO64.Observation.retired,
    read result.state.state cell,
    OS.TSO64.collect result.state.state 0, OS.TSO64.collect result.state.state 1)

def observe (first second old deltaA deltaB : Word) (entries : List (Entry Nat)) := do
  let ⟨cell, before⟩ ← setup first second old deltaA deltaB
  return ((replay ⟨0⟩ cell before entries).map view, checkComplete ⟨0⟩ cell before entries)

/-- Environment labels bracket separately scheduled MOV, RMW and RET actions. -/
def forward (old middle deltaA deltaB : Word) : List (Entry Nat) :=
  [.invoke 10 0 deltaA, .invoke 20 1 deltaB,
    .execute (.issue 0 false) .quiet, .execute (.issue 1 true) .quiet,
    .execute (.issue 0 false) (.rmw 10),
    .execute (.issue 0 false) (.response 10 0 old),
    .execute (.issue 1 false) (.rmw 20),
    .execute (.issue 1 false) (.response 20 1 middle)]

def reverse (old middle deltaA deltaB : Word) : List (Entry Nat) :=
  [.invoke 10 0 deltaA, .invoke 20 1 deltaB,
    .execute (.issue 0 true) .quiet, .execute (.issue 1 false) .quiet,
    .execute (.issue 1 false) (.rmw 20),
    .execute (.issue 0 false) (.rmw 10),
    .execute (.issue 1 false) (.response 20 1 old),
    .execute (.issue 0 false) (.response 10 0 middle)]

-- Independent literal old words and final values distinguish both actual
-- issue orders. The high half and the carry cannot be supplied by EAX32.
example : observe 0x07c10f48f0f08948 0x90909090909090c3
    0x11223344ffffffff 1 0x100000001
    (forward 0x11223344ffffffff 0x1122334500000000 1 0x100000001) = .ok
    (some ([.invoke 10 0 1, .invoke 20 1 0x100000001,
      .point ⟨10,0,1,0x11223344ffffffff⟩, .respond 10 0 0x11223344ffffffff,
      .point ⟨20,1,0x100000001,0x1122334500000000⟩, .respond 20 1 0x1122334500000000],
      [1,1,1,1,1,1], .ok 0x1122334600000001,
      .ok 0x11223344ffffffff, .ok 0x1122334500000000), true) := by rfl

example : observe 0x07c10f48f0f08948 0x90909090909090c3
    0x11223344ffffffff 1 0x100000001
    (reverse 0x11223344ffffffff 0x1122334600000000 1 0x100000001) = .ok
    (some ([.invoke 10 0 1, .invoke 20 1 0x100000001,
      .point ⟨20,1,0x100000001,0x11223344ffffffff⟩,
      .point ⟨10,0,1,0x1122334600000000⟩,
      .respond 20 1 0x11223344ffffffff, .respond 10 0 0x1122334600000000],
      [1,1,1,1,1,1], .ok 0x1122334600000001,
      .ok 0x1122334600000000, .ok 0x11223344ffffffff), true) := by rfl

def admitted (old deltaA deltaB : Word) (entries : List (Entry Nat)) := do
  let ⟨cell, before⟩ ← setup 0x07c10f48f0f08948 0x90909090909090c3 old deltaA deltaB
  return checkComplete ⟨0⟩ cell before entries

example : admitted 0xfffffffffffffffe 1 2 (forward 0xfffffffffffffffe 0xffffffffffffffff 1 2) =
    .ok true := by rfl
example : admitted 0xfffffffffffffffe 1 2 (reverse 0xfffffffffffffffe 0 1 2) = .ok true := by rfl

-- Admission must reject each plausible annotation defect through real replay
-- and/or the generic protocol, including zero-delta suppression.
def malformed : List (List (Entry Nat)) :=
  let good := forward 0x11223344ffffffff 0x11223344ffffffff 0 0
  [good.set 0 (.invoke 10 0 0x100000000),
    good.set 0 (.invoke 10 1 0),
    good.set 4 (.execute (.issue 0 false) .quiet),
    good.set 4 (.execute (.issue 0 false) (.rmw 99)),
    good.set 2 (.execute (.issue 0 false) (.rmw 10)),
    good.set 5 (.execute (.issue 0 false) (.response 10 0 0xffffffff)),
    good.set 5 (.execute (.issue 0 false) (.response 10 1 0x11223344ffffffff)),
    good.set 5 (.execute (.issue 0 false) (.response 99 0 0x11223344ffffffff)),
    good.set 5 (.execute (.issue 0 false) .quiet),
    good.set 6 (.execute (.issue 1 false) (.rmw 10)),
    good.set 7 (.execute (.issue 1 false) (.response 10 1 0x11223344ffffffff)),
    good.drop 1,
    .invoke 10 0 0 :: good,
    good ++ [.invoke 30 0 0],
    good ++ [.execute (.issue 0 false) (.response 10 0 0x11223344ffffffff)]]

def rejected := do
  let ⟨cell, before⟩ ← setup 0x07c10f48f0f08948 0x90909090909090c3 0x11223344ffffffff 0 0
  return malformed.map (checkComplete ⟨0⟩ cell before)

example : admitted 0x11223344ffffffff 0 0
    (forward 0x11223344ffffffff 0x11223344ffffffff 0 0) = .ok true := by rfl
example : rejected = .ok (List.replicate 15 false) := by rfl

-- Own publication gates LOCK; a peer's pending FIFO does not. The blocked
-- attempt and both drains stay in the actual trace without inventing points.
def buffered : List (Entry Nat) :=
  [.invoke 10 0 1, .invoke 20 1 2,
    .execute (.issue 0 false) .quiet, .execute (.issue 1 false) .quiet,
    .execute (.issue 0 false) .quiet, .execute (.issue 1 false) .quiet,
    .execute (.issue 0 false) .quiet, .execute (.drain 0) .quiet,
    .execute (.issue 0 false) (.rmw 10),
    .execute (.issue 1 false) .quiet,
    .execute (.issue 0 false) (.response 10 0 0x11223344ffffffff),
    .execute (.drain 1) .quiet,
    .execute (.issue 1 false) (.rmw 20),
    .execute (.issue 1 false) (.response 20 1 0x1122334500000000)]

example : observe 0x48f0f08948328948 0x90909090c307c10f 0x11223344ffffffff 1 2 buffered = .ok
    (some ([.invoke 10 0 1, .invoke 20 1 2,
      .point ⟨10,0,1,0x11223344ffffffff⟩, .respond 10 0 0x11223344ffffffff,
      .point ⟨20,1,2,0x1122334500000000⟩, .respond 20 1 0x1122334500000000],
      [1,1,1,1,0,0,1,0,1,0,1,1], .ok 0x1122334500000002,
      .ok 0x11223344ffffffff, .ok 0x1122334500000000), true) := by rfl

def inventedBuffered := do
  let ⟨cell, before⟩ ← setup 0x48f0f08948328948 0x90909090c307c10f 0x11223344ffffffff 1 2
  return ([buffered.set 6 (.execute (.issue 0 false) (.rmw 10)),
    buffered.set 7 (.execute (.drain 0) (.rmw 10)),
    buffered.set 7 (.execute (.drain 0) (.response 10 0 0x11223344ffffffff))]).map
      (checkComplete ⟨0⟩ cell before)

example : inventedBuffered = .ok [false,false,false] := by rfl

-- RET leaves its own already queued store unpublished. Collection requires
-- the later real drain, while the call response belongs to the earlier RET.
def pendingReturn (suffix : List (Entry Nat)) :=
  observe 0x07c10f48f0f08948 0x90909090c3328948 0x11223344ffffffff 1 0
    ([.invoke 10 0 1, .execute (.issue 0 false) .quiet,
      .execute (.issue 0 false) (.rmw 10), .execute (.issue 0 false) .quiet,
      .execute (.issue 0 false) (.response 10 0 0x11223344ffffffff)] ++ suffix)

example : pendingReturn [] = .ok
    (some ([.invoke 10 0 1, .point ⟨10,0,1,0x11223344ffffffff⟩,
      .respond 10 0 0x11223344ffffffff], [1,1,1,1], .ok 0x1122334500000000,
      .error .resource, .error .resource), true) := by rfl
example : pendingReturn [.execute (.drain 0) .quiet] = .ok
    (some ([.invoke 10 0 1, .point ⟨10,0,1,0x11223344ffffffff⟩,
      .respond 10 0 0x11223344ffffffff], [1,1,1,1,0], .ok 0x1122334500000000,
      .ok 0x11223344ffffffff, .error .resource), true) := by rfl

def sameActorSetup : Except OS.TSO64.Fault (Sigma (CheckedState ⟨0⟩)) := do
  let ready ← (TSO64.fixture 0x07c10f48f0f08948 0x90909090909090c3
    0x11223344ffffffff).mapError OS.TSO64.Fault.os
  match borrowed : OS.Atomics64.readBorrow ready.checked.world 22 ⟨4,0⟩ 11 ⟨327680,8⟩ with
  | .error fault => throw (.os fault)
  | .ok caller =>
    let initial : Current := ⟨⟨caller.1, []⟩,
      OS.Atomics64.readBorrow_wellFormed _ _ _ _ _ _ ready.checked.valid borrowed, by simp⟩
    let one ← attach initial 11 (TSO64.context 262144 131072 0 0)
      ready.codeA ready.callerA [ready.dataA] [ready.atomicA]
    let two ← attach one 11 (TSO64.context 327680 131072 0 0)
      ready.codeA caller.2 [ready.dataA] [ready.atomicA]
    selectTarget two

-- Two contexts share an OS actor and handle. Their identical zero RMW events
-- still receive distinct supplied occurrence IDs and distinct scheduler tids.
def identicalZero := do
  let ⟨cell, before⟩ ← sameActorSetup
  let entries := forward 0x11223344ffffffff 0x11223344ffffffff 0 0
  return ((replay ⟨0⟩ cell before entries).map fun (result : Result Nat ⟨0⟩ cell) =>
    (result.events, result.observations.filterMap fun (observation : OS.TSO64.Observation) => match observation with
      | .rmw _ event => some (event.actor, event.handle)
      | _ => none), checkComplete ⟨0⟩ cell before entries)

example : identicalZero = .ok
    (some ([.invoke 10 0 0, .invoke 20 1 0,
      .point ⟨10,0,0,0x11223344ffffffff⟩, .respond 10 0 0x11223344ffffffff,
      .point ⟨20,1,0,0x11223344ffffffff⟩, .respond 20 1 0x11223344ffffffff],
      [(11,⟨0⟩),(11,⟨0⟩)]), true) := by rfl

def enrollAt (before : TSO64.Checked) (ticket : OS.Ownership.Ticket) (address : Word) :
    Except OS.Atomics64.Fault (TSO64.Checked × OS.Atomics64.CellId64) :=
  match success : OS.Atomics64.enroll before.world 7 ticket address with
  | .error fault => .error fault
  | .ok result => .ok (⟨result.1,
      (OS.Atomics64.enroll_wellFormed _ _ _ _ _ before.valid success).1⟩, result.2)

def otherSetup : Except OS.TSO64.Fault (Sigma (CheckedState ⟨0⟩)) := do
  let ready ← (TSO64.fixture 0x9090c337c10f48f0 0x9090909090909090
    0x11223344ffffffff).mapError OS.TSO64.Fault.os
  let (allocated, out) ← (TSO64.change ready.checked (.allocate 7 ⟨524288,16⟩ OS.AddressSpace.readWrite)).mapError OS.TSO64.Fault.os
  let ticket ← (TSO64.ticket out).mapError OS.TSO64.Fault.os
  let (written, _) ← (TSO64.change allocated (.store64 7 ticket 524288 64)).mapError OS.TSO64.Fault.os
  let (registered, cell) ← (enrollAt written ticket 524288).mapError OS.TSO64.Fault.os
  let (handled, identifier) ← (TSO64.handle registered cell 11).mapError OS.TSO64.Fault.os
  let initial : Current := ⟨⟨handled.world, []⟩, handled.valid, by simp⟩
  let context := TSO64.context 262144 131072 9 0
  let actual := { context with registers := fun register => if register = .rdi then 524288 else context.registers register }
  let one ← attach initial 11 actual ready.codeA ready.callerA [] [identifier]
  selectTarget one

-- A real distinct-cell RMW preserves the selected target via registration,
-- while it cannot stand in for a target point or a response annotation.
def otherCell := do
  let ⟨cell, before⟩ ← otherSetup
  let quiet : List (Entry Nat) := [.execute (.issue 0 false) .quiet]
  return ((replay ⟨0⟩ cell before quiet).map fun (result : Result Nat ⟨0⟩ cell) =>
      (read result.state.state cell, loadQWord (OS.TSO64.published result.state.state.world) 524288,
        TSO64.events result.observations),
    checkComplete ⟨0⟩ cell before quiet,
    (replay ⟨0⟩ cell before [.execute (.issue 0 false) (.rmw 10)]).isNone,
    (replay ⟨0⟩ cell before [.execute (.issue 0 false) (.response 10 0 64)]).isNone)

example : otherCell = .ok
    (some (.ok 0x11223344ffffffff, .ok 73, [(0,9,64,73)]), true,true,true) := by rfl

-- The generic decoded source can alias the base. RSI labels do not determine
-- the point input, and a pending prefix receives no manufactured response.
def aliasSource := do
  let ⟨cell, before⟩ ← setup 0x9090c33fc10f48f0 0x9090909090909090 0x11223344ffff0000 99 123
  let entries : List (Entry Nat) := [.invoke 10 0 65536, .execute (.issue 0 false) (.rmw 10)]
  return ((replay ⟨0⟩ cell before entries).map fun (result : Result Nat ⟨0⟩ cell) =>
    (result.events, read result.state.state cell), checkComplete ⟨0⟩ cell before entries)

example : aliasSource = .ok
    (some ([.invoke 10 0 65536, .point ⟨10,0,65536,0x11223344ffff0000⟩],
      .ok 0x1122334500000000), false) := by rfl

def rspSource := do
  let ⟨cell, before⟩ ← setup 0x9090c327c10f48f0 0x9090909090909090 131072 1 2
  let entries : List (Entry Nat) := [.invoke 10 0 262144, .execute (.issue 0 false) (.rmw 10)]
  return ((replay ⟨0⟩ cell before entries).map fun (result : Result Nat ⟨0⟩ cell) =>
      (result.events, read result.state.state cell,
        OS.Borrowing.loadWord64 result.state.state.world.legacy.shared 11 0 262144),
    (replay ⟨0⟩ cell before (entries ++
      ([.execute (.issue 0 false) (.response 10 0 0)] : List (Entry Nat)))).isNone)

example : rspSource = .ok
    (some ([.invoke 10 0 262144, .point ⟨10,0,262144,131072⟩], .ok 393216, .ok 0x7000), true) := by rfl

end EDSL.Tests.FetchAddCalls64

#print axioms EDSL.OS.FetchAddCalls64.rmw_origin
#print axioms EDSL.OS.FetchAddCalls64.returned_origin
#print axioms EDSL.OS.FetchAddCalls64.checked_complete
#audit_edsl
