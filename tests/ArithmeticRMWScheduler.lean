/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures
import tests.Support.ExceptDecidable
import EDSL.OS.TSO64.WordProjection
import EDSL.Audit

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.ArithmeticRMWScheduler
open X86 OS.TSO64
open scoped EDSL.Tests.Support

-- Stage computational equality for the nested read result and finite views.
-- Each closed instance is reused by the outer Except decision, so synthesis
-- need not reconstruct every nested product in one search.
local instance : DecidableEq (Except Error Word) := inferInstance
local instance : DecidableEq (Nat × Word × Word × Word) := inferInstance
local instance : DecidableEq (Except Error Word × Option Bool × Option Bool) := inferInstance
local instance : DecidableEq
    (Except Error Word × Except Error Word × List WordProjection.ReferenceLabel) := inferInstance
local instance : DecidableEq
    (List (Nat × Word × Word × Word) × Nat × List Nat × Except Error Word ×
      Option Bool × Option Bool) := inferInstance
local instance : DecidableEq
    (List (Nat × Word × Word × Word) × List Nat × Option Nat × Except Error Word ×
      Except Error Word × List WordProjection.ReferenceLabel) := inferInstance
local instance : DecidableEq
    (List (Nat × Word × Word × Word) × Nat × Option (Word × Bool) ×
      Except Error Word) := inferInstance

structure Checked (profile : Profile) where
  state : OS.TSO64.State
  valid : WellFormed state profile

def attachChecked {profile : Profile} (before : Checked profile) (actor : Nat)
    (context : Context) (code caller : Nat) (grants : List OS.Ownership.Ticket)
    (atomics : List OS.Atomics64.HandleId64) : Except Fault (Checked profile) :=
  match success : attach before.state actor context code caller grants atomics with
  | .error fault => .error fault
  | .ok after => .ok ⟨after, attach_valid_for profile before.valid success⟩

/-- Retain the invariant proved for the actual arithmetic-family schedule. -/
def advance {profile : Profile} (before : Checked profile) (actions : List Action) :
    Except Fault (Checked profile) :=
  match success : schedule before.state actions profile .arithmetic with
  | .error fault => .error fault
  | .ok result => .ok ⟨result.1, schedule_wellFormed before.valid success⟩

/-- The production executor and annotation accessor supply the path witness;
the test does not evaluate a separate reference scheduler. -/
def certifiedRun {profile : Profile} (before : Checked profile) (actions : List Action) :
    Except Fault
      { output : (OS.TSO64.State × List Observation) × List WordProjection.ReferenceLabel //
        WordProjection.ScheduleTrace profile before.state actions output.1 output.2 .arithmetic ∧
        Concurrency.TSOWord.Path (WordProjection.project before.state) output.2
          (WordProjection.project output.1.1) } :=
  match success : schedule before.state actions profile .arithmetic with
  | .error fault => .error fault
  | .ok result =>
    match annotated : WordProjection.scheduleLabels before.state actions profile .arithmetic with
    | .error fault => .error fault
    | .ok labels => .ok ⟨(result, labels),
        WordProjection.schedule_labels_sound before.valid success annotated⟩

/-- ADD/INC frame the entire register function. CF follows the decoded tag,
even when INC's sum carry differs from incoming CF. The premise is an actual
guarded scheduler step, including its exact installed context. -/
theorem actual_registers_and_carry {before after : OS.TSO64.State} {tid : Nat} {af : Bool}
    {worker : Worker} {instruction : X86.AddRMW64.Instruction}
    {event : OS.Atomics64.FetchAddEvent} {profile : Profile}
    (live : before.workers[tid]? = some worker)
    (fetched : decode (fetchCPU before worker) .arithmetic = .ok (.locked instruction))
    (noDestination : instruction.oldDestination = none)
    (success : step before (.issue tid af) profile .arithmetic = .ok (after, .rmw tid event)) :
    ∃ current, after.workers[tid]? = some current ∧
      current.context.registers = worker.context.registers ∧
      current.context.flags.getLsbD 0 =
        (if instruction.isInc then worker.context.flags.getLsbD 0
          else event.arithmetic.event.before.uaddOverflow event.arithmetic.delta) := by
  cases step_origin success with
  | ordinary originLive running code caller originFetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue executed finish => cases finish
  | @rmw _ _ _ issuing actual identifier output machine _ originLive running code caller originFetched bounds empty grant effect =>
    have sameWorker : issuing = worker := Option.some.inj (originLive.symm.trans live)
    subst issuing
    have sameInstruction : actual = instruction :=
      OS.TSO64.Decoded.locked.inj (Except.ok.inj (originFetched.symm.trans fetched))
    subst actual
    have arithmetic : OS.Atomics64.AddRMWMachineEffect before.world worker.resources.actor identifier
        (sharedCPU before worker) instruction output machine := effect
    refine ⟨{ worker with context := .ofCPU machine.state },
      List.getElem?_set_self (List.getElem_of_getElem? live).1, ?_, ?_⟩
    · exact arithmetic.all_registers noDestination
    · exact arithmetic.cpu.flag_bits.1

/-- These are code bindings in the shared checked fixture, not a dispatcher.
Each entry RIP is still fetched from the current original executable loan. -/
def start (first second old : Word) (profile : Profile) (offsetA offsetB : Word := 0) :
    Except Fault (Checked profile) := do
  let ready ← (TSO64.fixture first second old).mapError Fault.os
  let seed : Checked profile := ⟨⟨ready.checked.world, []⟩, ⟨ready.checked.valid, by simp⟩⟩
  let a := { TSO64.context 262144 131072 7 99 with rip := 393216 + offsetA }
  let b := { TSO64.context 327680 196608 11 123 with
    rip := 393216 + offsetB, flags := 0x200203 }
  let one ← attachChecked seed 11 a ready.codeA ready.callerA [ready.dataA] [ready.atomicA]
  attachChecked one 12 b ready.codeB ready.callerB [ready.dataB] [ready.atomicB]

-- LOCK ADD [RDI],-1; LOCK INC [RDI]; LOCK ADD [RDI],0; RET.
def mixedLow : Word := 0xff48f0ff078348f0
def mixedHigh : Word := 0x00c300078348f007

def mixedActions : List Action :=
  [.issue 0 false, .issue 1 true, .issue 1 false, .issue 0 true]

def interleaving : Except Fault
    (List (Nat × Word × Word × Word) × Nat × List Nat × Except Error Word ×
      Option Bool × Option Bool) := do
  let before ← start mixedLow mixedHigh 0x1122334500000000 .ownedOnly 0 5
  let result ← schedule before.state mixedActions .ownedOnly .arithmetic
  return (TSO64.events result.2, result.2.length, result.2.map Observation.retired,
    loadQWord (published result.1.world) 65536,
    (result.1.workers[0]?).map (fun (current : Worker) => current.context.flags.getLsbD 0),
    (result.1.workers[1]?).map (fun (current : Worker) => current.context.flags.getLsbD 0))

/-- Real interleaving crosses bit32 in both directions, captures the current
old word in order, and retains the zero-delta occurrence. ADD sets CF from
arithmetic; the later INC retains it, while ADD zero clears stale CF. RSI and
RAX inputs deliberately differ from every instruction's immediate delta. -/
theorem actual_interleaving : interleaving = .ok
    ([(0,0xffffffffffffffff,0x1122334500000000,0x11223344ffffffff),
      (1,1,0x11223344ffffffff,0x1122334500000000),
      (1,0,0x1122334500000000,0x1122334500000000),
      (0,1,0x1122334500000000,0x1122334500000001)],
      4, [1,1,1,1], .ok 0x1122334500000001, some true, some false) := by
  decide +kernel

def zeroLabels : Except Fault (List WordProjection.ReferenceLabel) := do
  let before ← start mixedLow mixedHigh 0x1122334500000000 .sharedCell 9 5
  return (← certifiedRun before [.issue 0 false]).val.2

/-- Unchanged memory still has the complete five-label reference path under
the other authority profile; certifiedRun retains its actual soundness proof. -/
theorem zero_is_a_complete_rmw_path : zeroLabels = .ok
    [.lock 0, .read 0 ⟨0⟩ 0x1122334500000000,
      .write 0 ⟨0⟩ 0x1122334500000000, .tau, .unlock 0] := by
  decide +kernel

-- MOV [RDX],RSI; LOCK INC [RDI]; LOCK ADD [RDI],0; RET.
def fifoQueued : Except Fault (Checked .sharedCell) := do
  let before ← start 0xf007ff48f0328948 0x909090c300078348
    0x11223344ffffffff .sharedCell
  advance before [.issue 0 false, .issue 1 false]

/-- Observe the real enqueue and next issue without comparing states or
expanding the invariant proofs carried by a successful checked result. -/
private def fifoBlockedView : Except Fault
    (Option Nat × List (OS.Atomics64.CellId64 × Word) × Except Fault Observation) :=
  fifoQueued.map fun before =>
    ((before.state.workers[0]?).map (fun (current : Worker) => current.pending.length),
      WordProjection.buffers before.state 0,
      (step before.state (.issue 0 false) .sharedCell .arithmetic).map Prod.snd)

private theorem fifo_blocked_view : fifoBlockedView = .ok (some 1, [], .ok (.blocked 0)) := by
  decide +kernel

/-- Derive full state equality from the actual blocked observation, using the
executor's universal frame theorem rather than a state equality decision. -/
private theorem blocked_step_of_observation {before : OS.TSO64.State} {action : Action}
    {profile : Profile} {family : RMWFamily} {tid : Nat}
    (observed : (step before action profile family).map Prod.snd = .ok (.blocked tid)) :
    step before action profile family = .ok (before, .blocked tid) := by
  cases executed : step before action profile family with
  | error fault => simp only [executed, Except.map, reduceCtorEq] at observed
  | ok result =>
    rcases result with ⟨after, observation⟩
    have same : observation = .blocked tid := by
      simpa only [executed, Except.map, Except.ok.injEq] using observed
    subst observation
    have unchanged : after = before := blocked_unchanged executed
    exact congrArg (fun state : OS.TSO64.State =>
      (Except.ok (state, .blocked tid) : Except Fault (OS.TSO64.State × Observation))) unchanged

/-- Nonvacuous whole-state blocking: the actual ordinary enqueue is absent
from the managed projection but still blocks the locked issue. The sole
observation is blocked (zero events and zero retirement), with no labels. -/
theorem ordinary_fifo_blocks_whole_state :
    ∃ before : Checked .sharedCell, fifoQueued = .ok before ∧
      (before.state.workers[0]?).map (fun (current : Worker) => current.pending.length) = some 1 ∧
      WordProjection.buffers before.state 0 = [] ∧
      schedule before.state [.issue 0 false] .sharedCell .arithmetic =
        .ok (before.state, [.blocked 0]) ∧
      WordProjection.scheduleLabels before.state [.issue 0 false] .sharedCell .arithmetic =
        .ok [] := by
  have view := fifo_blocked_view
  cases queued : fifoQueued with
  | error fault => simp only [fifoBlockedView, queued, Except.map, reduceCtorEq] at view
  | ok before =>
    have projections :
        (before.state.workers[0]?).map (fun (current : Worker) => current.pending.length) = some 1 ∧
        WordProjection.buffers before.state 0 = [] ∧
        (step before.state (.issue 0 false) .sharedCell .arithmetic).map Prod.snd =
          .ok (.blocked 0) := by
      simpa only [fifoBlockedView, queued, Except.map, Except.ok.injEq, Prod.mk.injEq] using view
    rcases projections with ⟨pending, erased, observed⟩
    have blocked := blocked_step_of_observation observed
    refine ⟨before, rfl, pending, erased, ?_, ?_⟩
    · simp only [schedule, blocked, ok_bind, pure_ok]
    · simp only [WordProjection.scheduleLabels, blocked, ok_bind, pure_ok,
        WordProjection.stepLabels, List.nil_append]

def peerPending : Except Fault
    (List (Nat × Word × Word × Word) × List Nat × Option Nat × Except Error Word ×
      Except Error Word × List WordProjection.ReferenceLabel) := do
  let before ← fifoQueued
  let output ← certifiedRun before [.drain 0, .issue 0 false, .issue 1 true]
  let result := output.val.1
  return (TSO64.events result.2, result.2.map Observation.retired,
    (result.1.workers[1]?).map (fun (current : Worker) => current.pending.length),
    loadQWord (published result.1.world) 131072,
    loadQWord (published result.1.world) 196608, output.val.2)

/-- Draining only the own head enables exactly one INC while the peer's
ordinary head stays pending and its own attempt stays blocked. -/
theorem peer_fifo_does_not_block : peerPending = .ok
    ([(0,1,0x11223344ffffffff,0x1122334500000000)], [0,1,0], some 1,
      .ok 7, .ok 0,
      [.lock 0, .read 0 ⟨0⟩ 0x11223344ffffffff,
        .write 0 ⟨0⟩ 0x1122334500000000, .tau, .unlock 0]) := by
  decide +kernel

/-- Narrow the original code through an actual additional checked read loan.
Executable backing extends past it, so fetch confinement is tested as well as
instruction length. No synthetic resource descriptor is installed. -/
def boundaryStart (first : Word) (width : Nat) : Except Fault (Checked .ownedOnly) := do
  let ready ← (TSO64.fixture first 0 0xffffffffffffffff).mapError Fault.os
  let original ← (OS.Borrowing.authorize ready.checked.world.legacy.shared 11 ready.codeA).mapError Fault.loan
  let (narrowed, code) ← (TSO64.borrow ready.checked original.lender original.ticket
    11 ⟨393216,width⟩).mapError Fault.os
  let seed : Checked .ownedOnly := ⟨⟨narrowed.world, []⟩, ⟨narrowed.valid, by simp⟩⟩
  attachChecked seed 11 (TSO64.context 262144 131072 7 99)
    code ready.callerA [ready.dataA] [ready.atomicA]

def boundaryView (first : Word) (width : Nat) (family : RMWFamily := .xaddOnly) :
    Except Fault
      (List (Nat × Word × Word × Word) × Nat × Option (Word × Bool) × Except Error Word) := do
  let before ← boundaryStart first width
  let result ← step before.state (.issue 0 false) .ownedOnly family
  return (TSO64.events [result.2], result.2.retired,
    (result.1.workers[0]?).map (fun (current : Worker) =>
      (current.context.rip, current.context.flags.getLsbD 0)),
    loadQWord (published result.1.world) 65536)

/-- INC needs exactly four loaned executable bytes and preserves clear CF
even on full64 wrap. An eager five-byte dispatcher would reject this run. -/
theorem four_byte_inc : boundaryView 0x07ff48f0 4 .arithmetic = .ok
    ([(0,1,0xffffffffffffffff,0)], 1, some (393220,false), .ok 0) := by
  decide +kernel

theorem inc_needs_its_fourth_byte : boundaryView 0x07ff48f0 3 .arithmetic =
    .error (.machine (.inaccessibleInstruction 393219)) := by
  decide +kernel

theorem add_needs_its_fifth_byte : boundaryView 0x01078348f0 4 .arithmetic =
    .error (.machine (.inaccessibleInstruction 393220)) := by
  decide +kernel

/-- The matching ADD wrap sets CF, and succeeds with its real fifth byte. -/
theorem five_byte_add : boundaryView 0x01078348f0 5 .arithmetic = .ok
    ([(0,1,0xffffffffffffffff,0)], 1, some (393221,true), .ok 0) := by
  decide +kernel

theorem default_inc_retains_eager_fetch : boundaryView 0x07ff48f0 4 =
    .error (.machine (.inaccessibleInstruction 393220)) := by
  decide +kernel

theorem default_rejects_inc : boundaryView 0x07ff48f0 5 =
    .error (.machine .unsupportedEncoding) := by
  decide +kernel

theorem default_rejects_add : boundaryView 0x01078348f0 5 =
    .error (.machine .unsupportedEncoding) := by
  decide +kernel

end EDSL.Tests.ArithmeticRMWScheduler

#print axioms EDSL.Tests.ArithmeticRMWScheduler.actual_registers_and_carry
#print axioms EDSL.OS.TSO64.WordProjection.rmw_path
#print axioms EDSL.OS.TSO64.WordProjection.schedule_labels_sound
#audit_edsl
