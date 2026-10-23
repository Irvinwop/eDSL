/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.ModuloCounter
import EDSL.OS.AddRMWMachine64
import EDSL.OS.TSO64.Run

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.ArithmeticRMWOrigin64
open X86 Concurrency

abbrev Call (Id : Type) := ModuloCounter.Call 64 Id Nat

/-- Occurrence identity and scheduler index are annotations. The input and
old word are captured from the complete checked arithmetic event. -/
def call {Id : Type} (id : Id) (tid : Nat) (event : Atomics64.FetchAddEvent) : Call Id :=
  ⟨id, tid, event.arithmetic.delta, event.arithmetic.event.before⟩

/-- Instruction-independent prerequisites for one installed arithmetic RMW.
The current code/caller leases, code bounds and atomic grant belong to the
selected worker. The joint effect authenticates the actual current RAM decode,
checked OS authorization, prestate address/delta and complete CPU/OS response.

This predicate does not assert an executable scheduler step or a dispatch
converse. `of_step` below lifts an actual successful step under either
instruction family and either authority profile, including its exact current
installation. The default family retains XADD-only dispatch. -/
structure Evidence {Id : Type} (target : Atomics64.CellId64) (before : TSO64.State)
    (action : TSO64.Action) (result : TSO64.State × TSO64.Observation) (point : Call Id)
    (event : Atomics64.FetchAddEvent) (af : Bool) (worker : TSO64.Worker)
    (instruction : AddRMW64.Instruction) (identifier : Atomics64.HandleId64)
    (machine : AddRMW64.Observation) : Prop where
  observed : result.2 = .rmw point.thread event
  issued : action = .issue point.thread af
  live : before.workers[point.thread]? = some worker
  running : worker.phase ≠ .returned
  codeLease : TSO64.LeaseCurrent before.world worker.resources.actor worker.resources.code
  callerLease : TSO64.LeaseCurrent before.world worker.resources.actor worker.resources.caller
  bounds : TSO64.codeFits worker instruction.length
  empty : worker.pending = []
  grant : identifier ∈ worker.resources.atomics
  effect : Atomics64.AddRMWMachineEffect before.world worker.resources.actor identifier
    (TSO64.sharedCPU before worker) instruction (result.1.world, event) machine
  selected : event.cell = target
  input : point.input = instruction.delta (TSO64.sharedCPU before worker)
  output : point.output = event.arithmetic.event.before
  installed : result.1 = TSO64.install before point.thread result.1.world
    { worker with context := .ofCPU machine.state }

def Origin {Id : Type} (target : Atomics64.CellId64) (before : TSO64.State)
    (action : TSO64.Action) (result : TSO64.State × TSO64.Observation) (point : Call Id) : Prop :=
  ∃ event af worker instruction identifier machine,
    Evidence target before action result point event af worker instruction identifier machine

namespace Evidence
section Generic
variable {Id : Type} {target : Atomics64.CellId64} {before : TSO64.State}
  {action : TSO64.Action} {result : TSO64.State × TSO64.Observation} {point : Call Id}
  {event : Atomics64.FetchAddEvent} {af : Bool} {worker : TSO64.Worker}
  {instruction : AddRMW64.Instruction} {identifier : Atomics64.HandleId64}
  {machine : AddRMW64.Observation}
  (origin : Evidence target before action result point event af worker instruction identifier machine)
include origin

/-- The event input is the captured instruction delta, never a difference of
old/new values and never an invented source for ADD or INC. -/
theorem delta : event.arithmetic.delta = point.input :=
  origin.effect.delta.trans origin.input.symm

/-- The scheduler index is not substituted for the resource actor or handle. -/
theorem actor_handle : event.actor = worker.resources.actor ∧ event.handle = identifier :=
  origin.effect.actor_handle

/-- Actual current authorization, including the selected persistent cell.
No WellFormed premise or cached issuance-time authority is used here. -/
theorem authorized : ∃ handle cell,
    Atomics64.authorize before.world worker.resources.actor identifier = .ok (handle, cell) ∧
    handle.cell = target ∧ before.world.cells target = some cell ∧
    event.arithmetic.event.address = cell.address := by
  obtain ⟨handle, cell, authorized, _event, _stored⟩ :=
    Atomics64.fetchAdd_guarded _ _ _ _ _ origin.effect.checked
  have identity := Atomics64.fetchAdd_identity _ _ _ _ _ _ _ origin.effect.checked authorized
  have selected : handle.cell = target := identity.1.symm.trans origin.selected
  have linked := (Atomics64.authorize_ok _ _ _ _ authorized).2.2.1
  rw [selected] at linked
  exact ⟨handle, cell, authorized, selected, linked, identity.2⟩

/-- Independent modular-counter contract for the captured full-width input. -/
theorem arithmetic : ModuloCounter.Step point.output point.input point.output
    event.arithmetic.event.after := by
  apply ModuloCounter.step_iff.mpr
  have addition := (Atomics64.fetchAdd_sound _ _ _ _ _ origin.effect.checked).2.2.1
  rw [← origin.output, ← origin.input] at addition
  exact ⟨rfl, addition⟩

/-- Bind both actual endpoint reads to the selected current descriptor.
The proof uses the checked RMW's old read and readback, independent of a
scheduler-specific history projection or any old-value destination register. -/
theorem projection {cell : Atomics64.Cell} {prior next : Word}
    (live : before.world.cells target = some cell)
    (readBefore : loadQWord (TSO64.published before.world) cell.address = .ok prior)
    (readAfter : loadQWord (TSO64.published result.1.world) cell.address = .ok next) :
    ModuloCounter.Step prior point.input point.output next := by
  obtain ⟨_handle, actual, _authorized, _selected, linked, address⟩ := origin.authorized
  have same : actual = cell := Option.some.inj (linked.symm.trans live)
  subst actual
  have old := Atomics64.fetchAdd_old _ _ _ _ _ origin.effect.checked
  have readback := Atomics64.fetchAdd_readback _ _ _ _ _ origin.effect.checked
  rw [address] at old readback
  have priorEq : point.output = prior :=
    origin.output.trans (Except.ok.inj (old.symm.trans readBefore))
  have nextEq : next = event.arithmetic.event.after :=
    Except.ok.inj (readAfter.symm.trans readback)
  rw [← priorEq, nextEq]
  exact origin.arithmetic

theorem installed_worker : result.1.workers[point.thread]? =
    some { worker with context := .ofCPU machine.state } := by
  rw [origin.installed]
  exact List.getElem?_set_self (List.getElem_of_getElem? origin.live).1

/-- Generic register framing uses the optional destination. It supplies no
old-value writeback or ABI response promise for instructions without one. -/
theorem register_frame (register : Register) (other : instruction.oldDestination ≠ some register) :
    result.1.workers[point.thread]?.map (fun current => current.context.registers register) =
      some (worker.context.registers register) := by
  rw [origin.installed_worker]
  exact congrArg some (origin.effect.register_frame register other)

theorem all_registers (noDestination : instruction.oldDestination = none) :
    result.1.workers[point.thread]?.map (fun current => current.context.registers) =
      some worker.context.registers := by
  rw [origin.installed_worker]
  exact congrArg some (origin.effect.all_registers noDestination)

end Generic

/-- Compatibility facts are explicitly tagged XADD, including base/source
aliases and source RSP. They are not part of generic arithmetic origins. -/
theorem xadd_effect {Id : Type} {target : Atomics64.CellId64} {before : TSO64.State}
    {action : TSO64.Action} {result : TSO64.State × TSO64.Observation} {point : Call Id}
    {event : Atomics64.FetchAddEvent} {af : Bool} {worker : TSO64.Worker}
    {old : LockedAdd64.Instruction} {identifier : Atomics64.HandleId64}
    {machine : AddRMW64.Observation}
    (origin : Evidence target before action result point event af worker (.xadd old) identifier machine) :
    Atomics64.FetchAddMachineEffect before.world worker.resources.actor identifier
      (TSO64.sharedCPU before worker) old (result.1.world, event) machine := origin.effect.xadd

theorem xadd_source_input {Id : Type} {target : Atomics64.CellId64} {before : TSO64.State}
    {action : TSO64.Action} {result : TSO64.State × TSO64.Observation} {point : Call Id}
    {event : Atomics64.FetchAddEvent} {af : Bool} {worker : TSO64.Worker}
    {old : LockedAdd64.Instruction} {identifier : Atomics64.HandleId64}
    {machine : AddRMW64.Observation}
    (origin : Evidence target before action result point event af worker (.xadd old) identifier machine) :
    point.input = (TSO64.sharedCPU before worker).registers old.source := origin.input

theorem xadd_source_old {Id : Type} {target : Atomics64.CellId64} {before : TSO64.State}
    {action : TSO64.Action} {result : TSO64.State × TSO64.Observation} {point : Call Id}
    {event : Atomics64.FetchAddEvent} {af : Bool} {worker : TSO64.Worker}
    {old : LockedAdd64.Instruction} {identifier : Atomics64.HandleId64}
    {machine : AddRMW64.Observation}
    (origin : Evidence target before action result point event af worker (.xadd old) identifier machine) :
    result.1.workers[point.thread]?.map (fun current => current.context.registers old.source) =
      some point.output := by
  rw [origin.installed_worker]
  exact congrArg some (origin.effect.source_old.trans origin.output.symm)

/-- Even XADD yields RAX = old only with an explicit RAX destination. This
local consequence supplies neither a RET origin nor a full ABI certificate. -/
theorem xadd_rax {Id : Type} {target : Atomics64.CellId64} {before : TSO64.State}
    {action : TSO64.Action} {result : TSO64.State × TSO64.Observation} {point : Call Id}
    {event : Atomics64.FetchAddEvent} {af : Bool} {worker : TSO64.Worker}
    {old : LockedAdd64.Instruction} {identifier : Atomics64.HandleId64}
    {machine : AddRMW64.Observation}
    (origin : Evidence target before action result point event af worker (.xadd old) identifier machine)
    (destination : old.source = .rax) :
    result.1.workers[point.thread]?.map (fun current => current.context.registers .rax) =
      some point.output := by
  simpa only [destination] using origin.xadd_source_old

end Evidence

theorem Origin.projection {Id : Type} {target : Atomics64.CellId64} {before : TSO64.State}
    {action : TSO64.Action} {result : TSO64.State × TSO64.Observation} {point : Call Id}
    (origin : Origin target before action result point) {cell : Atomics64.Cell} {prior next : Word}
    (live : before.world.cells target = some cell)
    (readBefore : loadQWord (TSO64.published before.world) cell.address = .ok prior)
    (readAfter : loadQWord (TSO64.published result.1.world) cell.address = .ok next) :
    ModuloCounter.Step prior point.input point.output next := by
  obtain ⟨_event, _af, _worker, _instruction, _identifier, _machine, evidence⟩ := origin
  exact evidence.projection live readBefore readAfter

/-- An unchanged arithmetic result still has a real RMW observation and one
retired instruction. Event occurrence does not depend on a nonzero delta. -/
theorem Origin.observed {Id : Type} {target : Atomics64.CellId64} {before : TSO64.State}
    {action : TSO64.Action} {result : TSO64.State × TSO64.Observation} {point : Call Id}
    (origin : Origin target before action result point) :
    ∃ event, result.2 = .rmw point.thread event ∧ event.cell = target ∧
      event.arithmetic.delta = point.input ∧ event.arithmetic.event.before = point.output ∧
      result.2.retired = 1 := by
  obtain ⟨event, _af, _worker, _instruction, _identifier, _machine, evidence⟩ := origin
  exact ⟨event, evidence.observed, evidence.selected, evidence.delta, evidence.output.symm,
    by rw [evidence.observed]; rfl⟩

/-- Lift an actual current scheduler event from either instruction family and
either authority profile into the common captured-delta interface. The actual
step supplies the current dispatch gates; no Origin-to-step converse is asserted. -/
theorem of_step {Id : Type} {target : Atomics64.CellId64} {before after : TSO64.State}
    {action : TSO64.Action} {tid : Nat} {event : Atomics64.FetchAddEvent}
    {profile : TSO64.Profile} {family : TSO64.RMWFamily}
    (id : Id) (success : TSO64.step before action profile family = .ok (after, .rmw tid event))
    (selected : event.cell = target) :
    Origin target before action (after, .rmw tid event) (call id tid event) := by
  cases TSO64.step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue executed finish => cases finish
  | @rmw family _ af worker instruction identifier output machine _
      live running code caller fetched bounds empty grant effect =>
    have arithmetic := TSO64.RMWFamily.MachineEffect.arithmetic effect
    refine ⟨output.2, af, worker, family.embed instruction, identifier, machine, ?_⟩
    exact ⟨rfl, rfl, live, running, code, caller, bounds, empty, grant,
      arithmetic, selected, arithmetic.delta, rfl, rfl⟩

/-- A blocked own-FIFO attempt retains the whole scheduler state, retires
nothing and cannot carry an RMW event. It is not an installed arithmetic RMW. -/
theorem blocked {before after : TSO64.State} {action : TSO64.Action} {tid : Nat}
    {profile : TSO64.Profile} {family : TSO64.RMWFamily}
    (success : TSO64.step before action profile family = .ok (after, .blocked tid)) :
    after = before ∧ (TSO64.Observation.blocked tid).retired = 0 ∧
      ∀ issuer event, (TSO64.Observation.blocked tid) ≠ .rmw issuer event := by
  refine ⟨TSO64.blocked_unchanged success, rfl, ?_⟩
  intro issuer event same
  cases same

end EDSL.OS.ArithmeticRMWOrigin64

#print axioms EDSL.OS.ArithmeticRMWOrigin64.Evidence.delta
#print axioms EDSL.OS.ArithmeticRMWOrigin64.Evidence.actor_handle
#print axioms EDSL.OS.ArithmeticRMWOrigin64.Evidence.authorized
#print axioms EDSL.OS.ArithmeticRMWOrigin64.Evidence.arithmetic
#print axioms EDSL.OS.ArithmeticRMWOrigin64.Evidence.projection
#print axioms EDSL.OS.ArithmeticRMWOrigin64.Evidence.installed_worker
#print axioms EDSL.OS.ArithmeticRMWOrigin64.Evidence.register_frame
#print axioms EDSL.OS.ArithmeticRMWOrigin64.Evidence.all_registers
#print axioms EDSL.OS.ArithmeticRMWOrigin64.Evidence.xadd_effect
#print axioms EDSL.OS.ArithmeticRMWOrigin64.Evidence.xadd_source_input
#print axioms EDSL.OS.ArithmeticRMWOrigin64.Evidence.xadd_source_old
#print axioms EDSL.OS.ArithmeticRMWOrigin64.Evidence.xadd_rax
#print axioms EDSL.OS.ArithmeticRMWOrigin64.Origin.projection
#print axioms EDSL.OS.ArithmeticRMWOrigin64.Origin.observed
#print axioms EDSL.OS.ArithmeticRMWOrigin64.of_step
#print axioms EDSL.OS.ArithmeticRMWOrigin64.blocked
#audit_edsl
