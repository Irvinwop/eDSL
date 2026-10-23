/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.Simulation
import EDSL.OS.TSO64.EffectSimulation.Mixed.Authority
import tests.Support.MixedBlockingFixture
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Independent obligations for the synthetic, exact LOCK INC [RDI]; RET window.
The fixture supplies present admission only. The generated proof reads current
shared RAM through the real coupled machine effect, and preserves historical
INC evidence across arbitrary admitted idle interference. Return specifies the
original caller ABI and resources; it does not freeze the shared counter.
-/

namespace EDSL.Tests.MixedResumableBlocking
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation
open OS.TSO64.EffectSimulation.Mixed
open scoped EDSL.Tests.Support

abbrev Fixture := EDSL.Tests.Support.MixedBlockingFixture.Fixture

/-- The constructor records encoding constraints; actual dispatch is checked below. -/
def inc : AddRMW64.Instruction := .inc {
  rex := 0x48, modrm := 0x07
  rexSupported := by decide +kernel
  indirect := by decide +kernel
  groupZero := by decide +kernel }

def bytes : List Byte := [0xf0, 0x48, 0xff, 0x07, 0xc3]

def graph : VCGen.MixedCFG.Graph .arithmetic :=
  ⟨[⟨0, .locked inc, true, 1⟩, ⟨4, .ordinary (.legacy .ret), false, 0⟩], 1⟩

def caps : VCGen.MixedCFG.Caps := ⟨5, 2, by decide +kernel⟩
abbrev incNode : graph.Index := ⟨0, by decide +kernel⟩
abbrev retNode : graph.Index := ⟨1, by decide +kernel⟩

local instance (source destination : graph.Index) : Decidable (graph.Edge source destination) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- The production mixed decoder and graph validator authenticate all five bytes. -/
theorem graph_checked : VCGen.MixedCFG.checkWith .arithmetic caps bytes graph = true := by
  decide +kernel

theorem structural : VCGen.MixedCFG.Valid .arithmetic caps bytes graph :=
  VCGen.MixedCFG.checkWith_sound graph_checked

private theorem inc_ret_edge : graph.Edge incNode retNode := by decide +kernel

/-- Ordinary policy independently admits only RET and the original caller read. -/
def policy (original : Worker) : VCGen.Effects.Policy where
  Current _ := True
  AllowedRead _ read := read.kind = .stack ∧
    read.address = original.resources.callerAddress ∧ read.bytes = 8
  AllowedEffect _ instruction _ := instruction = .legacy .ret

def descriptor (fixture : Fixture) : Descriptor where
  family := .arithmetic
  profile := .sharedCell
  tid := 0
  bytes := bytes
  base := 393216
  graph := graph
  caps := caps
  structural := structural
  original := fixture.own
  codeLoan := fixture.ownFits
  callerValue := 0x7000
  policy _ := policy fixture.own

private theorem original_actor (fixture : Fixture) : fixture.own.resources.actor = 11 :=
  congrArg Prod.fst fixture.ownResources

private theorem original_atomics (fixture : Fixture) :
    fixture.own.resources.atomics = [fixture.issued.identifier, fixture.issued.ready.atomicA] :=
  congrArg (fun view : Nat × Nat × Nat × Word × List Ownership.Ticket ×
    List Atomics64.HandleId64 => view.2.2.2.2.2) fixture.ownResources

private theorem original_caller_address (fixture : Fixture) :
    fixture.own.resources.callerAddress = 262144 :=
  congrArg (fun view : Nat × Nat × Nat × Word × List Ownership.Ticket ×
    List Atomics64.HandleId64 => view.2.2.2.1) fixture.ownResources

/-- Present inputs only: both handles are valid, in reverse creation order.
No RAM value, generated obligation or execution result appears here. -/
structure Inputs (fixture : Fixture) (state : S) (worker : Worker) : Prop where
  rdi : worker.context.registers .rdi = 65536
  rsp : worker.context.registers .rsp = fixture.own.resources.callerAddress
  actor : worker.resources.actor = 11
  atomics : worker.resources.atomics = [fixture.issued.identifier, fixture.issued.ready.atomicA]
  fresh : Atomics64.authorize state.world 11 fixture.issued.identifier =
    .ok (fixture.fresh.handle, fixture.fresh.cell)
  old : Atomics64.authorize state.world 11 fixture.issued.ready.atomicA =
    .ok (fixture.old.handle, fixture.old.cell)

private theorem Inputs.chosen {fixture : Fixture} {state : S} {worker : Worker}
    (inputs : Inputs fixture state worker) :
    EDSL.OS.TSO64.atomicFor state.world worker.resources 65536 =
      some (fixture.issued.identifier, fixture.fresh.handle, fixture.fresh.cell) := by
  have address : fixture.fresh.cell.address = 65536 :=
    (congrArg Atomics64.Cell.address fixture.commonCell.1).trans fixture.counterAddress
  simp [EDSL.OS.TSO64.atomicFor, inputs.atomics, inputs.actor, inputs.fresh, address]

/-- Saved context and current authorizations survive, without any RAM equality. -/
private theorem inputs_idle {fixture : Fixture} {before after : S}
    {history extended : Log} {worker : Worker}
    (binding : Binding (descriptor fixture) incNode before worker)
    (inputs : Inputs fixture before worker)
    (idle : Idle .sharedCell 0 (before, history) (after, extended) .arithmetic) :
    ∃ current, Binding (descriptor fixture) incNode after current ∧
      Inputs fixture after current ∧
      EDSL.OS.TSO64.atomicFor after.world current.resources 65536 =
        some (fixture.issued.identifier, fixture.fresh.handle, fixture.fresh.cell) := by
  obtain ⟨current, live, saved, selection⟩ := idle.atomic_selection binding.live 65536
  refine ⟨current, ⟨live, saved.resources.trans binding.resources,
    saved.phase.trans binding.running, (congrArg Context.rip saved.context).trans binding.pc⟩,
    ?_, selection.trans inputs.chosen⟩
  exact ⟨(congrArg (fun context : Context => context.registers .rdi) saved.context).trans inputs.rdi,
    (congrArg (fun context : Context => context.registers .rsp) saved.context).trans inputs.rsp,
    (congrArg Resources.actor saved.resources).trans inputs.actor,
    (congrArg Resources.atomics saved.resources).trans inputs.atomics,
    (idle.authorize 11 fixture.issued.identifier).trans inputs.fresh,
    (idle.authorize 11 fixture.issued.ready.atomicA).trans inputs.old⟩

/-- An actual selected INC retirement at this exact history position. -/
def OwnInc (fixture : Fixture) (tick : Tick) : Prop :=
  ∃ (worker : Worker) (af : Bool) (output : World × Atomics64.FetchAddEvent)
      (machine : AddRMW64.Observation),
    Binding (descriptor fixture) incNode tick.before worker ∧
    tick.action = .issue 0 af ∧
    tick.result = (install tick.before 0 output.1
      { worker with context := .ofCPU machine.state }, .rmw 0 output.2) ∧
    AtomicIssued (descriptor fixture) incNode tick.before af tick.result output machine ∧
    EDSL.OS.TSO64.atomicFor tick.before.world worker.resources 65536 =
      some (fixture.issued.identifier, fixture.fresh.handle, fixture.fresh.cell) ∧
    output.2.handle = fixture.issued.identifier ∧ output.2.actor = 11 ∧
    output.2.arithmetic.event.address = 65536 ∧ output.2.arithmetic.delta = 1 ∧
    loadQWord (published tick.before.world) 65536 = .ok output.2.arithmetic.event.before ∧
    output.2.arithmetic.event.after = output.2.arithmetic.event.before + 1 ∧
    machine.state.rip = worker.context.rip + 4

def IncOccurred (fixture : Fixture) (history : Log) : Prop :=
  ∃ tick ∈ history, OwnInc fixture tick

private theorem occurred_append {fixture : Fixture} {history : Log}
    (occurred : IncOccurred fixture history) (suffix : Log) :
    IncOccurred fixture (history ++ suffix) := by
  obtain ⟨tick, member, evidence⟩ := occurred
  exact ⟨tick, List.mem_append_left suffix member, evidence⟩

private theorem occurred_idle {fixture : Fixture} {before after : S}
    {history extended : Log} (occurred : IncOccurred fixture history)
    (idle : Idle .sharedCell 0 (before, history) (after, extended) .arithmetic) :
    IncOccurred fixture extended := by
  obtain ⟨suffix, _trace, _allowed, appended⟩ := idle
  change extended = history ++ suffix at appended
  rw [appended]
  exact occurred_append occurred suffix

/-- Historical INC, original resources and the actual original caller ABI.
Arbitrary idle peers may change current shared RAM after that INC. -/
def returnPost (fixture : Fixture) : Assertion := fun state history =>
  (∃ worker, state.workers[0]? = some worker ∧ worker.phase = .returned ∧
    worker.context.rip = 0x7000 ∧
    worker.context.registers .rsp = fixture.own.resources.callerAddress + 8 ∧
    worker.resources = fixture.own.resources) ∧ IncOccurred fixture history

def entryInv (fixture : Fixture) : CutAssertion (descriptor fixture) :=
  fun node state _history => node = incNode ∧
    ∃ worker, state.workers[0]? = some worker ∧ Inputs fixture state worker

private theorem current_caller {fixture : Fixture} {state : S} {worker : Worker}
    (frame : Frame (descriptor fixture) state)
    (binding : Binding (descriptor fixture) retNode state worker)
    (stack : worker.context.registers .rsp = fixture.own.resources.callerAddress) :
    checkRead state worker ⟨.stack, worker.context.registers .rsp, 8⟩ .sharedCell = .ok () ∧
      readWord (localCPU state worker).memory (worker.context.registers .rsp) = .ok 0x7000 := by
  have caller : Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
      worker.resources.caller.identifier worker.resources.callerAddress = .ok 0x7000 := by
    rw [binding.resources]
    exact frame.caller
  have currentStack : worker.context.registers .rsp = worker.resources.callerAddress := by
    rw [binding.resources]
    exact stack
  have workerValid := frame.wellFormed.2 worker (List.mem_of_getElem? binding.live)
  refine ⟨?_, ?_⟩
  · simp [checkRead, currentStack, caller, Except.mapError]
  · rw [currentStack, local_original_caller frame.wellFormed workerValid]
    exact readWord_of_loadQWord _ _ _
      (Borrowing.loadWord64_ok _ _ _ _ _ caller).choose_spec.2.2

private theorem queue_unchanged {state : S} {worker : Worker} {update : Queue.Cursor}
    (queue : QueueEffect state worker (.legacy .ret) update .sharedCell) :
    update = ⟨worker.pending, worker.nextStore⟩ := by
  cases queue with
  | unchanged _ => rfl
  | enqueued stored _ => cases stored

private theorem oneStep_uniform_ok {before : X86.State}
    {instruction : Sequential.Instruction} {observed : Sequential.Observation}
    {currentPolicy : VCGen.Effects.Policy} {K : Bool → Sequential.Observation → Prop}
    (single : instruction.boolChoiceProfile = true)
    (executed : ∀ af, Sequential.execute before instruction af = .ok observed)
    (current : currentPolicy.Current before)
    (permitted :
      (∀ operand ∈ observed.reads, currentPolicy.AllowedRead before operand) ∧
      currentPolicy.AllowedEffect before instruction observed ∧
      (∀ final, observed.result = .returned final → currentPolicy.Current final) ∧
      (∀ request, observed.result ≠ .syscall request) ∧
      ∀ af, K af observed) :
    VCGen.Effects.oneStep currentPolicy Sequential.FlagChoices.uniform before instruction K := by
  unfold VCGen.Effects.oneStep
  refine ⟨current, ?_⟩
  intro af
  rw [Sequential.executeWith_uniform before instruction af single, executed af]
  exact ⟨permitted.1, permitted.2.1, permitted.2.2.1, permitted.2.2.2.1,
    permitted.2.2.2.2 af⟩

/-- RET is generated from the retained borrowing read, its real queue and every
real FinishEffect. The postcondition is derived from the installed CPU. -/
theorem ret_generated (fixture : Fixture) {state : S} {history : Log}
    {worker : Worker} (frame : Frame (descriptor fixture) state)
    (binding : Binding (descriptor fixture) retNode state worker)
    (stack : worker.context.registers .rsp = fixture.own.resources.callerAddress)
    (occurred : IncOccurred fixture history) :
    rwp (descriptor fixture) (returnPost fixture) (entryInv fixture) 1 retNode state history := by
  change IdleBox .sharedCell 0 _ state history .arithmetic
  intro after extended idle
  have retained := frame.idle idle
  obtain ⟨current, live, saved⟩ := idle.saved binding.live
  have bound : Binding (descriptor fixture) retNode after current :=
    ⟨live, saved.resources.trans binding.resources, saved.phase.trans binding.running,
      (congrArg Context.rip saved.context).trans binding.pc⟩
  have currentRsp : current.context.registers .rsp = fixture.own.resources.callerAddress := by
    rw [saved.context]
    exact stack
  have historical := occurred_idle occurred idle
  obtain ⟨gate, read⟩ := current_caller retained bound currentRsp
  change checkRead after current ⟨.stack, (localCPU after current).registers .rsp, 8⟩
    .sharedCell = .ok () at gate
  have reads : ∃ units, ((Sequential.Instruction.legacy .ret).operandReads
      (localCPU after current)).mapM (fun operand => checkRead after current operand .sharedCell) =
        .ok units := by
    exact ⟨[()], by simp only [Sequential.Instruction.operandReads, List.mapM_cons,
      gate, ok_bind, List.mapM_nil, pure_ok]⟩
  have valid := bound.resourcesValid retained
  have ready : OrdinaryReady after 0 current (.legacy .ret) .sharedCell .arithmetic :=
    ⟨bound.live, bound.running, valid.1, valid.2.1, bound.fetched retained,
      by decide +kernel, bound.codeFits retained, reads,
      ⟨⟨current.pending, current.nextStore⟩, .unchanged rfl⟩⟩
  let output : X86.State := { (localCPU after current).writeRegister .rsp
    (current.context.registers .rsp + 8) with rip := 0x7000 }
  let observed : Sequential.Observation :=
    ⟨.returned output, [⟨.stack, current.context.registers .rsp, 8⟩]⟩
  have canonicalCaller : canonical (0x7000 : Word) = true := by decide +kernel
  have executed (af : Bool) : Sequential.execute (localCPU after current) (.legacy .ret) af =
      .ok observed := by
    change readWord (localCPU after current).memory ((localCPU after current).registers .rsp) =
      .ok 0x7000 at read
    simp only [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
      executeRet, read, canonicalCaller, ↓reduceIte, ok_bind, pure_ok]
    rfl
  refine ⟨retained, current, bound, ready, ?_⟩
  change VCGen.Effects.oneStep (policy fixture.own) Sequential.FlagChoices.uniform
    (localCPU after current) (.legacy .ret) _
  refine oneStep_uniform_ok (instruction := .legacy .ret) rfl executed True.intro ?_
  refine ⟨?_, rfl, (fun _ _ => True.intro), ?_, ?_⟩
  · intro operand member
    have same := List.mem_singleton.mp member
    subst operand
    exact ⟨rfl, currentRsp, rfl⟩
  · intro request impossible
    cases impossible
  · intro _af
    refine ⟨⟨output, Or.inr rfl⟩, ?_⟩
    intro update result queue finish
    have cursor := queue_unchanged queue
    subst update
    cases finish with
    | next impossible => cases impossible
    | returned outcome =>
      cases outcome
      refine ⟨⟨_, List.getElem?_set_self (List.getElem_of_getElem? bound.live).1,
        rfl, rfl, ?_, bound.resources⟩, occurred_append historical _⟩
      change output.registers .rsp = fixture.own.resources.callerAddress + 8
      simpa [output, X86.State.writeRegister, localCPU, cpu] using
        congrArg (fun address : Word => address + 8) currentRsp

/-- An empty INC boundary quantifies over the real coupled effect; a nonempty
boundary requires neither atomic selection nor primitive execution. -/
theorem inc_generated (fixture : Fixture) {state : S} {history : Log}
    {worker : Worker} (frame : Frame (descriptor fixture) state)
    (binding : Binding (descriptor fixture) incNode state worker)
    (inputs : Inputs fixture state worker) :
    rwp (descriptor fixture) (returnPost fixture) (entryInv fixture) 2 incNode state history := by
  change IdleBox .sharedCell 0 _ state history .arithmetic
  intro after extended idle
  have retained := frame.idle idle
  obtain ⟨current, bound, currentInputs, selection⟩ := inputs_idle binding inputs idle
  refine ⟨retained, current, bound, ?_⟩
  change if current.pending = [] then _ else True
  by_cases empty : current.pending = []
  · rw [ite_eq_left empty]
    have chosen : EDSL.OS.TSO64.atomicFor after.world current.resources
        ((sharedCPU after current).registers inc.base) =
          some (fixture.issued.identifier, fixture.fresh.handle, fixture.fresh.cell) := by
      change EDSL.OS.TSO64.atomicFor after.world current.resources
        (current.context.registers .rdi) = _
      rw [currentInputs.rdi]
      exact selection
    refine ⟨fixture.issued.identifier, fixture.fresh.handle, fixture.fresh.cell, chosen, ?_⟩
    intro af output machine coupled
    have effect : Atomics64.AddRMWMachineEffect after.world current.resources.actor
        fixture.issued.identifier (sharedCPU after current) inc output machine := coupled
    have issued := AtomicIssued.of_effect (d := descriptor fixture) (node := incNode)
      (instruction := inc) (af := af) retained bound rfl empty chosen coupled
    have actual := issued.actual
    have nextFrame := retained.step actual
    have nextPC : machine.state.rip = 393216 + 4 := by
      change machine.state.rip = (393216 : Word) + 4
      have pc : current.context.rip = 393216 := by
        calc
          current.context.rip = (393216 : Word) + 0 := bound.pc
          _ = 393216 := by decide +kernel
      calc
        machine.state.rip = current.context.rip + BitVec.ofNat 64 inc.length := effect.rip
        _ = 393216 + BitVec.ofNat 64 inc.length := by rw [pc]
        _ = 393216 + 4 := by decide +kernel
    have nextBinding : Binding (descriptor fixture) retNode
        (install after 0 output.1 { current with context := .ofCPU machine.state })
        { current with context := .ofCPU machine.state } :=
      ⟨List.getElem?_set_self (List.getElem_of_getElem? bound.live).1,
        bound.resources, bound.running, nextPC⟩
    have nextStack : machine.state.registers .rsp = fixture.own.resources.callerAddress := by
      rw [effect.all_registers rfl]
      exact currentInputs.rsp
    have address : output.2.arithmetic.event.address = 65536 := by
      exact effect.cpu.address.trans currentInputs.rdi
    have delta : output.2.arithmetic.delta = 1 := effect.delta
    have old : loadQWord (published after.world) 65536 =
        .ok output.2.arithmetic.event.before := by
      simpa only [address, sharedCPU, cpu] using effect.cpu.old
    have increment : output.2.arithmetic.event.after = output.2.arithmetic.event.before + 1 := by
      simpa only [delta] using effect.cpu.after
    have historical : IncOccurred fixture
        (issueLog (descriptor fixture) after extended af
          (install after 0 output.1 { current with context := .ofCPU machine.state },
            .rmw 0 output.2)) := by
      refine ⟨⟨after, .issue 0 af,
        (install after 0 output.1 { current with context := .ofCPU machine.state },
          .rmw 0 output.2)⟩, List.mem_append_right _ (List.mem_singleton_self _),
        current, af, output, machine, bound, rfl, rfl, issued, selection,
        effect.actor_handle.2, ?_, address, delta, old, increment, ?_⟩
      · exact effect.actor_handle.1.trans currentInputs.actor
      · exact effect.rip
    refine ⟨retNode, inc_ret_edge, nextPC, ?_⟩
    exact ret_generated fixture nextFrame nextBinding nextStack historical
  · rw [ite_eq_right empty]
    trivial

/-- Annotations are constructed independently of any chosen scheduler actions. -/
def annotations (fixture : Fixture) : Annotations (descriptor fixture) (returnPost fixture) where
  Inv := entryInv fixture
  blocks := by
    intro cut state history worker _isCut frame binding invariant
    obtain ⟨sameNode, prior, live, inputs⟩ := invariant
    subst cut
    have sameWorker : prior = worker := Option.some.inj (live.symm.trans binding.live)
    subst prior
    exact inc_generated fixture frame binding inputs

/-- Actual present fixture admission uses the original protected caller word. -/
theorem admission (fixture : Fixture) : Admission (descriptor fixture) fixture.state := by
  refine ⟨fixture.valid, fixture.own_live, fixture.own_running, fixture.ownCode, ?_⟩
  change Borrowing.loadWord64 fixture.state.world.legacy.shared fixture.own.resources.actor
    fixture.own.resources.caller.identifier fixture.own.resources.callerAddress = .ok 0x7000
  rw [original_actor]
  exact fixture.ownCaller

private theorem initial_inputs (fixture : Fixture) : Inputs fixture fixture.state fixture.own := by
  refine ⟨?_, ?_, original_actor fixture, original_atomics fixture,
    fixture.fresh.actual, fixture.old.actual⟩
  · rw [fixture.own_context]
    rfl
  · rw [fixture.own_context, original_caller_address]
    rfl

/-- Entry has no generated-rwp, future-run or desired machine-output premise. -/
theorem entry (fixture : Fixture) : Entry (annotations fixture) fixture.state incNode := by
  refine ⟨admission fixture, rfl, ?_, rfl, fixture.own, fixture.own_live,
    initial_inputs fixture⟩
  refine ⟨fixture.own_live, rfl, fixture.own_running, ?_⟩
  change fixture.own.context.rip = (393216 : Word) + 0
  rw [fixture.own_context]
  rfl

/-- The actual initial generated residual precedes the choice of any schedule. -/
theorem generated_initial (fixture : Fixture) :
    Residual (descriptor fixture) fixture.state (returnPost fixture) (entryInv fixture)
      2 incNode fixture.state [] := by
  exact (entry fixture).related.2

/-- Closed present admission; the parent independently checked this finite
computation before the integration client's execution observations were added. -/
theorem present_admitted : Support.MixedBlockingFixture.presentView = .ok () := by
  decide +kernel

private theorem exists_admitted :
    ∃ fixture, Support.MixedBlockingFixture.blockingFixture = .ok fixture := by
  have admitted := present_admitted
  cases actual : Support.MixedBlockingFixture.blockingFixture with
  | error fault =>
    simp only [Support.MixedBlockingFixture.presentView, actual, Except.map, reduceCtorEq] at admitted
  | ok fixture => exact ⟨fixture, rfl⟩

-- Only now choose a future schedule. No declaration above depends on it.
def actions : List Action :=
  [.issue 0 false, .issue 1 true, .drain 0, .issue 0 true,
    .drain 0, .issue 0 false, .issue 0 true]

/-- Independently specified event contracts use admitted identities, never a
reference interpreter or an expected successor State. -/
def peerEvent (fixture : Fixture) : Atomics64.FetchAddEvent :=
  ⟨12, fixture.issued.ready.atomicB, fixture.peer.handle.cell, ⟨4, ⟨65536, 9, 13⟩⟩⟩

def ownEvent (fixture : Fixture) : Atomics64.FetchAddEvent :=
  ⟨11, fixture.issued.identifier, fixture.fresh.handle.cell, ⟨1, ⟨65536, 13, 14⟩⟩⟩

def expectedObservations (fixture : Fixture) : List O :=
  [.blocked 0, .rmw 1 (peerEvent fixture),
    .drained 0 (.ordinary fixture.issued.ready.dataA Support.MixedBlockingFixture.firstStore),
    .blocked 0,
    .drained 0 (.ordinary fixture.issued.ready.dataA Support.MixedBlockingFixture.secondStore),
    .rmw 0 (ownEvent fixture), .returned 0]

/-- A small view of the production result, retaining the actual successful
schedule rather than constructing a desired final State. -/
def executionView : Except Fault Bool := do
  let fixture ← Support.MixedBlockingFixture.blockingFixture
  let result ← EDSL.OS.TSO64.schedule fixture.state actions .sharedCell .arithmetic
  return decide (result.2 = expectedObservations fixture)

theorem execution_view : executionView = .ok true := by decide +kernel

/-- The real successful Except branches supply both the input Fixture and
actual final machine state. This is an existential execution witness. -/
theorem actual_run : ∃ (fixture : Fixture) (final : S),
    Support.MixedBlockingFixture.blockingFixture = .ok fixture ∧
    EDSL.OS.TSO64.schedule fixture.state actions .sharedCell .arithmetic =
      .ok (final, expectedObservations fixture) := by
  have observed := execution_view
  cases admitted : Support.MixedBlockingFixture.blockingFixture with
  | error fault => simp only [executionView, admitted, error_bind, reduceCtorEq] at observed
  | ok fixture =>
    cases scheduled : EDSL.OS.TSO64.schedule fixture.state actions .sharedCell .arithmetic with
    | error fault =>
      simp only [executionView, admitted, ok_bind, scheduled, error_bind, reduceCtorEq] at observed
    | ok result =>
      rcases result with ⟨final, observations⟩
      have correct : observations = expectedObservations fixture := by
        have decision : decide (observations = expectedObservations fixture) = true := by
          simpa only [executionView, admitted, ok_bind, scheduled, pure_ok,
            Except.ok.injEq] using observed
        exact of_decide_eq_true decision
      exact ⟨fixture, final, rfl, by simpa only [correct] using scheduled⟩

/-- Finite current-state observations, independent of graph control and proofs. -/
structure BoundaryView where
  worker : Option (Word × Nat × Phase)
  counter : Except Error Word
  deriving DecidableEq

def boundaryView (state : S) : BoundaryView :=
  ⟨(state.workers[0]?).map (fun worker =>
      (worker.context.rip, worker.pending.length, worker.phase)),
    loadQWord (published state.world) 65536⟩

def expectedBoundaries : List BoundaryView :=
  [⟨some (393216, 2, .running), .ok 9⟩,
    ⟨some (393216, 2, .running), .ok 9⟩,
    ⟨some (393216, 2, .running), .ok 13⟩,
    ⟨some (393216, 1, .running), .ok 13⟩,
    ⟨some (393216, 1, .running), .ok 13⟩,
    ⟨some (393216, 0, .running), .ok 13⟩,
    ⟨some (393220, 0, .running), .ok 14⟩,
    ⟨some (0x7000, 0, .returned), .ok 14⟩]

/-- Prefix computations are observations of the same production schedule.
Their connection to the full run is proved by schedule_cut below. -/
def prefixView (index : Nat) : Except Fault BoundaryView := do
  let fixture ← Support.MixedBlockingFixture.blockingFixture
  let result ← EDSL.OS.TSO64.schedule fixture.state (actions.take index) .sharedCell .arithmetic
  return boundaryView result.1

private theorem prefix_zero : prefixView 0 = .ok expectedBoundaries[0] := by decide +kernel
private theorem prefix_one : prefixView 1 = .ok expectedBoundaries[1] := by decide +kernel
private theorem prefix_two : prefixView 2 = .ok expectedBoundaries[2] := by decide +kernel
private theorem prefix_three : prefixView 3 = .ok expectedBoundaries[3] := by decide +kernel
private theorem prefix_four : prefixView 4 = .ok expectedBoundaries[4] := by decide +kernel
private theorem prefix_five : prefixView 5 = .ok expectedBoundaries[5] := by decide +kernel
private theorem prefix_six : prefixView 6 = .ok expectedBoundaries[6] := by decide +kernel
private theorem prefix_seven : prefixView 7 = .ok expectedBoundaries[7] := by decide +kernel

private theorem prefix_view (index : Fin 8) :
    prefixView index.val = .ok expectedBoundaries[index.val] := by
  rcases index with ⟨index, bound⟩
  have casesIndex : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
  rcases casesIndex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prefix_zero
  · exact prefix_one
  · exact prefix_two
  · exact prefix_three
  · exact prefix_four
  · exact prefix_five
  · exact prefix_six
  · exact prefix_seven

private theorem prefix_observation {fixture : Fixture} {before : S} {index : Fin 8}
    (admitted : Support.MixedBlockingFixture.blockingFixture = .ok fixture)
    (actual : EDSL.OS.TSO64.schedule fixture.state (actions.take index.val) .sharedCell .arithmetic =
      .ok (before, (expectedObservations fixture).take index.val)) :
    boundaryView before = expectedBoundaries[index.val] := by
  have observed := prefix_view index
  simpa only [prefixView, admitted, ok_bind, actual, pure_ok, Except.ok.injEq] using observed

/-- Inspect adapter control rather than infer it from a machine RIP. -/
def controlView {fixture : Fixture}
    (ghost : Ghost (descriptor fixture) fixture.state (returnPost fixture)) : Option (Nat × Nat) :=
  match ghost.control with
  | .running node fuel => some (node.val, fuel)
  | .done _ => none

def expectedControls : List (Option (Nat × Nat)) :=
  [some (0, 2), some (0, 2), some (0, 2), some (0, 2),
    some (0, 2), some (0, 2), some (1, 1), none]

private def Quiet (action : Action) (seen : O) : Prop :=
  passive 0 action ∨ seen = .blocked 0

private inductive QuietPairs : List Action → List O → Prop where
  | nil : QuietPairs [] []
  | cons {action : Action} {seen : O} {chosen : List Action} {observations : List O}
      (head : Quiet action seen) (tail : QuietPairs chosen observations) :
      QuietPairs (action :: chosen) (seen :: observations)

private theorem advance_quiet_control {fixture : Fixture}
    {before after : Ghost (descriptor fixture) fixture.state (returnPost fixture)}
    {action : Action} {seen : O}
    (advanced : Advance (descriptor fixture) fixture.state (returnPost fixture)
      before action seen after) (quiet : Quiet action seen) :
    after.control = before.control := by
  cases advanced with
  | passive _ _ => rfl
  | blocked _ => rfl
  | next _ _ _ _ =>
    rcases quiet with quiet | impossible
    · exact False.elim (quiet rfl)
    · cases impossible
  | rmw _ _ _ =>
    rcases quiet with quiet | impossible
    · exact False.elim (quiet rfl)
    · cases impossible
  | returned _ =>
    rcases quiet with quiet | impossible
    · exact False.elim (quiet rfl)
    · cases impossible

private theorem lift_quiet_control {fixture : Fixture}
    {before after : Ghost (descriptor fixture) fixture.state (returnPost fixture)}
    {chosen : List Action} {observations : List O}
    (trace : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      before chosen observations after) :
    QuietPairs chosen observations → after.control = before.control := by
  induction trace with
  | nil => intro _; rfl
  | cons head _tail ih =>
    intro quiet
    cases quiet with
    | cons first rest => exact (ih rest).trans (advance_quiet_control head first)

private theorem quiet_take {chosen : List Action} {observations : List O}
    (quiet : QuietPairs chosen observations) (index : Nat) :
    QuietPairs (chosen.take index) (observations.take index) := by
  induction quiet generalizing index with
  | nil =>
    simp only [List.take_nil]
    exact .nil
  | cons head _tail ih =>
    cases index with
    | zero => exact .nil
    | succ index => exact .cons head (ih index)

private theorem first_five_quiet (fixture : Fixture) :
    QuietPairs (actions.take 5) ((expectedObservations fixture).take 5) :=
  .cons (.inr rfl) (.cons (.inl (by change (1 : Nat) ≠ 0; decide +kernel))
    (.cons (.inl True.intro) (.cons (.inr rfl) (.cons (.inl True.intro) .nil))))

private theorem early_control {fixture : Fixture} {index : Nat}
    {ghost : Ghost (descriptor fixture) fixture.state (returnPost fixture)}
    (bound : index ≤ 5)
    (trace : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      (initialGhost (descriptor fixture) fixture.state (returnPost fixture) incNode)
      (actions.take index) ((expectedObservations fixture).take index) ghost) :
    ghost.control = .running incNode 2 := by
  have quiet : QuietPairs (actions.take index)
      ((expectedObservations fixture).take index) := by
    simpa only [List.take_take, Nat.min_eq_left bound] using
      quiet_take (first_five_quiet fixture) index
  exact lift_quiet_control trace quiet

/-- Split the same lifted trace, retaining its actual intermediate ghost. -/
private theorem lift_cut {fixture : Fixture}
    {before after : Ghost (descriptor fixture) fixture.state (returnPost fixture)}
    {chosen : List Action} {observations : List O}
    (trace : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      before chosen observations after) (index : Nat) :
    ∃ middle,
      LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
        before (chosen.take index) (observations.take index) middle ∧
      LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
        middle (chosen.drop index) (observations.drop index) after := by
  induction trace generalizing index with
  | nil =>
    simp only [List.take_nil, List.drop_nil]
    exact ⟨_, .nil, .nil⟩
  | cons head tail ih =>
    cases index with
    | zero => exact ⟨_, .nil, .cons head tail⟩
    | succ index =>
      obtain ⟨middle, front, suffix⟩ := ih index
      exact ⟨middle, .cons head front, suffix⟩

/-- Decompose list indices while their payloads and ghosts are variables. -/
private theorem lift_uncons {G : Type} {advance : G → Action → O → G → Prop}
    {before after : G} {action : Action} {seen : O}
    {chosen : List Action} {observations : List O}
    (trace : LiftTrace advance before (action :: chosen) (seen :: observations) after) :
    ∃ middle, advance before action seen middle ∧
      LiftTrace advance middle chosen observations after := by
  cases trace with
  | cons head tail => exact ⟨_, head, tail⟩

private theorem lift_single {G : Type} {advance : G → Action → O → G → Prop}
    {before after : G} {action : Action} {seen : O}
    (trace : LiftTrace advance before [action] [seen] after) :
    advance before action seen after := by
  cases trace with
  | cons head tail =>
    cases tail
    exact head

/-- Invert an RMW with variable indices, retaining the exact checked issue. -/
private theorem advance_rmw_witnesses {d : Descriptor} {initial : S} {Post : Assertion}
    {before after : Ghost d initial Post} {action : Action} {seen : O}
    {af : Bool} {event : Atomics64.FetchAddEvent}
    (advanced : Advance d initial Post before action seen after)
    (actionEq : action = .issue d.tid af) (seenEq : seen = .rmw d.tid event) :
    ∃ (node destination : d.graph.Index) (fuel : Nat)
        (output : World × Atomics64.FetchAddEvent) (machine : AddRMW64.Observation),
      before.control = .running node (fuel + 1) ∧
      AtomicIssued d node before.current af (after.current, .rmw d.tid event) output machine ∧
      d.graph.Edge node destination ∧
      after.control = .running destination (arrivalFuel d destination fuel) := by
  cases advanced with
  | passive quiet _ =>
    rw [actionEq] at quiet
    exact False.elim (quiet rfl)
  | blocked _ => cases seenEq
  | next _ _ _ _ => cases seenEq
  | rmw issued edge _ =>
    have choiceEq := (Action.issue.inj actionEq).2
    have eventEq := (Observation.rmw.inj seenEq).2
    cases choiceEq
    cases eventEq
    exact ⟨_, _, _, _, _, rfl, issued, edge, rfl⟩
  | returned _ => cases seenEq

private theorem inc_destination : ∀ destination : graph.Index,
    graph.Edge incNode destination → destination = retNode := by
  unfold VCGen.MixedCFG.Graph.Edge
  decide +kernel

private theorem advance_inc_control {fixture : Fixture}
    {before after : Ghost (descriptor fixture) fixture.state (returnPost fixture)}
    {event : Atomics64.FetchAddEvent}
    (advanced : Advance (descriptor fixture) fixture.state (returnPost fixture)
      before (.issue 0 false) (.rmw 0 event) after)
    (source : before.control = .running incNode 2) :
    after.control = .running retNode 1 := by
  obtain ⟨node, destination, fuel, _output, _machine, atSource, _issued, edge, atDestination⟩ :=
    advance_rmw_witnesses advanced rfl rfl
  have controls := Control.running.inj (atSource.symm.trans source)
  have nodeEq : node = incNode := controls.1
  have fuelEq : fuel = 1 := Nat.succ.inj controls.2
  subst node
  subst fuel
  have destinationEq := inc_destination destination edge
  subst destination
  exact atDestination

private theorem six_control {fixture : Fixture}
    {ghost : Ghost (descriptor fixture) fixture.state (returnPost fixture)}
    (trace : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      (initialGhost (descriptor fixture) fixture.state (returnPost fixture) incNode)
      (actions.take 6) ((expectedObservations fixture).take 6) ghost) :
    ghost.control = .running retNode 1 := by
  obtain ⟨middle, early, last⟩ := lift_cut trace 5
  have firstFive : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      (initialGhost (descriptor fixture) fixture.state (returnPost fixture) incNode)
      (actions.take 5) ((expectedObservations fixture).take 5) middle := by
    simpa [actions, expectedObservations] using early
  have one : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      middle [.issue 0 false] [.rmw 0 (ownEvent fixture)] ghost := by
    simpa [actions, expectedObservations] using last
  exact advance_inc_control (lift_single one) (early_control (by omega) firstFive)

private theorem advance_return_control {fixture : Fixture}
    {before after : Ghost (descriptor fixture) fixture.state (returnPost fixture)}
    (advanced : Advance (descriptor fixture) fixture.state (returnPost fixture)
      before (.issue 0 true) (.returned 0) after) : controlView after = none := by
  obtain ⟨response, _fuel, _source, destination, _choice⟩ := advanced.returned_response
  rw [destination]
  rfl

private theorem seven_control {fixture : Fixture}
    {ghost : Ghost (descriptor fixture) fixture.state (returnPost fixture)}
    (trace : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      (initialGhost (descriptor fixture) fixture.state (returnPost fixture) incNode)
      (actions.take 7) ((expectedObservations fixture).take 7) ghost) :
    controlView ghost = none := by
  obtain ⟨middle, _early, last⟩ := lift_cut trace 6
  have one : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      middle [.issue 0 true] [.returned 0] ghost := by
    simpa [actions, expectedObservations] using last
  exact advance_return_control (lift_single one)

private theorem prefix_control {fixture : Fixture} (index : Fin 8)
    {ghost : Ghost (descriptor fixture) fixture.state (returnPost fixture)}
    (trace : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      (initialGhost (descriptor fixture) fixture.state (returnPost fixture) incNode)
      (actions.take index.val) ((expectedObservations fixture).take index.val) ghost) :
    controlView ghost = expectedControls[index.val] := by
  rcases index with ⟨index, bound⟩
  have casesIndex : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
  rcases casesIndex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [controlView, early_control (index := 0) (by decide +kernel) trace] <;> rfl
  · simp only [controlView, early_control (index := 1) (by decide +kernel) trace] <;> rfl
  · simp only [controlView, early_control (index := 2) (by decide +kernel) trace] <;> rfl
  · simp only [controlView, early_control (index := 3) (by decide +kernel) trace] <;> rfl
  · simp only [controlView, early_control (index := 4) (by decide +kernel) trace] <;> rfl
  · simp only [controlView, early_control (index := 5) (by decide +kernel) trace] <;> rfl
  · simp only [controlView, six_control trace] <;> rfl
  · exact seven_control trace

private theorem lift_authentic {fixture : Fixture}
    {before after : Ghost (descriptor fixture) fixture.state (returnPost fixture)}
    {chosen : List Action} {observations : List O}
    (trace : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      before chosen observations after) :
    OriginTrace .sharedCell fixture.state before.history before.current .arithmetic →
      OriginTrace .sharedCell fixture.state after.history after.current .arithmetic := by
  induction trace with
  | nil => exact id
  | cons head _tail ih =>
    intro authentic
    apply ih
    rw [head.tick]
    exact authentic.snoc head.origin

/-- Exact selected evidence retained by the adapter's arithmetic constructor. -/
def SelectedINC (fixture : Fixture) (before after : S) : Prop :=
  ∃ (worker : Worker) (output : World × Atomics64.FetchAddEvent)
      (machine : AddRMW64.Observation),
    Binding (descriptor fixture) incNode before worker ∧
    AtomicIssued (descriptor fixture) incNode before false
      (after, .rmw 0 (ownEvent fixture)) output machine ∧
    EDSL.OS.TSO64.atomicFor before.world worker.resources 65536 =
      some (fixture.issued.identifier, fixture.fresh.handle, fixture.fresh.cell) ∧
    Atomics64.authorize before.world 11 fixture.issued.ready.atomicA =
      .ok (fixture.old.handle, fixture.old.cell) ∧
    worker.resources.atomics = [fixture.issued.identifier, fixture.issued.ready.atomicA] ∧
    fixture.issued.identifier ≠ fixture.issued.ready.atomicA ∧
    output.2 = ownEvent fixture ∧
    loadQWord (published before.world) 65536 = .ok 13 ∧
    machine.state.rip = 393220 ∧
    after.workers[0]? = some { worker with context := .ofCPU machine.state }

private theorem advance_inc_selected {fixture : Fixture}
    {before after : Ghost (descriptor fixture) fixture.state (returnPost fixture)}
    (authentic : OriginTrace .sharedCell fixture.state before.history before.current .arithmetic)
    (advanced : Advance (descriptor fixture) fixture.state (returnPost fixture)
      before (.issue 0 false) (.rmw 0 (ownEvent fixture)) after)
    (source : before.control = .running incNode 2) :
    SelectedINC fixture before.current after.current := by
  have evidence : ∃ output machine,
      AtomicIssued (descriptor fixture) incNode before.current false
        (after.current, .rmw 0 (ownEvent fixture)) output machine := by
    obtain ⟨node, _destination, _fuel, output, machine, atSource, issued, _edge,
      _atDestination⟩ := advance_rmw_witnesses advanced rfl rfl
    have nodeEq : node = incNode := (Control.running.inj (atSource.symm.trans source)).1
    subst node
    exact ⟨output, machine, issued⟩
  obtain ⟨output, machine, issued⟩ := evidence
  obtain ⟨worker, instruction, identifier, handle, cell, binding, selected,
    _empty, _decoded, chosen, _changed, _executed, coupled, installed⟩ := issued.witnesses
  have instructionEq : instruction = inc := (Decoded.locked.inj selected).symm
  subst instruction
  have effect : Atomics64.AddRMWMachineEffect before.current.world worker.resources.actor
      identifier (sharedCPU before.current worker) inc output machine := coupled
  have eventEq : output.2 = ownEvent fixture :=
    (Observation.rmw.inj (congrArg Prod.snd installed)).2.symm
  have identifierEq : identifier = fixture.issued.identifier :=
    effect.actor_handle.2.symm.trans (congrArg Atomics64.FetchAddEvent.handle eventEq)
  subst identifier
  have actor : worker.resources.actor = 11 :=
    (congrArg Resources.actor binding.resources).trans (original_actor fixture)
  have fresh : Atomics64.authorize before.current.world 11 fixture.issued.identifier =
      .ok (fixture.fresh.handle, fixture.fresh.cell) :=
    (authentic.stable.authorize 11 fixture.issued.identifier).trans fixture.fresh.actual
  have granted := (atomicFor_sound chosen).2.1
  rw [actor] at granted
  have descriptorEq := Except.ok.inj (granted.symm.trans fresh)
  have handleEq : handle = fixture.fresh.handle := congrArg Prod.fst descriptorEq
  have cellEq : cell = fixture.fresh.cell := congrArg Prod.snd descriptorEq
  have operand : worker.context.registers .rdi = 65536 :=
    effect.cpu.address.symm.trans
      (congrArg (fun event : Atomics64.FetchAddEvent => event.arithmetic.event.address) eventEq)
  have selection : EDSL.OS.TSO64.atomicFor before.current.world worker.resources 65536 =
      some (fixture.issued.identifier, fixture.fresh.handle, fixture.fresh.cell) := by
    change EDSL.OS.TSO64.atomicFor before.current.world worker.resources
      (worker.context.registers .rdi) = _ at chosen
    rw [operand, handleEq, cellEq] at chosen
    exact chosen
  refine ⟨worker, output, machine, binding, issued, selection,
    (authentic.stable.authorize 11 fixture.issued.ready.atomicA).trans fixture.old.actual,
    (congrArg Resources.atomics binding.resources).trans (original_atomics fixture),
    fixture.handles_different, eventEq, ?_, ?_, ?_⟩
  · simpa only [eventEq, ownEvent, sharedCPU, cpu] using effect.cpu.old
  · have pc : worker.context.rip = 393216 := by
      calc
        worker.context.rip = (393216 : Word) + 0 := binding.pc
        _ = 393216 := by decide +kernel
    calc
      machine.state.rip = worker.context.rip + BitVec.ofNat 64 inc.length := effect.rip
      _ = 393216 + BitVec.ofNat 64 inc.length := by rw [pc]
      _ = 393220 := by decide +kernel
  · have finalEq : after.current = install before.current 0 output.1
        { worker with context := .ofCPU machine.state } := congrArg Prod.fst installed
    rw [finalEq]
    exact List.getElem?_set_self (List.getElem_of_getElem? binding.live).1

private theorem selected_from_trace {fixture : Fixture}
    {ghost : Ghost (descriptor fixture) fixture.state (returnPost fixture)}
    (trace : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      (initialGhost (descriptor fixture) fixture.state (returnPost fixture) incNode)
      actions (expectedObservations fixture) ghost) :
    ∃ before after,
      LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
        (initialGhost (descriptor fixture) fixture.state (returnPost fixture) incNode)
        (actions.take 5) ((expectedObservations fixture).take 5) before ∧
      Advance (descriptor fixture) fixture.state (returnPost fixture)
        before (.issue 0 false) (.rmw 0 (ownEvent fixture)) after ∧
      SelectedINC fixture before.current after.current := by
  obtain ⟨middle, front, suffix⟩ := lift_cut trace 5
  have lastTwo : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      middle [.issue 0 false, .issue 0 true]
      [.rmw 0 (ownEvent fixture), .returned 0] ghost := by
    simpa [actions, expectedObservations] using suffix
  obtain ⟨after, head, _tail⟩ := lift_uncons lastTwo
  exact ⟨middle, after, front, head,
    advance_inc_selected (lift_authentic front .nil) head
      (early_control (by omega) front)⟩

private theorem response_from_trace {fixture : Fixture}
    {ghost : Ghost (descriptor fixture) fixture.state (returnPost fixture)}
    (trace : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      (initialGhost (descriptor fixture) fixture.state (returnPost fixture) incNode)
      actions (expectedObservations fixture) ghost) :
    ∃ response : Response (descriptor fixture) fixture.state (returnPost fixture),
      ghost = ⟨response.after, response.history, .done response⟩ := by
  obtain ⟨middle, _prefix, suffix⟩ := lift_cut trace 6
  have lastOne : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      middle [.issue 0 true] [.returned 0] ghost := by
    simpa [actions, expectedObservations] using suffix
  obtain ⟨response, _fuel, _source, destination, _choice⟩ :=
    (lift_single lastOne).returned_response
  exact ⟨response, destination⟩

/-- Both actual own blocks retain the WHOLE input state. -/
private theorem whole_blocks {fixture : Fixture} {final : S}
    (actual : EDSL.OS.TSO64.schedule fixture.state actions .sharedCell .arithmetic =
      .ok (final, expectedObservations fixture)) :
    EDSL.OS.TSO64.step fixture.state (.issue 0 false) .sharedCell .arithmetic =
      .ok (fixture.state, .blocked 0) ∧
    ∃ before,
      EDSL.OS.TSO64.schedule fixture.state (actions.take 3) .sharedCell .arithmetic =
        .ok (before, (expectedObservations fixture).take 3) ∧
      EDSL.OS.TSO64.step before (.issue 0 true) .sharedCell .arithmetic =
        .ok (before, .blocked 0) := by
  obtain ⟨before0, action0, after0, prefix0, actionAt0, stepped0⟩ :=
    ScheduleTrace.observation_at actual (index := 0) (by rfl)
  have beforeEq : fixture.state = before0 := congrArg Prod.fst (Except.ok.inj prefix0)
  subst before0
  have actionEq0 : action0 = .issue 0 false := (Option.some.inj actionAt0).symm
  subst action0
  have unchanged0 := blocked_unchanged stepped0
  subst after0
  have first := stepped0
  obtain ⟨before, action, after, prefixRun, actionAt, stepped⟩ :=
    ScheduleTrace.observation_at actual (index := 3) (by rfl)
  have actionEq : action = .issue 0 true := (Option.some.inj actionAt).symm
  subst action
  have unchanged := blocked_unchanged stepped
  subst after
  exact ⟨first, before, prefixRun, stepped⟩

/-- All eight cuts are actual prefixes of ONE full successful run. They retain
current protected resources as well as the exact adapter node/fuel table. -/
def Prefixes (fixture : Fixture) (final : S) : Prop :=
  ∀ index : Fin 8, ∃ before ghost,
    EDSL.OS.TSO64.schedule fixture.state (actions.take index.val) .sharedCell .arithmetic =
      .ok (before, (expectedObservations fixture).take index.val) ∧
    EDSL.OS.TSO64.schedule before (actions.drop index.val) .sharedCell .arithmetic =
      .ok (final, (expectedObservations fixture).drop index.val) ∧
    Related (annotations fixture) before ghost ∧
    LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      (initialGhost (descriptor fixture) fixture.state (returnPost fixture) incNode)
      (actions.take index.val) ((expectedObservations fixture).take index.val) ghost ∧
    boundaryView before = expectedBoundaries[index.val] ∧
    controlView ghost = expectedControls[index.val] ∧
    Frame (descriptor fixture) before

private theorem all_prefixes {fixture : Fixture} {final : S}
    (admitted : Support.MixedBlockingFixture.blockingFixture = .ok fixture)
    (actual : EDSL.OS.TSO64.schedule fixture.state actions .sharedCell .arithmetic =
      .ok (final, expectedObservations fixture)) : Prefixes fixture final := by
  intro index
  obtain ⟨before, ghost, prefixRun, suffix, related, lifted⟩ :=
    (annotations fixture).schedule_cut (entry fixture) actual index.val
  exact ⟨before, ghost, prefixRun, suffix, related, lifted,
    prefix_observation (index := index) admitted prefixRun,
    prefix_control index lifted, related.frame⟩

/-- Acceptance combines the independent generated client with actual execution,
complete log positions, both whole-state blocks, and adapter selection evidence.
Every environmental/resource assumption remains in the production contracts. -/
structure Integration (fixture : Fixture) (final : S)
    (ghost : Ghost (descriptor fixture) fixture.state (returnPost fixture)) : Prop where
  admitted : Support.MixedBlockingFixture.blockingFixture = .ok fixture
  entry : Entry (annotations fixture) fixture.state incNode
  residual : Residual (descriptor fixture) fixture.state (returnPost fixture) (entryInv fixture)
    2 incNode fixture.state []
  actual : EDSL.OS.TSO64.schedule fixture.state actions .sharedCell .arithmetic =
    .ok (final, expectedObservations fixture)
  related : Related (annotations fixture) final ghost
  lifted : LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
    (initialGhost (descriptor fixture) fixture.state (returnPost fixture) incNode)
    actions (expectedObservations fixture) ghost
  authentic : OriginTrace .sharedCell fixture.state ghost.history final .arithmetic
  actionPositions : ghost.history.map Tick.action = actions
  observationPositions : ghost.history.map (fun tick => tick.result.2) = expectedObservations fixture
  sevenPositions : ghost.history.length = 7
  retirements : ghost.history.map (fun tick => tick.result.2.retired) = [0, 1, 0, 0, 0, 1, 1]
  prefixes : Prefixes fixture final
  firstWholeBlock : EDSL.OS.TSO64.step fixture.state (.issue 0 false) .sharedCell .arithmetic =
    .ok (fixture.state, .blocked 0)
  secondWholeBlock : ∃ before,
    EDSL.OS.TSO64.schedule fixture.state (actions.take 3) .sharedCell .arithmetic =
      .ok (before, (expectedObservations fixture).take 3) ∧
    EDSL.OS.TSO64.step before (.issue 0 true) .sharedCell .arithmetic =
      .ok (before, .blocked 0)
  selected : ∃ before after,
    LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      (initialGhost (descriptor fixture) fixture.state (returnPost fixture) incNode)
      (actions.take 5) ((expectedObservations fixture).take 5) before ∧
    Advance (descriptor fixture) fixture.state (returnPost fixture)
      before (.issue 0 false) (.rmw 0 (ownEvent fixture)) after ∧
    SelectedINC fixture before.current after.current
  returnedPosition : ∃ (response : Response (descriptor fixture) fixture.state (returnPost fixture))
      (fuel : Nat),
    EDSL.OS.TSO64.schedule fixture.state (actions.take 6) .sharedCell .arithmetic =
      .ok (response.before, (expectedObservations fixture).take 6) ∧
    actions[6]? = some (.issue 0 response.af) ∧
    LiftTrace (Advance (descriptor fixture) fixture.state (returnPost fixture))
      (initialGhost (descriptor fixture) fixture.state (returnPost fixture) incNode)
      (actions.take 6) ((expectedObservations fixture).take 6)
      ⟨response.before, response.priorLog, .running response.node (fuel + 1)⟩ ∧
    response.priorLog.map Tick.action = actions.take 6 ∧
    response.priorLog.map (fun tick => tick.result.2) = (expectedObservations fixture).take 6 ∧
    Done (descriptor fixture) fixture.state (returnPost fixture) response response.after response.history
  frame : Frame (descriptor fixture) final
  response : ∃ response : Response (descriptor fixture) fixture.state (returnPost fixture),
    final = response.after ∧ ghost.history = response.history ∧
    Done (descriptor fixture) fixture.state (returnPost fixture) response final ghost.history ∧
    returnPost fixture final ghost.history

/-- Closed integration regression. Admission and generated obligations are
constructed independently; no desired future success or postcondition is a
premise. All states and ticks come from production schedule/adapter witnesses. -/
theorem independent_integration : ∃ (fixture : Fixture) (final : S)
    (ghost : Ghost (descriptor fixture) fixture.state (returnPost fixture)),
    Integration fixture final ghost := by
  obtain ⟨fixture, final, admitted, actual⟩ := actual_run
  obtain ⟨ghost, related, lifted, authentic, actionsEq, observationsEq⟩ :=
    (annotations fixture).schedule (entry fixture) actual
  have lengthEq : ghost.history.length = 7 := by
    simpa only [List.length_map, actions, List.length_cons, List.length_nil] using
      congrArg List.length actionsEq
  have retirements : ghost.history.map (fun tick => tick.result.2.retired) =
      [0, 1, 0, 0, 0, 1, 1] := by
    calc
      ghost.history.map (fun tick => tick.result.2.retired) =
          (ghost.history.map (fun tick => tick.result.2)).map Observation.retired := by
        simp only [List.map_map, Function.comp_def]
      _ = (expectedObservations fixture).map Observation.retired :=
        congrArg (List.map Observation.retired) observationsEq
      _ = [0, 1, 0, 0, 0, 1, 1] := rfl
  obtain ⟨firstBlock, secondBlock⟩ := whole_blocks actual
  obtain ⟨response, destination⟩ := response_from_trace lifted
  have finalEq : final = response.after := related.1.trans (congrArg Ghost.current destination)
  have historyEq : ghost.history = response.history := congrArg Ghost.history destination
  have done : Done (descriptor fixture) fixture.state (returnPost fixture)
      response final ghost.history := by
    have retained := related.2
    rw [destination] at retained
    simpa only [finalEq, historyEq] using retained
  have post : returnPost fixture final ghost.history := by
    rw [finalEq, historyEq]
    exact response.post
  exact ⟨fixture, final, ghost, {
    admitted := admitted
    entry := entry fixture
    residual := generated_initial fixture
    actual := actual
    related := related
    lifted := lifted
    authentic := authentic
    actionPositions := actionsEq
    observationPositions := observationsEq
    sevenPositions := lengthEq
    retirements := retirements
    prefixes := all_prefixes admitted actual
    firstWholeBlock := firstBlock
    secondWholeBlock := secondBlock
    selected := selected_from_trace lifted
    returnedPosition := (annotations fixture).returned_at (entry fixture) actual (index := 6) rfl
    frame := related.frame
    response := ⟨response, finalEq, historyEq, done, post⟩ }⟩

end EDSL.Tests.MixedResumableBlocking

#print axioms EDSL.Tests.MixedResumableBlocking.graph_checked
#print axioms EDSL.Tests.MixedResumableBlocking.structural
#print axioms EDSL.Tests.MixedResumableBlocking.ret_generated
#print axioms EDSL.Tests.MixedResumableBlocking.inc_generated
#print axioms EDSL.Tests.MixedResumableBlocking.admission
#print axioms EDSL.Tests.MixedResumableBlocking.entry
#print axioms EDSL.Tests.MixedResumableBlocking.generated_initial
#print axioms EDSL.Tests.MixedResumableBlocking.present_admitted
#print axioms EDSL.Tests.MixedResumableBlocking.execution_view
#print axioms EDSL.Tests.MixedResumableBlocking.actual_run
#print axioms EDSL.Tests.MixedResumableBlocking.independent_integration
#audit_edsl
