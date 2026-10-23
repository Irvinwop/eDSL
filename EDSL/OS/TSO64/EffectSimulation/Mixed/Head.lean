/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects.OneStep
import EDSL.OS.TSO64.EffectSimulation.Ordinary
import EDSL.OS.TSO64.EffectSimulation.Resources
import EDSL.X86.VCGen.MixedCFGTransport

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Current mixed instruction boundaries for the production TSO64 scheduler.
The descriptor fixes admitted bytes, original protected resources, family and
ordinary policy. The frame transports actual code and the protected caller
word, while shared data and CPU operands remain those of the current world.

Dispatch, FIFO blocking and locked enabledness use the existing mixed graph
transport and native `lockedFor` kernel. Ordinary obligations use the production
`Effects.oneStep`, current read/queue admission and complete CPU reification.
Retirement evidence records an actual scheduler step, including its selected
atomic handle; an arbitrary native origin is never converted into a step.
No idle closure, recursive block, future schedule or program result is assumed.
Theorems retain the underlying long-mode/CET-off, coherent scalar WB RAM,
stable translation/no-alias and protected-resource model assumptions; they
assert no additional hardware, compiler, fairness or termination refinement.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

/-- Fixed call data and independently admitted complete mixed byte window. -/
structure Descriptor where
  family : RMWFamily
  profile : Profile
  tid : Nat
  bytes : List Byte
  base : Word
  graph : VCGen.MixedCFG.Graph family
  caps : VCGen.MixedCFG.Caps
  structural : VCGen.MixedCFG.Valid family caps bytes graph
  original : Worker
  codeLoan : Borrowing.Subregion ⟨base, bytes.length⟩ original.resources.code.loan.region
  callerValue : Word
  policy : S → VCGen.Effects.Policy

abbrev Assertion := S → Log → Prop
abbrev CutAssertion (d : Descriptor) := d.graph.Index → S → Log → Prop

/-- Admission is about current inputs, resources and the protected caller read. -/
structure Admission (d : Descriptor) (initial : S) : Prop where
  wellFormed : WellFormed initial d.profile
  live : initial.workers[d.tid]? = some d.original
  running : d.original.phase = .running
  code : CodeAt (published initial.world) d.base d.bytes
  caller : Borrowing.loadWord64 initial.world.legacy.shared d.original.resources.actor
    d.original.resources.caller.identifier d.original.resources.callerAddress = .ok d.callerValue

/-- Original resource identity and protected bytes, without freezing shared RAM. -/
structure Frame (d : Descriptor) (state : S) : Prop where
  wellFormed : WellFormed state d.profile
  worker : ∃ current, state.workers[d.tid]? = some current ∧
    current.resources = d.original.resources
  code : CodeAt (published state.world) d.base d.bytes
  caller : Borrowing.loadWord64 state.world.legacy.shared d.original.resources.actor
    d.original.resources.caller.identifier d.original.resources.callerAddress = .ok d.callerValue

theorem Admission.frame {d : Descriptor} {initial : S}
    (admitted : Admission d initial) : Frame d initial :=
  ⟨admitted.wellFormed, ⟨d.original, admitted.live, rfl⟩, admitted.code, admitted.caller⟩

/-- Every actual native origin preserves the original protected frame. -/
theorem Frame.origin {d : Descriptor} {before : S} {action : Action} {result : S × O}
    (frame : Frame d before) (origin : Origin before action result d.profile d.family) :
    Frame d result.1 := by
  obtain ⟨prior, live, original⟩ := frame.worker
  obtain ⟨current, currentLive, retained⟩ := origin_resources origin live
  exact ⟨origin_wellFormed origin frame.wellFormed,
    ⟨current, currentLive, retained.trans original⟩, origin_code origin frame.code,
    origin_loan_read_preserved origin frame.wellFormed frame.caller⟩

theorem Frame.along {d : Descriptor} {initial final : S} {history : Log}
    (trace : OriginTrace d.profile initial history final d.family) :
    Frame d initial → Frame d final := by
  induction trace with
  | nil => exact id
  | cons head _ ih => intro frame; exact ih (frame.origin head)

theorem Frame.pause {d : Descriptor} {before after : S} {history extended : Log}
    (frame : Frame d before)
    (paused : Pause d.profile d.tid (before, history) (after, extended) d.family) :
    Frame d after := by
  obtain ⟨_suffix, trace, _quiet, _appended⟩ := paused
  exact Frame.along trace frame

theorem Frame.step {d : Descriptor} {before : S} {action : Action} {result : S × O}
    (frame : Frame d before)
    (actual : TSO64.step before action d.profile d.family = .ok result) : Frame d result.1 :=
  frame.origin (step_origin actual)

/-- This actual live, running worker is at the authenticated instruction boundary. -/
structure Binding (d : Descriptor) (node : d.graph.Index) (state : S) (worker : Worker) : Prop where
  live : state.workers[d.tid]? = some worker
  resources : worker.resources = d.original.resources
  running : worker.phase = .running
  pc : worker.context.rip = d.base + BitVec.ofNat 64 (d.graph.node node).offset

theorem Binding.codeLoan {d : Descriptor} {node : d.graph.Index} {state : S} {worker : Worker}
    (binding : Binding d node state worker) :
    Borrowing.Subregion ⟨d.base, d.bytes.length⟩ worker.resources.code.loan.region := by
  simpa only [binding.resources] using d.codeLoan

theorem Binding.resourcesValid {d : Descriptor} {node : d.graph.Index}
    {state : S} {worker : Worker} (binding : Binding d node state worker)
    (frame : Frame d state) : ResourcesValid state.world worker.resources :=
  (frame.wellFormed.2 worker (List.mem_of_getElem? binding.live)).1

theorem Binding.localCode {d : Descriptor} {node : d.graph.Index} {state : S} {worker : Worker}
    (binding : Binding d node state worker) (frame : Frame d state) :
    CodeAt (localCPU state worker).memory d.base d.bytes :=
  VCGen.ManagedRules.local_code frame.wellFormed
    (frame.wellFormed.2 worker (List.mem_of_getElem? binding.live)) frame.code binding.codeLoan

/-- Guarded dispatch is derived from the whole admitted window and current loan. -/
theorem Binding.fetched {d : Descriptor} {node : d.graph.Index} {state : S} {worker : Worker}
    (binding : Binding d node state worker) (frame : Frame d state) :
    decode (fetchCPU state worker) d.family = .ok (d.graph.node node).instruction :=
  d.structural.guarded_decoded frame.code binding.codeLoan node binding.pc

theorem Binding.localDecoded {d : Descriptor} {node : d.graph.Index}
    {state : S} {worker : Worker} (binding : Binding d node state worker)
    (frame : Frame d state) :
    decode (localCPU state worker) d.family = .ok (d.graph.node node).instruction :=
  d.structural.decoded (binding.localCode frame) node (localCPU state worker) rfl binding.pc

/-- Locked operands and code are read from the current published world. -/
theorem Binding.sharedDecoded {d : Descriptor} {node : d.graph.Index}
    {state : S} {worker : Worker} (binding : Binding d node state worker)
    (frame : Frame d state) :
    decode (sharedCPU state worker) d.family = .ok (d.graph.node node).instruction :=
  d.structural.decoded frame.code node (sharedCPU state worker) rfl binding.pc

/-- This bound uses the exact four/five-byte locked tag or ordinary length. -/
theorem Binding.codeFits {d : Descriptor} {node : d.graph.Index} {state : S} {worker : Worker}
    (binding : Binding d node state worker) (frame : Frame d state) :
    TSO64.codeFits worker (VCGen.MixedCFG.instructionLength (d.graph.node node).instruction) :=
  d.structural.codeFits frame.code binding.codeLoan node binding.pc

/-- Invert the production dispatch; no instruction bytes are decoded here. -/
private theorem decode_ordinary {family : RMWFamily} {initial : X86.State}
    {instruction : Sequential.Instruction}
    (decoded : decode initial family = .ok (.ordinary instruction)) :
    Sequential.decodeAt initial = .ok instruction := by
  cases first : fetchByte initial.memory initial.rip with
  | error fault => simp [decode, first, Except.mapError] at decoded
  | ok byte =>
    by_cases lock : byte = 0xf0#8
    · cases actual : family.decodeAt initial <;>
        simp [decode, first, lock, actual, Except.mapError] at decoded
    · cases actual : Sequential.decodeAt initial with
      | error fault => simp [decode, first, lock, actual, Except.mapError] at decoded
      | ok ordinary =>
        simp [decode, first, lock, actual, Except.mapError] at decoded
        cases decoded
        rfl

private theorem decode_locked {family : RMWFamily} {initial : X86.State}
    {instruction : family.Instruction}
    (decoded : decode initial family = .ok (.locked instruction)) :
    family.decodeAt initial = .ok instruction := by
  cases first : fetchByte initial.memory initial.rip with
  | error fault => simp [decode, first, Except.mapError] at decoded
  | ok byte =>
    by_cases lock : byte = 0xf0#8
    · cases actual : family.decodeAt initial with
      | error fault => simp [decode, first, lock, actual, Except.mapError] at decoded
      | ok locked =>
        simp [decode, first, lock, actual, Except.mapError] at decoded
        cases decoded
        rfl
    · cases actual : Sequential.decodeAt initial <;>
        simp [decode, first, lock, actual, Except.mapError] at decoded

theorem Binding.ordinaryDecoded {d : Descriptor} {node : d.graph.Index}
    {state : S} {worker : Worker} {instruction : Sequential.Instruction}
    (binding : Binding d node state worker) (frame : Frame d state)
    (selected : (d.graph.node node).instruction = .ordinary instruction) :
    Sequential.decodeAt (localCPU state worker) = .ok instruction := by
  apply decode_ordinary (family := d.family)
  simpa only [selected] using binding.localDecoded frame

theorem Binding.atomicDecoded {d : Descriptor} {node : d.graph.Index}
    {state : S} {worker : Worker} {instruction : d.family.Instruction}
    (binding : Binding d node state worker) (frame : Frame d state)
    (selected : (d.graph.node node).instruction = .locked instruction) :
    d.family.decodeAt (sharedCPU state worker) = .ok instruction := by
  apply decode_locked
  simpa only [selected] using binding.sharedDecoded frame

/-- Equality with native dispatch retains all errors and the entire blocking gate. -/
theorem Frame.dispatch {d : Descriptor} {node : d.graph.Index} {state : S} {worker : Worker}
    (frame : Frame d state) (binding : Binding d node state worker) (af : Bool) :
    TSO64.step state (.issue d.tid af) d.profile d.family =
      match (d.graph.node node).instruction with
      | .ordinary instruction => ordinary state d.tid worker instruction af d.profile
      | .locked instruction => lockedFor d.family state d.tid worker instruction := by
  have resources := binding.resourcesValid frame
  change issue state d.tid af d.profile d.family = _
  have actual := d.structural.issue_eq_dispatch binding.live binding.running resources.1 resources.2.1
    frame.code binding.codeLoan node binding.pc af d.profile
  cases selected : (d.graph.node node).instruction with
  | ordinary instruction => simpa only [selected] using actual
  | locked instruction => simpa only [selected] using actual

/-- A nonempty whole own FIFO blocks before any selector or primitive is needed. -/
theorem Frame.blocked {d : Descriptor} {node : d.graph.Index} {state : S} {worker : Worker}
    {instruction : d.family.Instruction} (frame : Frame d state)
    (binding : Binding d node state worker)
    (selected : (d.graph.node node).instruction = .locked instruction)
    (nonempty : worker.pending ≠ []) (af : Bool) :
    TSO64.step state (.issue d.tid af) d.profile d.family = .ok (state, .blocked d.tid) := by
  have bounds : codeFits worker (d.family.embed instruction).length := by
    simpa only [selected, VCGen.MixedCFG.instructionLength] using binding.codeFits frame
  rw [frame.dispatch binding af, selected]
  cases pending : worker.pending with
  | nil => exact False.elim (nonempty pending)
  | cons head tail => simp [lockedFor, bounds, pending]

inductive Retirement where
  | ordinary (observation : Sequential.Observation)
  | rmw (output : World × Atomics64.FetchAddEvent) (machine : AddRMW64.Observation)

/-- Fresh sequential head, real OS queue/finish and full reconstructed CPU. -/
structure OrdinaryIssued (d : Descriptor) (node : d.graph.Index) (before : S) (af : Bool)
    (result : S × O) (observation : Sequential.Observation) : Prop where
  witnesses : ∃ (worker : Worker) (instruction : Sequential.Instruction) (update : Queue.Cursor),
    Binding d node before worker ∧ (d.graph.node node).instruction = .ordinary instruction ∧
    OrdinaryReady before d.tid worker instruction d.profile d.family ∧
    VCGen.Effects.Head d.bytes d.base (d.policy before) (Sequential.FlagChoices.uniform af)
      (localCPU before worker) instruction observation ∧
    QueueEffect before worker instruction update d.profile ∧
    FinishEffect before d.tid worker update.pending observation result update.nextStore
  actual : TSO64.step before (.issue d.tid af) d.profile d.family = .ok result
  reifies : Reifies d.tid result observation
  world : result.1.world = before.world

/-- The exact first matching selector and both native executions are retained. -/
structure AtomicIssued (d : Descriptor) (node : d.graph.Index) (before : S) (af : Bool)
    (result : S × O) (output : World × Atomics64.FetchAddEvent)
    (machine : AddRMW64.Observation) : Prop where
  witnesses : ∃ (worker : Worker) (instruction : d.family.Instruction)
      (identifier : Atomics64.HandleId64) (handle : Atomics64.Handle) (cell : Atomics64.Cell),
    Binding d node before worker ∧ (d.graph.node node).instruction = .locked instruction ∧
    worker.pending = [] ∧
    d.family.decodeAt (sharedCPU before worker) = .ok instruction ∧
    atomicFor before.world worker.resources
      ((sharedCPU before worker).registers (d.family.embed instruction).base) =
        some (identifier, handle, cell) ∧
    Atomics64.fetchAdd before.world worker.resources.actor identifier
      ((d.family.embed instruction).delta (sharedCPU before worker)) = .ok output ∧
    d.family.stepCPU (sharedCPU before worker) = .ok machine ∧
    d.family.MachineEffect before.world worker.resources.actor identifier
      (sharedCPU before worker) instruction output machine ∧
    result = (install before d.tid output.1 { worker with context := .ofCPU machine.state },
      .rmw d.tid output.2)
  actual : TSO64.step before (.issue d.tid af) d.profile d.family = .ok result

inductive RetiredEvidence (d : Descriptor) (node : d.graph.Index) (before : S) (af : Bool) :
    (S × O) → Retirement → Prop where
  | ordinary {result : S × O} {observation : Sequential.Observation}
      (issued : OrdinaryIssued d node before af result observation) :
      RetiredEvidence d node before af result (.ordinary observation)
  | rmw {result : S × O} {output : World × Atomics64.FetchAddEvent}
      {machine : AddRMW64.Observation} (issued : AtomicIssued d node before af result output machine) :
      RetiredEvidence d node before af result (.rmw output machine)

/-- Extract selected-handle evidence from an actual checked locked step.
The native origin relation alone deliberately forgets this selector equality. -/
theorem AtomicIssued.of_step {d : Descriptor} {node : d.graph.Index}
    {before : S} {worker : Worker} {instruction : d.family.Instruction} {af : Bool}
    {result : S × O} (frame : Frame d before) (binding : Binding d node before worker)
    (selected : (d.graph.node node).instruction = .locked instruction)
    (empty : worker.pending = [])
    (actual : TSO64.step before (.issue d.tid af) d.profile d.family = .ok result) :
    ∃ output machine, AtomicIssued d node before af result output machine := by
  have native : lockedFor d.family before d.tid worker instruction = .ok result := by
    have dispatch := frame.dispatch binding af
    rw [selected] at dispatch
    exact dispatch.symm.trans actual
  cases lockedFor_effect native with
  | blocked _bounds nonempty => exact False.elim (nonempty empty)
  | @rmw identifier handle cell output machine _bounds currentEmpty decoded chosen changed executed =>
    exact ⟨output, machine,
      ⟨⟨worker, instruction, identifier, handle, cell, binding, selected, currentEmpty,
        decoded, chosen, changed, executed, lockedFor_coupled decoded chosen changed executed,
        rfl⟩, actual⟩⟩

/-- Independent current-step enabledness. Current WF and the actual selector
supply primitive, machine and coupled-effect witnesses without a future run. -/
theorem Frame.atomicEnabled {d : Descriptor} {node : d.graph.Index} {state : S} {worker : Worker}
    {instruction : d.family.Instruction} {identifier : Atomics64.HandleId64}
    {handle : Atomics64.Handle} {cell : Atomics64.Cell} (frame : Frame d state)
    (binding : Binding d node state worker)
    (selected : (d.graph.node node).instruction = .locked instruction)
    (empty : worker.pending = [])
    (chosen : atomicFor state.world worker.resources
      ((sharedCPU state worker).registers (d.family.embed instruction).base) =
        some (identifier, handle, cell)) (af : Bool) :
    ∃ (output : World × Atomics64.FetchAddEvent) (machine : AddRMW64.Observation),
      AtomicIssued d node state af
        (install state d.tid output.1 { worker with context := .ofCPU machine.state },
          .rmw d.tid output.2) output machine := by
  have bounds : codeFits worker (d.family.embed instruction).length := by
    simpa only [selected, VCGen.MixedCFG.instructionLength] using binding.codeFits frame
  have decoded := binding.atomicDecoded frame selected
  obtain ⟨output, machine, changed, executed, native⟩ :=
    lockedFor_enabled (tid := d.tid) frame.wellFormed.1 bounds empty decoded chosen
  have actual : TSO64.step state (.issue d.tid af) d.profile d.family = .ok
      (install state d.tid output.1 { worker with context := .ofCPU machine.state },
        .rmw d.tid output.2) := by
    rw [frame.dispatch binding af, selected]
    exact native
  exact ⟨output, machine,
    ⟨⟨worker, instruction, identifier, handle, cell, binding, selected, empty, decoded,
      chosen, changed, executed, lockedFor_coupled decoded chosen changed executed, rfl⟩,
      actual⟩⟩

theorem AtomicIssued.origin {d : Descriptor} {node : d.graph.Index} {before : S} {af : Bool}
    {result : S × O} {output : World × Atomics64.FetchAddEvent} {machine : AddRMW64.Observation}
    (issued : AtomicIssued d node before af result output machine) :
    Origin before (.issue d.tid af) result d.profile d.family :=
  step_origin issued.actual

theorem OrdinaryIssued.origin {d : Descriptor} {node : d.graph.Index} {before : S} {af : Bool}
    {result : S × O} {observation : Sequential.Observation}
    (issued : OrdinaryIssued d node before af result observation) :
    Origin before (.issue d.tid af) result d.profile d.family :=
  step_origin issued.actual

/-- Recover the effect for a specified actual selector triple. The live slot,
node and selector equalities identify every operand and handle with the witness. -/
theorem AtomicIssued.effect {d : Descriptor} {node : d.graph.Index} {before : S} {af : Bool}
    {result : S × O} {output : World × Atomics64.FetchAddEvent} {machine : AddRMW64.Observation}
    {worker : Worker} {instruction : d.family.Instruction} {identifier : Atomics64.HandleId64}
    {handle : Atomics64.Handle} {cell : Atomics64.Cell}
    (issued : AtomicIssued d node before af result output machine)
    (binding : Binding d node before worker)
    (selected : (d.graph.node node).instruction = .locked instruction)
    (chosen : atomicFor before.world worker.resources
      ((sharedCPU before worker).registers (d.family.embed instruction).base) =
        some (identifier, handle, cell)) :
    d.family.MachineEffect before.world worker.resources.actor identifier
      (sharedCPU before worker) instruction output machine := by
  obtain ⟨current, actualInstruction, actualIdentifier, _handle, _cell, actualBinding,
    actualNode, _empty, _decoded, actualChosen, _changed, _executed, effect, _installed⟩ :=
    issued.witnesses
  have sameWorker : current = worker :=
    Option.some.inj (actualBinding.live.symm.trans binding.live)
  subst current
  have sameInstruction : actualInstruction = instruction :=
    Decoded.locked.inj (actualNode.symm.trans selected)
  subst actualInstruction
  have sameIdentifier : actualIdentifier = identifier :=
    congrArg Prod.fst (Option.some.inj (actualChosen.symm.trans chosen))
  subst actualIdentifier
  exact effect

/-- Current admissions and a checked joint effect determine the actual native
issue. Clients can use this rule without unfolding scheduler implementation. -/
theorem AtomicIssued.of_effect {d : Descriptor} {node : d.graph.Index}
    {before : S} {worker : Worker} {instruction : d.family.Instruction} {af : Bool}
    {identifier : Atomics64.HandleId64} {handle : Atomics64.Handle} {cell : Atomics64.Cell}
    {output : World × Atomics64.FetchAddEvent} {machine : AddRMW64.Observation}
    (frame : Frame d before) (binding : Binding d node before worker)
    (selected : (d.graph.node node).instruction = .locked instruction)
    (empty : worker.pending = [])
    (chosen : atomicFor before.world worker.resources
      ((sharedCPU before worker).registers (d.family.embed instruction).base) =
        some (identifier, handle, cell))
    (effect : d.family.MachineEffect before.world worker.resources.actor identifier
      (sharedCPU before worker) instruction output machine) :
    AtomicIssued d node before af
      (install before d.tid output.1 { worker with context := .ofCPU machine.state },
        .rmw d.tid output.2) output machine := by
  obtain ⟨priorOutput, priorMachine, issued⟩ :=
    frame.atomicEnabled binding selected empty chosen af
  have prior := RMWFamily.MachineEffect.arithmetic (issued.effect binding selected chosen)
  have current := RMWFamily.MachineEffect.arithmetic effect
  have outputEq : priorOutput = output := Except.ok.inj (prior.checked.symm.trans current.checked)
  have machineEq : priorMachine = machine := Except.ok.inj (prior.step.symm.trans current.step)
  subst priorOutput
  subst priorMachine
  exact issued

theorem RetiredEvidence.actual {d : Descriptor} {node : d.graph.Index} {before : S} {af : Bool}
    {result : S × O} {retirement : Retirement}
    (issued : RetiredEvidence d node before af result retirement) :
    TSO64.step before (.issue d.tid af) d.profile d.family = .ok result := by
  cases issued with
  | ordinary evidence => exact evidence.actual
  | rmw evidence => exact evidence.actual

theorem RetiredEvidence.origin {d : Descriptor} {node : d.graph.Index} {before : S} {af : Bool}
    {result : S × O} {retirement : Retirement}
    (issued : RetiredEvidence d node before af result retirement) :
    Origin before (.issue d.tid af) result d.profile d.family :=
  step_origin issued.actual

theorem RetiredEvidence.frame {d : Descriptor} {node : d.graph.Index} {before : S} {af : Bool}
    {result : S × O} {retirement : Retirement}
    (issued : RetiredEvidence d node before af result retirement) (frame : Frame d before) :
    Frame d result.1 :=
  frame.origin issued.origin

/-- Each retirement tag certifies one native retirement, including legacy RET. -/
theorem RetiredEvidence.retired {d : Descriptor} {node : d.graph.Index} {before : S} {af : Bool}
    {result : S × O} {retirement : Retirement}
    (issued : RetiredEvidence d node before af result retirement) : result.2.retired = 1 := by
  cases issued with
  | ordinary evidence =>
    obtain ⟨_worker, _instruction, _update, _binding, _node, _ready, _head, _queue, finish⟩ :=
      evidence.witnesses
    cases finish <;> rfl
  | rmw evidence =>
    obtain ⟨_worker, _instruction, _identifier, _handle, _cell, _binding, _node, _empty,
      _decoded, _chosen, _changed, _executed, _effect, installed⟩ := evidence.witnesses
    rw [installed]
    rfl

/-- An ordinary finish must exist; atomics and syscalls cannot satisfy it. -/
def OrdinaryOutcome (observation : Sequential.Observation) : Prop :=
  ∃ output, observation.result = .next output ∨ observation.result = .returned output

/-- Generated obligations for only the current step. A nonempty own FIFO
needs no atomic authority or effect. An empty FIFO requires the real selector,
and the continuation ranges over joint current primitive/machine effects. -/
def One (d : Descriptor) (node : d.graph.Index) (state : S)
    (K : Bool → (S × O) → Retirement → Prop) : Prop :=
  ∃ worker, Binding d node state worker ∧
    match (d.graph.node node).instruction with
    | .ordinary instruction =>
      OrdinaryReady state d.tid worker instruction d.profile d.family ∧
      VCGen.Effects.oneStep (C := Bool) (d.policy state) Sequential.FlagChoices.uniform
        (localCPU state worker) instruction (fun af observation =>
          OrdinaryOutcome observation ∧
          ∀ (update : Queue.Cursor) (result : S × O),
            QueueEffect state worker instruction update d.profile →
            FinishEffect state d.tid worker update.pending observation result update.nextStore →
            K af result (.ordinary observation))
    | .locked instruction =>
      if worker.pending = [] then
        ∃ identifier handle cell,
          atomicFor state.world worker.resources
            ((sharedCPU state worker).registers (d.family.embed instruction).base) =
              some (identifier, handle, cell) ∧
          ∀ (af : Bool) (output : World × Atomics64.FetchAddEvent) (machine : AddRMW64.Observation),
            d.family.MachineEffect state.world worker.resources.actor identifier
              (sharedCPU state worker) instruction output machine →
            K af (install state d.tid output.1 { worker with context := .ofCPU machine.state },
              .rmw d.tid output.2) (.rmw output machine)
      else True

/-- Identify a real queue/finish with the production ordinary issue. This
uses the checked head's executor and the original readiness gates unchanged. -/
private theorem checked_issue {state : S} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {af : Bool} {profile : Profile} {family : RMWFamily}
    {bytes : List Byte} {base : Word} {policy : VCGen.Effects.Policy}
    {observation : Sequential.Observation} {update : Queue.Cursor} {result : S × O}
    (ready : OrdinaryReady state tid worker instruction profile family)
    (head : VCGen.Effects.Head bytes base policy (Sequential.FlagChoices.uniform af)
      (localCPU state worker) instruction observation)
    (queue : QueueEffect state worker instruction update profile)
    (finish : FinishEffect state tid worker update.pending observation result update.nextStore) :
    TSO64.step state (.issue tid af) profile family = .ok result := by
  have executed := head.actual
  rw [Sequential.stepWith_eq_executeWith _ head.decoded,
    Sequential.executeWith_uniform _ _ af (supported_boolChoiceProfile ready.admitted)] at executed
  obtain ⟨units, reads⟩ := ready.reads
  change issue state tid af profile family = .ok result
  simp [issue, ready.live, ready.running, ready.codeCurrent, ready.callerCurrent,
    ready.dispatch, ordinary, ready.admitted, ready.bounds, head.decoded, reads,
    VCGen.ManagedRules.queue_checked queue, executed, Except.mapError,
    VCGen.ManagedRules.finish_checked finish]

/-- The supplied semantic finish and full reification concern the same actual
issue. Existence and coherence reuse the existing ordinary head adapter. -/
theorem OrdinaryIssued.of_head {d : Descriptor} {node : d.graph.Index} {state : S} {af : Bool}
    {worker : Worker} {instruction : Sequential.Instruction} {observation : Sequential.Observation}
    {update : Queue.Cursor} {result : S × O} (frame : Frame d state)
    (binding : Binding d node state worker)
    (selected : (d.graph.node node).instruction = .ordinary instruction)
    (ready : OrdinaryReady state d.tid worker instruction d.profile d.family)
    (head : VCGen.Effects.Head d.bytes d.base (d.policy state) (Sequential.FlagChoices.uniform af)
      (localCPU state worker) instruction observation)
    (queue : QueueEffect state worker instruction update d.profile)
    (finish : FinishEffect state d.tid worker update.pending observation result update.nextStore) :
    OrdinaryIssued d node state af result observation := by
  have checked := checked_issue ready head queue finish
  obtain ⟨actual, success, reified, world, _valid⟩ := issue_from_head frame.wellFormed ready head
  have same : actual = result := Except.ok.inj (success.symm.trans checked)
  subst actual
  exact ⟨⟨worker, instruction, update, binding, selected, ready, head, queue, finish⟩,
    checked, reified, world⟩

/-- Present obligations independently produce a native blocked stutter or an
actual retirement with its continuation. No future successful step is a premise. -/
theorem One.resume {d : Descriptor} {node : d.graph.Index} {state : S}
    {K : Bool → (S × O) → Retirement → Prop}
    (frame : Frame d state) (one : One d node state K) (af : Bool) :
    TSO64.step state (.issue d.tid af) d.profile d.family = .ok (state, .blocked d.tid) ∨
      ∃ result retirement, RetiredEvidence d node state af result retirement ∧
        K af result retirement := by
  obtain ⟨worker, binding, generated⟩ := one
  cases selected : (d.graph.node node).instruction with
  | ordinary instruction =>
    simp only [selected] at generated
    obtain ⟨ready, vc⟩ := generated
    obtain ⟨observation, head, _noSyscall, outcome, continuation⟩ :=
      VCGen.Effects.oneStep_head (binding.localCode frame)
        (binding.ordinaryDecoded frame selected) vc af
    obtain ⟨update, queue⟩ := ready.queue
    have finishing : ∃ result : S × O,
        FinishEffect state d.tid worker update.pending observation result update.nextStore := by
      obtain ⟨output, next | returned⟩ := outcome
      · let replacement : Worker :=
          { worker with
            context := .ofCPU output
            pending := update.pending
            nextStore := update.nextStore }
        exact ⟨(install state d.tid state.world replacement, .ordinary d.tid), .next next⟩
      · let replacement : Worker :=
          { worker with
            context := .ofCPU output
            phase := .returned
            pending := update.pending
            nextStore := update.nextStore }
        exact ⟨(install state d.tid state.world replacement, .returned d.tid), .returned returned⟩
    obtain ⟨result, finish⟩ := finishing
    have issued := OrdinaryIssued.of_head frame binding selected ready head queue finish
    exact .inr ⟨result, .ordinary observation, .ordinary issued,
      continuation update result queue finish⟩
  | locked instruction =>
    simp only [selected] at generated
    by_cases empty : worker.pending = []
    · rw [ite_eq_left empty] at generated
      obtain ⟨identifier, handle, cell, chosen, continuation⟩ := generated
      obtain ⟨output, machine, issued⟩ := frame.atomicEnabled binding selected empty chosen af
      exact .inr ⟨_, .rmw output machine, .rmw issued,
        continuation af output machine (issued.effect binding selected chosen)⟩
    · exact .inl (frame.blocked binding selected empty af)

/-- Both current AF valuations are enabled by present obligations, including
native whole-state blocking. The result is constructed independently of a run. -/
theorem One.enabled {d : Descriptor} {node : d.graph.Index} {state : S}
    {K : Bool → (S × O) → Retirement → Prop}
    (frame : Frame d state) (one : One d node state K) (af : Bool) :
    ∃ result, TSO64.step state (.issue d.tid af) d.profile d.family = .ok result := by
  rcases One.resume frame one af with blocked | ⟨result, _retirement, issued, _post⟩
  · exact ⟨(state, .blocked d.tid), blocked⟩
  · exact ⟨result, issued.actual⟩

/-- Specialization to an observed current step uses native determinism, never
an origin converse. The retired continuation is about that exact result. -/
theorem One.resume_of_step {d : Descriptor} {node : d.graph.Index} {state : S}
    {K : Bool → (S × O) → Retirement → Prop} {af : Bool} {result : S × O}
    (frame : Frame d state) (one : One d node state K)
    (actual : TSO64.step state (.issue d.tid af) d.profile d.family = .ok result) :
    result = (state, .blocked d.tid) ∨
      ∃ retirement, RetiredEvidence d node state af result retirement ∧ K af result retirement := by
  rcases One.resume frame one af with blocked | ⟨observed, retirement, issued, post⟩
  · exact .inl (Except.ok.inj (actual.symm.trans blocked))
  · have same : observed = result := Except.ok.inj (issued.actual.symm.trans actual)
    subst observed
    exact .inr ⟨retirement, issued, post⟩

/-- Continuation weakening preserves the exact current native admissions. -/
theorem One.mono {d : Descriptor} {node : d.graph.Index} {state : S}
    {K L : Bool → (S × O) → Retirement → Prop}
    (implies : ∀ af result retirement, K af result retirement → L af result retirement)
    (one : One d node state K) : One d node state L := by
  obtain ⟨worker, binding, generated⟩ := one
  refine ⟨worker, binding, ?_⟩
  cases selected : (d.graph.node node).instruction with
  | ordinary instruction =>
    simp only [selected] at generated ⊢
    refine ⟨generated.1, ?_⟩
    apply VCGen.Effects.oneStep_mono (vc := generated.2)
    intro af observation post
    refine ⟨post.1, ?_⟩
    intro update result queue finish
    exact implies af result (.ordinary observation) (post.2 update result queue finish)
  | locked instruction =>
    simp only [selected] at generated ⊢
    by_cases empty : worker.pending = []
    · rw [ite_eq_left empty] at generated ⊢
      obtain ⟨identifier, handle, cell, chosen, continuation⟩ := generated
      refine ⟨identifier, handle, cell, chosen, ?_⟩
      intro af output machine effect
      exact implies af _ (.rmw output machine) (continuation af output machine effect)
    · simp only [ite_eq_right empty]

#print axioms Descriptor
#print axioms Admission
#print axioms Frame
#print axioms Admission.frame
#print axioms Frame.origin
#print axioms Frame.along
#print axioms Frame.pause
#print axioms Frame.step
#print axioms Binding
#print axioms Binding.codeLoan
#print axioms Binding.resourcesValid
#print axioms Binding.localCode
#print axioms Binding.fetched
#print axioms Binding.localDecoded
#print axioms Binding.sharedDecoded
#print axioms Binding.codeFits
#print axioms decode_ordinary
#print axioms decode_locked
#print axioms Binding.ordinaryDecoded
#print axioms Binding.atomicDecoded
#print axioms Frame.dispatch
#print axioms Frame.blocked
#print axioms Retirement
#print axioms OrdinaryIssued
#print axioms AtomicIssued
#print axioms RetiredEvidence
#print axioms AtomicIssued.of_step
#print axioms Frame.atomicEnabled
#print axioms AtomicIssued.origin
#print axioms OrdinaryIssued.origin
#print axioms AtomicIssued.effect
#print axioms AtomicIssued.of_effect
#print axioms RetiredEvidence.actual
#print axioms RetiredEvidence.origin
#print axioms RetiredEvidence.frame
#print axioms RetiredEvidence.retired
#print axioms OrdinaryOutcome
#print axioms One
#print axioms checked_issue
#print axioms OrdinaryIssued.of_head
#print axioms One.resume
#print axioms One.enabled
#print axioms One.resume_of_step
#print axioms One.mono

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
