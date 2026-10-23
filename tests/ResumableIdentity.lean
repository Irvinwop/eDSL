/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Resumable.Block

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
A positive client of the generated ordinary-block residual. The owned synthetic
window is exactly MOV RAX,RDI; RET. The independent contract returns arbitrary
input x in RAX, through the original caller slot, in returned phase.

Admission concerns a real current world/worker and the original protected loans.
There is no initial RAX requirement, empty-FIFO requirement, future Head, future
successful run, desired poststate, or equality of writable RAM. Both instruction
boundaries quantify over every native passive origin admitted by Box. The helper
for the RET boundary receives its current RAX from the actual preceding MOV.

This client proves the generated residual; generic schedule transport is
provided by the library. It makes no corpus, termination, fairness or physical claim.
-/

namespace EDSL.Tests.ResumableIdentity
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation
open OS.TSO64.EffectSimulation.Resumable

/-- Owned exact bytes: full-width register copy followed by RET. -/
def bytes : List Byte := [0x48, 0x89, 0xf8, 0xc3]

def graph : Sequential.CFG.Graph := ⟨[
  ⟨0, .movReg64 .rax .rdi, true, 1⟩,
  ⟨3, .legacy .ret, false, 0⟩], 1⟩

abbrev entry : graph.Index := ⟨0, by decide +kernel⟩
abbrev retNode : graph.Index := ⟨1, by decide +kernel⟩

private def exceptEq {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error left, .error right =>
    match decEq left right with
    | .isTrue same => .isTrue (congrArg Except.error same)
    | .isFalse different => .isFalse (fun same => different (Except.error.inj same))
  | .ok left, .ok right =>
    match decEq left right with
    | .isTrue same => .isTrue (congrArg Except.ok same)
    | .isFalse different => .isFalse (fun same => different (Except.ok.inj same))
  | .error _, .ok _ => .isFalse (fun same => by cases same)
  | .ok _, .error _ => .isFalse (fun same => by cases same)

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α) := exceptEq

private theorem pair_components {α β : Type} {actual : α × β} {left : α} {right : β}
    (same : actual = (left, right)) : actual.1 = left ∧ actual.2 = right :=
  ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

private theorem entry_edge : graph.Edge entry retNode := by decide +kernel

-- Keep the finite decoder computation out of elaborator reflexivity reduction.
private def decodingSnapshot : Except Error Sequential.Instruction ×
    Except Error Sequential.Instruction :=
  (Sequential.decodeAt (Sequential.codeState bytes 0),
    Sequential.decodeAt (Sequential.codeState bytes 3))

private theorem decoding_snapshot :
    decodingSnapshot = (.ok (.movReg64 .rax .rdi), .ok (.legacy .ret)) := by
  decide +kernel

/-- The production decoder, independently of the graph annotations. -/
theorem exact_decoding :
    Sequential.decodeAt (Sequential.codeState bytes 0) = .ok (.movReg64 .rax .rdi) ∧
    Sequential.decodeAt (Sequential.codeState bytes 3) = .ok (.legacy .ret) :=
  pair_components (actual := decodingSnapshot) decoding_snapshot

theorem graph_checked : Sequential.CFG.Structural.check bytes graph = true := by
  decide +kernel

theorem structural : Sequential.CFG.Structural.Valid bytes graph :=
  Sequential.CFG.Structural.check_sound graph_checked

-- These also authenticate the actual guarded scheduler decoder and code span.
private theorem checked_nodes : ∀ node : graph.Index,
    VCGen.AtomicMethods.Node bytes (graph.node node).offset
      (.ordinary (graph.node node).instruction) := by
  decide +kernel

private theorem supported_nodes : ∀ node : graph.Index,
    supported (graph.node node).instruction = true := by
  decide +kernel

private theorem no_store (node : graph.Index) (initial : X86.State) :
    storeIntent (graph.node node).instruction initial = none := by
  rcases node with ⟨index, bound⟩
  have casesIndex : index = 0 ∨ index = 1 := by
    change index < 2 at bound
    omega
  rcases casesIndex with rfl | rfl <;> rfl

/-- Only these two ordinary effects and reads of the original caller slot are
allowed. OS authority still comes from the real current resources and gates. -/
def policy (original : Worker) : VCGen.Effects.Policy where
  Current _ := True
  AllowedRead _ read := read.kind = .stack ∧
    read.address = original.resources.callerAddress ∧ read.bytes = 8
  AllowedEffect _ instruction _ :=
    instruction = .movReg64 .rax .rdi ∨ instruction = .legacy .ret

/-- Fixed invocation data, with no premise about a future execution. -/
structure Invocation where
  profile : Profile
  tid : Nat
  base : Word
  original : Worker
  codeLoan : Borrowing.Subregion ⟨base, bytes.length⟩ original.resources.code.loan.region
  callerValue : Word

def Invocation.descriptor (call : Invocation) : Descriptor where
  profile := call.profile
  tid := call.tid
  bytes := bytes
  base := call.base
  graph := graph
  graphProfile := Sequential.CFG.defaultProfile
  structural := structural
  original := call.original
  codeLoan := call.codeLoan
  callerValue := call.callerValue
  policy _ := policy call.original

/-- Independent identity/ABI contract on the actual response state. RSP addition
has the machine model's modular word meaning. History is retained by Residual. -/
def identityPost (call : Invocation) (x : Word) : Assertion := fun state _ =>
  ∃ worker, state.workers[call.tid]? = some worker ∧
    worker.phase = .returned ∧ worker.context.registers .rax = x ∧
    worker.context.rip = call.callerValue ∧
    worker.context.registers .rsp = call.original.resources.callerAddress + 8 ∧
    worker.resources = call.original.resources

def noExit (call : Invocation) : CutAssertion call.descriptor := fun _ _ _ => False

private theorem current_code_loan {call : Invocation} {node : graph.Index}
    {state : S} {worker : Worker} (binding : Binding call.descriptor node state worker) :
    Borrowing.Subregion ⟨call.base, bytes.length⟩ worker.resources.code.loan.region := by
  rw [binding.resources]
  change Borrowing.Subregion ⟨call.base, bytes.length⟩ call.original.resources.code.loan.region
  exact call.codeLoan

/-- All non-read gates come from current WF, guarded decoding of exact bytes,
and the production non-store queue relation. No future success is assumed. -/
private theorem current_ready {call : Invocation} {node : graph.Index}
    {state : S} {worker : Worker} (frame : Frame call.descriptor state)
    (binding : Binding call.descriptor node state worker)
    (reads : ∃ units, ((graph.node node).instruction.operandReads
      (localCPU state worker)).mapM (fun read => checkRead state worker read call.profile) =
        .ok units) :
    OrdinaryReady state call.tid worker (graph.node node).instruction call.profile := by
  have workerValid := frame.wellFormed.2 worker (List.mem_of_getElem? binding.live)
  have fits := current_code_loan binding
  have fetched := (checked_nodes node).decoded (by decide +kernel)
    (VCGen.AtomicMethods.guarded_code frame.code fits) (fetchCPU state worker) rfl binding.pc
  exact ⟨binding.live, binding.running, workerValid.1.1, workerValid.1.2.1,
    fetched, supported_nodes node, (checked_nodes node).codeFits frame.code fits binding.pc,
    reads, ⟨⟨worker.pending, worker.nextStore⟩, .unchanged (no_store node _)⟩⟩

/-- Passive closure retains the saved context, phase and original resources;
RAM and FIFO are deliberately absent from this conclusion. -/
private theorem paused_binding {call : Invocation} {node : graph.Index}
    {before after : S} {history extended : Log} {worker : Worker}
    (binding : Binding call.descriptor node before worker)
    (paused : Pause call.profile call.tid (before, history) (after, extended)) :
    ∃ current, Binding call.descriptor node after current ∧ current.context = worker.context := by
  obtain ⟨current, live, saved⟩ := paused.saved binding.live
  exact ⟨current, ⟨live, saved.resources.trans binding.resources,
    saved.phase.trans binding.running, (congrArg Context.rip saved.context).trans binding.pc⟩,
    saved.context⟩

/-- Real stack admission and the executor's actual caller load follow from the
retained original borrowing read, even with a nonempty current FIFO. -/
private theorem current_caller {call : Invocation} {node : graph.Index}
    {state : S} {worker : Worker} (frame : Frame call.descriptor state)
    (binding : Binding call.descriptor node state worker)
    (stack : worker.context.registers .rsp = call.original.resources.callerAddress) :
    checkRead state worker ⟨.stack, worker.context.registers .rsp, 8⟩ call.profile = .ok () ∧
      readWord (localCPU state worker).memory (worker.context.registers .rsp) =
        .ok call.callerValue := by
  have caller : Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
      worker.resources.caller.identifier worker.resources.callerAddress = .ok call.callerValue := by
    rw [binding.resources]
    change Borrowing.loadWord64 state.world.legacy.shared call.original.resources.actor
      call.original.resources.caller.identifier call.original.resources.callerAddress =
        .ok call.callerValue
    exact frame.caller
  have currentStack : worker.context.registers .rsp = worker.resources.callerAddress := by
    rw [binding.resources]
    change worker.context.registers .rsp = call.original.resources.callerAddress
    exact stack
  have workerValid := frame.wellFormed.2 worker (List.mem_of_getElem? binding.live)
  refine ⟨?_, ?_⟩
  · simp [checkRead, currentStack, caller, Except.mapError]
  · rw [currentStack, local_original_caller frame.wellFormed workerValid]
    have word := (Borrowing.loadWord64_ok _ _ _ _ _ caller).choose_spec.2.2
    exact readWord_of_loadQWord _ _ _ word

private theorem queue_unchanged {state : S} {worker : Worker}
    {instruction : Sequential.Instruction} {update : Queue.Cursor} {profile : Profile}
    (intent : storeIntent instruction (localCPU state worker) = none)
    (queue : QueueEffect state worker instruction update profile) :
    update = ⟨worker.pending, worker.nextStore⟩ := by
  cases queue with
  | unchanged _ => rfl
  | enqueued stored _ => rw [intent] at stored; cases stored

-- Rewrite the production oneStep match before specializing its continuation
-- to dependent invocation/graph data. Every Bool choice still reaches K.
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

-- This helper is instantiated only with the RAX obtained from the real MOV.
private theorem ret_generated (call : Invocation) {state : S} {history : Log}
    {worker : Worker} (frame : Frame call.descriptor state)
    (binding : Binding call.descriptor retNode state worker) (x : Word)
    (captured : worker.context.registers .rax = x)
    (stack : worker.context.registers .rsp = call.original.resources.callerAddress)
    (canonicalCaller : canonical call.callerValue = true) :
    rwp call.descriptor (identityPost call x) (noExit call) 1 retNode state history := by
  change Box call.profile call.tid _ state history
  intro after extended paused
  have retained := frame.pause paused
  obtain ⟨current, bound, context⟩ := paused_binding binding paused
  have currentRax : current.context.registers .rax = x := by rw [context]; exact captured
  have currentRsp : current.context.registers .rsp = call.original.resources.callerAddress := by
    rw [context]
    exact stack
  obtain ⟨gate, read⟩ := current_caller retained bound currentRsp
  change checkRead after current ⟨.stack, (localCPU after current).registers .rsp, 8⟩
    call.profile = .ok () at gate
  have reads : ∃ units, ((Sequential.Instruction.legacy .ret).operandReads
      (localCPU after current)).mapM (fun operand => checkRead after current operand call.profile) =
        .ok units := by
    exact ⟨[()], by simp only [Sequential.Instruction.operandReads, List.mapM_cons,
      gate, ok_bind, List.mapM_nil, pure_ok]⟩
  have ready := current_ready retained bound reads
  let output : X86.State := { (localCPU after current).writeRegister .rsp
    (current.context.registers .rsp + 8) with rip := call.callerValue }
  let observed : Sequential.Observation :=
    ⟨.returned output, [⟨.stack, current.context.registers .rsp, 8⟩]⟩
  have executed (af : Bool) : Sequential.execute (localCPU after current) (.legacy .ret) af =
      .ok observed := by
    change readWord (localCPU after current).memory ((localCPU after current).registers .rsp) =
      .ok call.callerValue at read
    simp only [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
      executeRet, read, canonicalCaller, ↓reduceIte, ok_bind, pure_ok]
    rfl
  refine ⟨retained, current, bound, ready, ?_⟩
  change VCGen.Effects.oneStep (policy call.original) Sequential.FlagChoices.uniform
    (localCPU after current) (.legacy .ret) _
  refine oneStep_uniform_ok (instruction := .legacy .ret) rfl executed True.intro ?_
  refine ⟨?_, Or.inr rfl, (fun _ _ => True.intro), ?_, ?_⟩
  · intro operand member
    have same := List.mem_singleton.mp member
    subst operand
    exact ⟨rfl, currentRsp, rfl⟩
  · intro request impossible
    cases impossible
  · intro _af
    refine ⟨⟨output, Or.inr rfl⟩, ?_⟩
    intro update result queue finish
    have cursor := queue_unchanged (no_store retNode _) queue
    subst update
    cases finish with
    | next impossible => cases impossible
    | returned outcome =>
      cases outcome
      refine ⟨_, List.getElem?_set_self (List.getElem_of_getElem? bound.live).1,
        rfl, ?_, rfl, ?_, bound.resources⟩
      · change (output.registers .rax) = x
        simpa [output, X86.State.writeRegister, localCPU, cpu] using currentRax
      · change (output.registers .rsp) = call.original.resources.callerAddress + 8
        simpa [output, X86.State.writeRegister, localCPU, cpu] using
          congrArg (fun address : Word => address + 8) currentRsp

private theorem mov_generated (call : Invocation) {state : S} {history : Log}
    {worker : Worker} (frame : Frame call.descriptor state)
    (binding : Binding call.descriptor entry state worker) (x : Word)
    (input : worker.context.registers .rdi = x)
    (stack : worker.context.registers .rsp = call.original.resources.callerAddress)
    (canonicalCaller : canonical call.callerValue = true) :
    rwp call.descriptor (identityPost call x) (noExit call) 2 entry state history := by
  change Box call.profile call.tid _ state history
  intro after extended paused
  have retained := frame.pause paused
  obtain ⟨current, bound, context⟩ := paused_binding binding paused
  have currentInput : current.context.registers .rdi = x := by rw [context]; exact input
  have currentRsp : current.context.registers .rsp = call.original.resources.callerAddress := by
    rw [context]
    exact stack
  have reads : ∃ units, ((Sequential.Instruction.movReg64 .rax .rdi).operandReads
      (localCPU after current)).mapM (fun operand => checkRead after current operand call.profile) =
        .ok units := ⟨[], rfl⟩
  have ready := current_ready retained bound reads
  let output : X86.State := { (localCPU after current).writeRegister .rax
    (current.context.registers .rdi) with rip := current.context.rip + 3 }
  have executed (af : Bool) : Sequential.execute (localCPU after current)
      (.movReg64 .rax .rdi) af = .ok ⟨.next output, []⟩ := rfl
  have outputRax : output.registers .rax = x := by
    simpa [output, X86.State.writeRegister, localCPU, cpu] using currentInput
  have outputRsp : output.registers .rsp = call.original.resources.callerAddress := by
    simpa [output, X86.State.writeRegister, localCPU, cpu] using currentRsp
  have outputPC : output.rip = call.base + 3 := by
    change current.context.rip + 3 = call.base + 3
    have pc : current.context.rip = call.base + 0#64 := bound.pc
    exact congrArg (fun address : Word => address + 3) (pc.trans (BitVec.add_zero call.base))
  refine ⟨retained, current, bound, ready, ?_⟩
  change VCGen.Effects.oneStep (policy call.original) Sequential.FlagChoices.uniform
    (localCPU after current) (.movReg64 .rax .rdi) _
  refine oneStep_uniform_ok (instruction := .movReg64 .rax .rdi) rfl executed True.intro ?_
  refine ⟨(by intro operand member; cases member), Or.inl rfl, ?_, ?_, ?_⟩
  · intro final impossible
    cases impossible
  · intro request impossible
    cases impossible
  · intro af
    refine ⟨⟨output, Or.inl rfl⟩, ?_⟩
    intro update result queue finish
    have actual : step after (.issue call.tid af) call.profile = .ok result :=
      VCGen.ManagedRules.step_ordinary (checked_nodes entry) (by decide +kernel)
        retained.wellFormed bound.live bound.running retained.code (current_code_loan bound)
        bound.pc rfl reads queue (executed af) finish
    have nextFrame := retained.origin (step_origin actual)
    have cursor := queue_unchanged (no_store entry _) queue
    subst update
    cases finish with
    | returned impossible => cases impossible
    | next outcome =>
      cases outcome
      refine ⟨retNode, entry_edge, outputPC, ?_⟩
      have nextBinding : Binding call.descriptor retNode
          (install after call.tid after.world { current with context := .ofCPU output })
          { current with context := .ofCPU output } :=
        ⟨List.getElem?_set_self (List.getElem_of_getElem? bound.live).1,
          bound.resources, bound.running, outputPC⟩
      exact ret_generated call nextFrame nextBinding x outputRax outputRsp canonicalCaller

/-- Inhabit the generated fuel-2 residual from independent present admission,
entry RDI=x and the original caller ABI. Arbitrary admitted initial pending stores
and arbitrary passive peer/drain histories at BOTH boundaries are permitted. -/
theorem generated_identity (call : Invocation) {initial : S}
    (admitted : Admission call.descriptor initial) (x : Word)
    (entryPC : call.original.context.rip = call.base)
    (input : call.original.context.registers .rdi = x)
    (stack : call.original.context.registers .rsp = call.original.resources.callerAddress)
    (canonicalCaller : canonical call.callerValue = true) :
    rwp call.descriptor (identityPost call x) (noExit call) 2 entry initial [] := by
  apply mov_generated call admitted.frame (worker := call.original)
  · refine ⟨admitted.live, rfl, admitted.running, ?_⟩
    change call.original.context.rip = call.base + 0#64
    exact entryPC.trans (BitVec.add_zero call.base).symm
  · exact input
  · exact stack
  · exact canonicalCaller

/-- The positive client also starts an authentic Residual; no future-success
assumption or preassigned RAX value is part of this theorem's inputs. -/
theorem identity_residual (call : Invocation) {initial : S}
    (admitted : Admission call.descriptor initial) (x : Word)
    (entryPC : call.original.context.rip = call.base)
    (input : call.original.context.registers .rdi = x)
    (stack : call.original.context.registers .rsp = call.original.resources.callerAddress)
    (canonicalCaller : canonical call.callerValue = true) :
    Residual call.descriptor initial (identityPost call x) (noExit call) 2 entry initial [] :=
  Residual.start admitted (generated_identity call admitted x entryPC input stack canonicalCaller)

end EDSL.Tests.ResumableIdentity

#print axioms EDSL.Tests.ResumableIdentity.exact_decoding
#print axioms EDSL.Tests.ResumableIdentity.graph_checked
#print axioms EDSL.Tests.ResumableIdentity.structural
#print axioms EDSL.Tests.ResumableIdentity.generated_identity
#print axioms EDSL.Tests.ResumableIdentity.identity_residual
#audit_edsl
