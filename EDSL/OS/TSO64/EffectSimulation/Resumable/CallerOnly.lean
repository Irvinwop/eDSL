/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Resumable.Simulation
import EDSL.X86.Sequential.CallerOnly
import EDSL.X86.VCGen.PureCall
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Reuse the existing sequential generated WPs on a fixed reference memory while
real TSO64 execution reads its current local memory and FIFO. Admission combines
the production caller-only classification with independently checked guarded
native decoding. Only the original STACK8 caller read needs operand authority.

Current protected resources and code are regenerated at each paused boundary.
The reference CPU retains the actual worker's complete context; equality of
current shared RAM, an empty FIFO, and a successful future issue are unnecessary.
The effect policy below deliberately depends on current resource authority and
the finite instruction/read admission. Arbitrary memory-sensitive policies are
outside this adapter.

Returns project an independently established reference postcondition to the
actual returned context at that exact issue tick. The existing historical
Response/Done interface remains responsible for later publication. Ranks are
checked by the source cutpoint WP on the reference CPU; this adapter supplies
partial correctness and current enabledness, not scheduler termination or
fairness. Existing ISA, OS-resource, ordinary-RAM and target assumptions remain.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Resumable
open X86

/-- Static admission retains the guarded native dispatch check independently
of sequential CFG structure. The size bound is the existing native bridge's
bound, not an additional decoder or a finite execution bound. -/
structure CallerOnlyGraph (descriptor : Descriptor) : Prop where
  only : ∀ node : descriptor.graph.Index,
    Sequential.CallerOnly (descriptor.graph.node node).instruction
  native : ∀ node : descriptor.graph.Index,
    VCGen.AtomicMethods.Node descriptor.bytes (descriptor.graph.node node).offset
      (.ordinary (descriptor.graph.node node).instruction)
  byteBound : descriptor.bytes.length ≤ 64

/-- Read authority names the original loan's address and exact STACK8 width. -/
def callerRead (descriptor : Descriptor) (read : Sequential.Read) : Prop :=
  read.kind = .stack ∧ read.address = descriptor.original.resources.callerAddress ∧ read.bytes = 8

/-- The current OS resource obligation is independent of the CPU's RAM.
Ordinary retirement retains the world, so return checks the same authority. -/
def authorityCallerPolicy (descriptor : Descriptor) (state : S) : VCGen.Effects.Policy where
  Current _ := ResourcesValid state.world descriptor.original.resources
  AllowedRead _ read := callerRead descriptor read
  AllowedEffect _ instruction _ := Sequential.CallerOnly instruction

/-- A present live binding and the original sequential invariant evaluated on
the saved context with the reference RAM. It contains no future run witness. -/
def referenceInv (descriptor : Descriptor) (reference : Memory)
    (Inv : descriptor.graph.Index → X86.State → Prop) : CutAssertion descriptor :=
  fun node state _ => ∃ worker, Binding descriptor node state worker ∧ Inv node (cpu worker reference)

/-- Observation of the real returned worker at this issue tick. No claim about
the current world being the reference memory occurs in the return contract. -/
def returnedContext (descriptor : Descriptor) (Post : Context → Prop) : Assertion :=
  fun state _ => ∃ worker, state.workers[descriptor.tid]? = some worker ∧
    worker.phase = .returned ∧ worker.resources = descriptor.original.resources ∧ Post worker.context

theorem CallerOnlyGraph.valid {descriptor : Descriptor} (safe : CallerOnlyGraph descriptor) :
    Sequential.CFG.Valid descriptor.bytes descriptor.graph descriptor.graphProfile :=
  descriptor.structural.toReadOnly (fun node => (safe.only node).readOnly)

/-- The finite caller-only subset also passes the scheduler's ordinary gate. -/
theorem callerOnly_supported {instruction : Sequential.Instruction}
    (only : Sequential.CallerOnly instruction) : supported instruction = true := by
  cases instruction with
  | legacy old =>
    rcases only with contextOnly | rfl
    · cases old <;> simp_all [ContextOnly, supported]
    · rfl
  | _ => exact only.boolChoiceProfile

/-- The production queue sees neither ordinary store width. -/
theorem callerOnly_noStore {instruction : Sequential.Instruction}
    (only : Sequential.CallerOnly instruction) (before : X86.State) :
    storeIntent instruction before = none := by
  obtain ⟨narrow, wide⟩ := only.noStore before
  simp only [storeIntent, wide, narrow, Option.map_none]

/-- Passive origins preserve precisely the context used by reference proofs,
while allowing current RAM and the subject's pending FIFO to change. -/
theorem Binding.pause_reference {descriptor : Descriptor} {node : descriptor.graph.Index}
    {before after : S} {history extended : Log} {worker : Worker}
    (binding : Binding descriptor node before worker)
    (paused : Pause descriptor.profile descriptor.tid (before, history) (after, extended))
    (reference : Memory) :
    ∃ current, Binding descriptor node after current ∧ cpu current reference = cpu worker reference := by
  obtain ⟨current, live, saved⟩ := paused.saved binding.live
  refine ⟨current, ⟨live, saved.resources.trans binding.resources,
    saved.phase.trans binding.running, (congrArg Context.rip saved.context).trans binding.pc⟩, ?_⟩
  simp only [cpu, saved.context]

theorem Frame.current_resources {descriptor : Descriptor} {node : descriptor.graph.Index}
    {state : S} {worker : Worker} (frame : Frame descriptor state)
    (binding : Binding descriptor node state worker) :
    ResourcesValid state.world descriptor.original.resources := by
  have valid := (frame.wellFormed.2 worker (List.mem_of_getElem? binding.live)).1
  simpa only [binding.resources] using valid

/-- Original caller authority supplies the actual primitive read even when a
well-formed pending FIFO is nonempty. Current RSP identity is a separate input. -/
theorem Binding.current_caller {descriptor : Descriptor} {node : descriptor.graph.Index}
    {state : S} {worker : Worker} (binding : Binding descriptor node state worker)
    (frame : Frame descriptor state)
    (stack : worker.context.registers .rsp = descriptor.original.resources.callerAddress) :
    checkRead state worker ⟨.stack, worker.context.registers .rsp, 8⟩ descriptor.profile = .ok () ∧
      readWord (localCPU state worker).memory (worker.context.registers .rsp) =
        .ok descriptor.callerValue := by
  have caller : Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
      worker.resources.caller.identifier worker.resources.callerAddress = .ok descriptor.callerValue := by
    simpa only [binding.resources] using frame.caller
  have currentStack : worker.context.registers .rsp = worker.resources.callerAddress := by
    simpa only [binding.resources] using stack
  have workerValid := frame.wellFormed.2 worker (List.mem_of_getElem? binding.live)
  refine ⟨?_, ?_⟩
  · simp [checkRead, currentStack, caller, Except.mapError]
  · rw [currentStack, local_original_caller frame.wellFormed workerValid]
    have word := (Borrowing.loadWord64_ok _ _ _ _ _ caller).choose_spec.2.2
    exact readWord_of_loadQWord _ _ _ word

/-- RET's actual trace and the generated read contract identify current RSP;
an unrelated readable stack location cannot satisfy this obligation. -/
theorem callerOnly_rsp {descriptor : Descriptor} {before : X86.State}
    {instruction : Sequential.Instruction} {af : Bool} {observation : Sequential.Observation}
    (only : Sequential.CallerOnly instruction)
    (executed : Sequential.execute before instruction af = .ok observation)
    (allowed : ∀ read ∈ observation.reads, callerRead descriptor read)
    (ret : instruction = .legacy .ret) :
    before.registers .rsp = descriptor.original.resources.callerAddress := by
  have footprint := only.reads executed
  rw [ite_eq_left ret] at footprint
  have member : (⟨.stack, before.registers .rsp, 8⟩ : Sequential.Read) ∈ observation.reads := by
    rw [footprint]
    exact List.mem_singleton_self _
  exact (allowed _ member).2.1

/-- Derive every current issue gate from static byte admission, present WF and
one successful reference observation's independently supplied read contract.
No successor CPU or successful OS issue is an input. -/
theorem CallerOnlyGraph.ready {descriptor : Descriptor} (safe : CallerOnlyGraph descriptor)
    {node : descriptor.graph.Index} {state : S} {worker : Worker} {reference : Memory}
    {af : Bool} {observation : Sequential.Observation}
    (frame : Frame descriptor state) (binding : Binding descriptor node state worker)
    (executed : Sequential.execute (cpu worker reference) (descriptor.graph.node node).instruction af =
      .ok observation)
    (allowed : ∀ read ∈ observation.reads, callerRead descriptor read) :
    OrdinaryReady state descriptor.tid worker (descriptor.graph.node node).instruction descriptor.profile := by
  have workerValid := frame.wellFormed.2 worker (List.mem_of_getElem? binding.live)
  have fits : Borrowing.Subregion ⟨descriptor.base, descriptor.bytes.length⟩
      worker.resources.code.loan.region := by
    simpa only [binding.resources] using descriptor.codeLoan
  have fetched := (safe.native node).decoded safe.byteBound
    (VCGen.AtomicMethods.guarded_code frame.code fits) (fetchCPU state worker) rfl binding.pc
  have checkedReads : ∃ units, ((descriptor.graph.node node).instruction.operandReads
      (localCPU state worker)).mapM (fun read => checkRead state worker read descriptor.profile) =
        .ok units := by
    rw [(safe.only node).operandReads (localCPU state worker)]
    by_cases ret : (descriptor.graph.node node).instruction = .legacy .ret
    · rw [ite_eq_left ret]
      have stack : worker.context.registers .rsp = descriptor.original.resources.callerAddress :=
        callerOnly_rsp (safe.only node) executed allowed ret
      have checked := (binding.current_caller frame stack).1
      refine ⟨[()], ?_⟩
      simp only [localCPU, cpu, List.mapM_cons, List.mapM_nil, checked, ok_bind, pure_ok]
    · rw [ite_eq_right ret]
      exact ⟨[], rfl⟩
  exact ⟨binding.live, binding.running, workerValid.1.1, workerValid.1.2.1,
    fetched, callerOnly_supported (safe.only node), (safe.native node).codeFits frame.code fits binding.pc,
    checkedReads, ⟨⟨worker.pending, worker.nextStore⟩,
      .unchanged (callerOnly_noStore (safe.only node) _)⟩⟩

/-- Transport the complete successful production observation from reference
RAM to current local RAM. The only operand premise is regenerated from the
original protected caller, at the actual RSP identified by the source WP. -/
theorem Binding.execute_reference {descriptor : Descriptor} {node : descriptor.graph.Index}
    {state : S} {worker : Worker} {reference : Memory} {af : Bool}
    {observation : Sequential.Observation} (binding : Binding descriptor node state worker)
    (frame : Frame descriptor state)
    (only : Sequential.CallerOnly (descriptor.graph.node node).instruction)
    (caller : readWord reference descriptor.original.resources.callerAddress = .ok descriptor.callerValue)
    (executed : Sequential.execute (cpu worker reference) (descriptor.graph.node node).instruction af =
      .ok observation)
    (allowed : ∀ read ∈ observation.reads, callerRead descriptor read) :
    Sequential.execute (localCPU state worker) (descriptor.graph.node node).instruction af =
      .ok (observation.mapMemory (fun _ => (localCPU state worker).memory)) := by
  have agree : (descriptor.graph.node node).instruction = .legacy .ret →
      readWord (localCPU state worker).memory ((cpu worker reference).registers .rsp) =
        readWord (cpu worker reference).memory ((cpu worker reference).registers .rsp) := by
    intro ret
    have stack : worker.context.registers .rsp = descriptor.original.resources.callerAddress :=
      callerOnly_rsp only executed allowed ret
    have actual := (binding.current_caller frame stack).2
    change readWord (localCPU state worker).memory (worker.context.registers .rsp) =
      readWord reference (worker.context.registers .rsp)
    rw [actual, stack, caller]
  have moved := only.execute_memory_eq (cpu worker reference) (localCPU state worker).memory af agree
  rw [executed] at moved
  exact moved

/-- A real semantic queue/finish pair identifies an actual production issue,
its successor protected frame, and full-CPU reification. This reuses the checked
native rule and does not ask clients for successful successor states. -/
theorem CallerOnlyGraph.finish {descriptor : Descriptor} (safe : CallerOnlyGraph descriptor)
    {node : descriptor.graph.Index} {state : S} {worker : Worker} {af : Bool}
    {observation : Sequential.Observation} {update : Queue.Cursor} {result : S × O}
    (frame : Frame descriptor state) (binding : Binding descriptor node state worker)
    (ready : OrdinaryReady state descriptor.tid worker (descriptor.graph.node node).instruction descriptor.profile)
    (executed : Sequential.execute (localCPU state worker) (descriptor.graph.node node).instruction af =
      .ok observation)
    (queue : QueueEffect state worker (descriptor.graph.node node).instruction update descriptor.profile)
    (finish : FinishEffect state descriptor.tid worker update.pending observation result update.nextStore) :
    step state (.issue descriptor.tid af) descriptor.profile = .ok result ∧
      Frame descriptor result.1 ∧ Reifies descriptor.tid result observation := by
  have fits : Borrowing.Subregion ⟨descriptor.base, descriptor.bytes.length⟩
      worker.resources.code.loan.region := by
    simpa only [binding.resources] using descriptor.codeLoan
  have actual := VCGen.ManagedRules.step_ordinary (safe.native node) safe.byteBound
    frame.wellFormed binding.live binding.running frame.code fits binding.pc ready.admitted
    ready.reads queue executed finish
  have stepped : Sequential.step af (localCPU state worker) = .ok observation :=
    (Sequential.step_eq_execute af (binding.decoded frame)).trans executed
  have effect : OrdinaryEffect state descriptor.tid worker (descriptor.graph.node node).instruction af
      result descriptor.profile :=
    .intro ready.admitted ready.bounds (binding.decoded frame) ready.reads queue stepped finish
  obtain ⟨observed, vector, reified, _world⟩ := ordinary_reifies binding.live binding.running effect
  have expected : Sequential.stepWith (Sequential.FlagChoices.uniform af) (localCPU state worker) =
      .ok observation := by
    rw [Sequential.stepWith_eq_executeWith _ (binding.decoded frame),
      Sequential.executeWith_uniform _ _ af (safe.only node).boolChoiceProfile]
    exact executed
  have same : observed = observation := Except.ok.inj (vector.symm.trans expected)
  subst observed
  exact ⟨actual, frame.origin (step_origin actual), reified⟩

private theorem cpu_reference {worker : Worker} {output : X86.State} {reference : Memory}
    (context : worker.context = Context.ofCPU output) (memory : output.memory = reference) :
    cpu worker reference = output := by
  unfold cpu
  rw [context]
  change { output with memory := reference } = output
  rw [← memory]

/-- Full actual successor context is enough to reconstruct the next reference
CPU, including all GPRs, flags and RIP. Only reference RAM is framed here. -/
theorem Frame.reference_next {descriptor : Descriptor} {destination : descriptor.graph.Index}
    {result : S × O} {observation : Sequential.Observation} {output : X86.State}
    {reference currentMemory : Memory} (frame : Frame descriptor result.1)
    (reified : Reifies descriptor.tid result observation)
    (next : observation.result = .next { output with memory := currentMemory })
    (pc : output.rip = descriptor.base + BitVec.ofNat 64 (descriptor.graph.node destination).offset)
    (memory : output.memory = reference) :
    ∃ worker, Binding descriptor destination result.1 worker ∧ cpu worker reference = output := by
  obtain ⟨worker, live, coherent⟩ := reified
  rw [next] at coherent
  obtain ⟨_label, running, actualCPU⟩ := coherent
  obtain ⟨original, originalLive, resources⟩ := frame.worker
  have same : worker = original := Option.some.inj (live.symm.trans originalLive)
  have context : worker.context = Context.ofCPU output := congrArg Context.ofCPU actualCPU
  refine ⟨worker, ⟨live, (congrArg Worker.resources same).trans resources, running, ?_⟩,
    cpu_reference context memory⟩
  exact (congrArg X86.State.rip actualCPU).trans pc

/-- Project at the actual returned tick. This establishes no memory-sensitive
postcondition in a later publication world. -/
theorem Frame.reference_returned {descriptor : Descriptor} {result : S × O}
    {observation : Sequential.Observation} {output : X86.State} {currentMemory : Memory}
    {Post : Context → Prop} {history : Log} (frame : Frame descriptor result.1)
    (reified : Reifies descriptor.tid result observation)
    (returned : observation.result = .returned { output with memory := currentMemory })
    (post : Post (Context.ofCPU output)) : returnedContext descriptor Post result.1 history := by
  obtain ⟨worker, live, coherent⟩ := reified
  rw [returned] at coherent
  obtain ⟨_label, phase, actualCPU⟩ := coherent
  obtain ⟨original, originalLive, resources⟩ := frame.worker
  have same : worker = original := Option.some.inj (live.symm.trans originalLive)
  have context : worker.context = Context.ofCPU output := congrArg Context.ofCPU actualCPU
  refine ⟨worker, live, phase, (congrArg Worker.resources same).trans resources, ?_⟩
  rw [context]
  exact post

/-- Lift an existing generated sequential cutpoint WP. Both choices execute the
production semantics on reference RAM. Every real pause regenerates current
code/read/resource/queue authority before using exact observation transport.
The source's independent read contract may include reference-memory facts;
only its implication to original caller authority is needed in the OS policy. -/
theorem rwp_of_callerOnly_cutpointWP
    (descriptor : Descriptor) (safe : CallerOnlyGraph descriptor) (reference : Memory)
    (policy : ∀ state, descriptor.policy state = authorityCallerPolicy descriptor state)
    (referenceCode : CodeAt reference descriptor.base descriptor.bytes)
    (referenceCaller : readWord reference descriptor.original.resources.callerAddress =
      .ok descriptor.callerValue)
    (Post : X86.State → Prop) (ContextPost : Context → Prop)
    (project : ∀ output, Post output → ContextPost (Context.ofCPU output))
    (AllowedRead : X86.State → Sequential.Read → Prop)
    (permits : ∀ before read, AllowedRead before read → callerRead descriptor read)
    (Inv : descriptor.graph.Index → X86.State → Prop)
    (rank : descriptor.graph.Index → X86.State → Nat) (budget fuel : Nat)
    (node : descriptor.graph.Index) (state : S) (history : Log) (worker : Worker)
    (frame : Frame descriptor state) (binding : Binding descriptor node state worker)
    (generated : VCGen.Cutpoints.wp descriptor.graph descriptor.base Post AllowedRead Inv rank budget
      fuel node (cpu worker reference)) :
    rwp descriptor (returnedContext descriptor ContextPost) (referenceInv descriptor reference Inv)
      fuel node state history := by
  induction fuel generalizing node state history worker with
  | zero => exact False.elim generated
  | succ fuel induction =>
    intro current past paused
    have currentFrame := frame.pause paused
    obtain ⟨subject, currentBinding, referenceSame⟩ := binding.pause_reference paused reference
    have currentWP : VCGen.Cutpoints.wp descriptor.graph descriptor.base Post AllowedRead Inv rank budget
        (fuel + 1) node (cpu subject reference) := by
      rw [referenceSame]
      exact generated
    have witness : ∃ observation,
        Sequential.execute (cpu subject reference) (descriptor.graph.node node).instruction false =
          .ok observation ∧ ∀ read ∈ observation.reads, callerRead descriptor read := by
      have one := currentWP false
      cases executed : Sequential.execute (cpu subject reference) (descriptor.graph.node node).instruction false with
      | error fault => simp only [executed] at one
      | ok observation =>
        simp only [executed] at one
        exact ⟨observation, rfl, fun read member => permits _ read (one.1 read member)⟩
    obtain ⟨witnessObservation, witnessExecution, witnessReads⟩ := witness
    have ready := safe.ready currentFrame currentBinding witnessExecution witnessReads
    refine ⟨currentFrame, subject, currentBinding, ready, ?_⟩
    rw [policy current]
    refine ⟨currentFrame.current_resources currentBinding, ?_⟩
    intro af
    have one := currentWP af
    cases executed : Sequential.execute (cpu subject reference) (descriptor.graph.node node).instruction af with
    | error fault => simp only [executed] at one
    | ok observation =>
      simp only [executed] at one
      have allowed : ∀ read ∈ observation.reads, callerRead descriptor read :=
        fun read member => permits _ read (one.1 read member)
      have moved := currentBinding.execute_reference currentFrame (safe.only node)
        referenceCaller executed allowed
      have vector : Sequential.executeWith (localCPU current subject)
          (descriptor.graph.node node).instruction (Sequential.FlagChoices.uniform af) =
          .ok (observation.mapMemory (fun _ => (localCPU current subject).memory)) := by
        rw [Sequential.executeWith_uniform _ _ af (safe.only node).boolChoiceProfile]
        exact moved
      rw [vector]
      obtain ⟨output, outputMemory, next | ⟨returned, _ret⟩⟩ := (safe.only node).result executed
      · have mappedNext : (observation.mapMemory (fun _ => (localCPU current subject).memory)).result =
            .next { output with memory := (localCPU current subject).memory } := by
          simp only [Sequential.Observation.mapMemory, next, StepResult.mapMemory]
        have follows := one.2
        simp only [next] at follows
        obtain ⟨destination, nextPC, continuation⟩ := follows
        have referenceDecoded : Sequential.decodeAt (cpu subject reference) =
            .ok (descriptor.graph.node node).instruction :=
          descriptor.structural.decoded referenceCode node (cpu subject reference) rfl currentBinding.pc
        have referenceStep := (Sequential.step_eq_execute af referenceDecoded).trans executed
        obtain ⟨actualDestination, edge, actualPC, _memory, _code⟩ :=
          safe.valid.next referenceCode node currentBinding.pc referenceStep next
        have same : actualDestination = destination := safe.valid.wordOffset_injective
          ((BitVec.add_right_inj descriptor.base).mp (actualPC.symm.trans nextPC))
        subst actualDestination
        refine ⟨allowed, safe.only node, ?_, ?_,
          ⟨{ output with memory := (localCPU current subject).memory }, .inl mappedNext⟩, ?_⟩
        · intro _final _returned
          exact currentFrame.current_resources currentBinding
        · intro request impossible
          rw [mappedNext] at impossible
          cases impossible
        · intro update result queue finish
          obtain ⟨_actual, afterFrame, reified⟩ :=
            safe.finish currentFrame currentBinding ready moved queue finish
          obtain ⟨nextWorker, nextBinding, referenceCPU⟩ :=
            afterFrame.reference_next reified mappedNext nextPC outputMemory
          change cpu nextWorker reference = output at referenceCPU
          simp only [Follow, mappedNext]
          refine ⟨destination, edge, nextPC, ?_⟩
          cases isCut : descriptor.graph.cutpoint destination with
          | true =>
            simp only [isCut, ↓reduceIte] at continuation ⊢
            refine ⟨nextWorker, nextBinding, ?_⟩
            rw [referenceCPU]
            exact continuation.1
          | false =>
            simp only [isCut, Bool.false_eq_true, ite_false] at continuation ⊢
            apply induction (node := destination) (state := result.1)
              (history := issueLog descriptor.tid current past af result) (worker := nextWorker)
              afterFrame nextBinding
            simpa only [referenceCPU] using continuation
      · have mappedReturned : (observation.mapMemory (fun _ => (localCPU current subject).memory)).result =
            .returned { output with memory := (localCPU current subject).memory } := by
          simp only [Sequential.Observation.mapMemory, returned, StepResult.mapMemory]
        have referencePost : Post output := by simpa only [returned] using one.2
        refine ⟨allowed, safe.only node, ?_, ?_,
          ⟨{ output with memory := (localCPU current subject).memory }, .inr mappedReturned⟩, ?_⟩
        · intro _final _returned
          exact currentFrame.current_resources currentBinding
        · intro request impossible
          rw [mappedReturned] at impossible
          cases impossible
        · intro update result queue finish
          obtain ⟨_actual, afterFrame, reified⟩ :=
            safe.finish currentFrame currentBinding ready moved queue finish
          simp only [Follow, mappedReturned]
          exact afterFrame.reference_returned reified mappedReturned (project output referencePost)

/-- Thin sparse-cutpoint integration with eager restart and the existing
historical response simulation. No client supplies instruction-local VCs. -/
def callerOnlyAnnotations
    (descriptor : Descriptor) (safe : CallerOnlyGraph descriptor) (reference : Memory)
    (policy : ∀ state, descriptor.policy state = authorityCallerPolicy descriptor state)
    (referenceCode : CodeAt reference descriptor.base descriptor.bytes)
    (referenceCaller : readWord reference descriptor.original.resources.callerAddress =
      .ok descriptor.callerValue)
    (Post : X86.State → Prop) (ContextPost : Context → Prop)
    (project : ∀ output, Post output → ContextPost (Context.ofCPU output))
    (AllowedRead : X86.State → Sequential.Read → Prop)
    (permits : ∀ before read, AllowedRead before read → callerRead descriptor read)
    (annotations : VCGen.Cutpoints.Annotations descriptor.bytes descriptor.graph descriptor.base Post AllowedRead) :
    Annotations descriptor (returnedContext descriptor ContextPost) where
  Inv := referenceInv descriptor reference annotations.Inv
  blocks cut state history worker isCut frame binding invariant := by
    obtain ⟨current, currentBinding, inside⟩ := invariant
    have same : current = worker := Option.some.inj (currentBinding.live.symm.trans binding.live)
    subst current
    have generated := annotations.blocks cut (cpu worker reference) isCut
      ⟨referenceCode, binding.pc⟩ inside
    exact rwp_of_callerOnly_cutpointWP descriptor safe reference policy referenceCode referenceCaller
      Post ContextPost project AllowedRead permits annotations.Inv annotations.rank
      (annotations.rank cut (cpu worker reference)) (descriptor.graph.depth cut + 1)
      cut state history worker frame binding generated

/-- Bounded clients without edges into a cutpoint reuse their existing Result
contract and exact source WP. The projection extracts a state contract from
that evidence; this lemma neither assumes the contract nor regenerates it. -/
theorem cutpointWP_of_bounded_noCutSuccessor
    {bytes : List Byte} {graph : Sequential.CFG.Graph} {graphProfile : Sequential.CFG.Profile}
    (valid : Sequential.CFG.Valid bytes graph graphProfile) (base : Word)
    (noCut : ∀ source destination : graph.Index,
      graph.Edge source destination → graph.cutpoint destination = false)
    (AllowedRead : X86.State → Sequential.Read → Prop) (Post : X86.State → Prop)
    (fuel : Nat) (node : graph.Index) (initial : X86.State)
    (Evidence : Sequential.Result → Prop)
    (project : ∀ result, Evidence result → Post result.state)
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (generated : VCGen.wp graph base AllowedRead fuel node initial Evidence) :
    VCGen.Cutpoints.wp graph base Post AllowedRead (fun _ _ => False) (fun _ _ => 0) 0
      fuel node initial := by
  induction fuel generalizing node initial Evidence with
  | zero => exact False.elim generated
  | succ fuel induction =>
    intro af
    have one := generated af
    cases executed : Sequential.execute initial (graph.node node).instruction af with
    | error fault => simp only [executed] at one
    | ok observation =>
      simp only [executed] at one ⊢
      refine ⟨one.1, ?_⟩
      have follows := one.2
      cases outcome : observation.result with
      | returned output =>
        simp only [outcome] at follows ⊢
        exact project ⟨output, 1, observation.reads⟩ follows
      | atomic event output => simp only [outcome] at follows
      | syscall request => simp only [outcome] at follows
      | next output =>
        simp only [outcome] at follows ⊢
        obtain ⟨destination, nextPC, continuation⟩ := follows
        have decoded : Sequential.decodeAt initial = .ok (graph.node node).instruction :=
          valid.decoded code node initial rfl pc
        have stepped := (Sequential.step_eq_execute af decoded).trans executed
        obtain ⟨actualDestination, edge, actualPC, _memory, nextCode⟩ :=
          valid.next code node pc stepped outcome
        have same : actualDestination = destination := valid.wordOffset_injective
          ((BitVec.add_right_inj base).mp (actualPC.symm.trans nextPC))
        subst actualDestination
        refine ⟨destination, nextPC, ?_⟩
        rw [noCut node destination edge]
        apply induction (node := destination) (initial := output)
          (Evidence := fun result => Evidence (result.prepend 1 observation.reads))
          (fun result evidence => project (result.prepend 1 observation.reads) evidence)
          nextCode nextPC continuation

private theorem referenceInv_false (descriptor : Descriptor) (reference : Memory) :
    referenceInv descriptor reference (fun _ _ => False) = (fun _ _ _ => False) := by
  funext node state history
  apply propext
  constructor
  · rintro ⟨_worker, _binding, impossible⟩
    exact impossible
  · intro impossible
    exact False.elim impossible

/-- Bounded generated clients need only a static no-cut-successor fact and a
projection from their already proved Result evidence. Both original Bool
choices and the original fuel remain intact. Exits are impossible. -/
theorem rwp_of_callerOnly_wp
    (descriptor : Descriptor) (safe : CallerOnlyGraph descriptor) (reference : Memory)
    (policy : ∀ state, descriptor.policy state = authorityCallerPolicy descriptor state)
    (referenceCode : CodeAt reference descriptor.base descriptor.bytes)
    (referenceCaller : readWord reference descriptor.original.resources.callerAddress =
      .ok descriptor.callerValue)
    (noCut : ∀ source destination : descriptor.graph.Index,
      descriptor.graph.Edge source destination → descriptor.graph.cutpoint destination = false)
    (ContextPost : Context → Prop) (Evidence : Sequential.Result → Prop)
    (project : ∀ result, Evidence result → ContextPost (Context.ofCPU result.state))
    (AllowedRead : X86.State → Sequential.Read → Prop)
    (permits : ∀ before read, AllowedRead before read → callerRead descriptor read)
    (fuel : Nat) (node : descriptor.graph.Index) (state : S) (history : Log) (worker : Worker)
    (frame : Frame descriptor state) (binding : Binding descriptor node state worker)
    (generated : VCGen.wp descriptor.graph descriptor.base AllowedRead fuel node
      (cpu worker reference) Evidence) :
    rwp descriptor (returnedContext descriptor ContextPost) (fun _ _ _ => False)
      fuel node state history := by
  have sequential := cutpointWP_of_bounded_noCutSuccessor safe.valid descriptor.base noCut
    AllowedRead (fun output => ContextPost (Context.ofCPU output)) fuel node (cpu worker reference)
    Evidence project referenceCode binding.pc generated
  have lifted := rwp_of_callerOnly_cutpointWP descriptor safe reference policy referenceCode referenceCaller
    (fun output => ContextPost (Context.ofCPU output)) ContextPost (fun _ post => post)
    AllowedRead permits (fun _ _ => False) (fun _ _ => 0) 0 fuel node state history worker
    frame binding sequential
  rw [referenceInv_false] at lifted
  exact lifted

/-- The canonical initial reference memory is the actual admitted local view,
including any well-formed incoming FIFO. No earlier issue history is invented. -/
theorem Admission.reference_code {descriptor : Descriptor} {initial : S}
    (admitted : Admission descriptor initial) :
    CodeAt (localCPU initial descriptor.original).memory descriptor.base descriptor.bytes := by
  exact VCGen.ManagedRules.local_code admitted.wellFormed
    (admitted.wellFormed.2 descriptor.original (List.mem_of_getElem? admitted.live))
    admitted.code descriptor.codeLoan

theorem Admission.reference_caller {descriptor : Descriptor} {initial : S}
    (admitted : Admission descriptor initial) :
    readWord (localCPU initial descriptor.original).memory descriptor.original.resources.callerAddress =
      .ok descriptor.callerValue := by
  have workerValid := admitted.wellFormed.2 descriptor.original (List.mem_of_getElem? admitted.live)
  rw [local_original_caller admitted.wellFormed workerValid]
  have word := (Borrowing.loadWord64_ok _ _ _ _ _ admitted.caller).choose_spec.2.2
  exact readWord_of_loadQWord _ _ _ word

#print axioms CallerOnlyGraph.valid
#print axioms callerOnly_supported
#print axioms callerOnly_noStore
#print axioms Binding.pause_reference
#print axioms Frame.current_resources
#print axioms Binding.current_caller
#print axioms callerOnly_rsp
#print axioms CallerOnlyGraph.ready
#print axioms Binding.execute_reference
#print axioms CallerOnlyGraph.finish
#print axioms Frame.reference_next
#print axioms Frame.reference_returned
#print axioms rwp_of_callerOnly_cutpointWP
#print axioms callerOnlyAnnotations
#print axioms cutpointWP_of_bounded_noCutSuccessor
#print axioms rwp_of_callerOnly_wp
#print axioms Admission.reference_code
#print axioms Admission.reference_caller

end EDSL.OS.TSO64.EffectSimulation.Resumable

#audit_edsl
