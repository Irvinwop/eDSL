/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.Head
import EDSL.X86.Sequential.CallerOnly

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Caller-only reference execution for one selected ordinary mixed node. The
mixed descriptor's checked caps authenticate current decoding and code bounds;
other nodes may be locked, and no separate byte-window bound is imposed here.

The reference CPU uses the actual worker's entire saved context. Its successful
observation and exact caller-read contract supply present OS readiness, while
the protected original caller supplies agreement with current local RAM. The
actual pending FIFO and next-store counter remain those of the current worker.
Complete observation transport retains every read, result constructor and CPU
field, changing only the carried memory to that actual local view.

This is a current-head bridge under the imported target, resource and memory
contracts. It supplies no recursive simulation, future issue, fairness,
termination, ABI or corpus claim.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

/-- Authority for the original protected STACK8 caller read. -/
def callerRead (d : Descriptor) (read : Sequential.Read) : Prop :=
  read.kind = .stack ∧ read.address = d.original.resources.callerAddress ∧ read.bytes = 8

/-- Current authority is independent of the reference CPU's memory. -/
def authorityCallerPolicy (d : Descriptor) (state : S) : VCGen.Effects.Policy where
  Current _ := ResourcesValid state.world d.original.resources
  AllowedRead _ read := callerRead d read
  AllowedEffect _ instruction _ := Sequential.CallerOnly instruction

/-- The finite caller-only subset passes the ordinary scheduler gate. -/
theorem callerOnly_supported {instruction : Sequential.Instruction}
    (only : Sequential.CallerOnly instruction) : supported instruction = true := by
  cases instruction with
  | legacy old =>
    rcases only with contextOnly | rfl
    · cases old <;> simp_all [ContextOnly, supported]
    · rfl
  | _ => exact only.boolChoiceProfile

/-- Neither ordinary store width contributes an intent to the real queue. -/
theorem callerOnly_noStore {instruction : Sequential.Instruction}
    (only : Sequential.CallerOnly instruction) (before : X86.State) :
    storeIntent instruction before = none := by
  obtain ⟨narrow, wide⟩ := only.noStore before
  simp only [storeIntent, wide, narrow, Option.map_none]

theorem Frame.current_resources {d : Descriptor} {node : d.graph.Index}
    {state : S} {worker : Worker} (frame : Frame d state)
    (binding : Binding d node state worker) : ResourcesValid state.world d.original.resources := by
  simpa only [binding.resources] using binding.resourcesValid frame

/-- A current protected loan authenticates the actual caller primitive even
with a nonempty well-formed own FIFO. RSP identity is a separate obligation. -/
theorem Binding.current_caller {d : Descriptor} {node : d.graph.Index}
    {state : S} {worker : Worker} (binding : Binding d node state worker)
    (frame : Frame d state)
    (stack : worker.context.registers .rsp = d.original.resources.callerAddress) :
    checkRead state worker ⟨.stack, worker.context.registers .rsp, 8⟩ d.profile = .ok () ∧
      readWord (localCPU state worker).memory (worker.context.registers .rsp) =
        .ok d.callerValue := by
  have caller : Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
      worker.resources.caller.identifier worker.resources.callerAddress = .ok d.callerValue := by
    simpa only [binding.resources] using frame.caller
  have currentStack : worker.context.registers .rsp = worker.resources.callerAddress := by
    simpa only [binding.resources] using stack
  have workerValid := frame.wellFormed.2 worker (List.mem_of_getElem? binding.live)
  refine ⟨?_, ?_⟩
  · simp [checkRead, currentStack, caller, Except.mapError]
  · rw [currentStack, local_original_caller frame.wellFormed workerValid]
    have word := (Borrowing.loadWord64_ok _ _ _ _ _ caller).choose_spec.2.2
    exact readWord_of_loadQWord _ _ _ word

/-- Successful RET exposes its actual RSP in the read trace. The supplied
read contract identifies that address with the original protected caller. -/
theorem callerOnly_rsp {d : Descriptor} {before : X86.State}
    {instruction : Sequential.Instruction} {af : Bool} {observation : Sequential.Observation}
    (only : Sequential.CallerOnly instruction)
    (executed : Sequential.execute before instruction af = .ok observation)
    (allowed : ∀ read ∈ observation.reads, callerRead d read)
    (ret : instruction = .legacy .ret) :
    before.registers .rsp = d.original.resources.callerAddress := by
  have footprint := only.reads executed
  rw [ite_eq_left ret] at footprint
  have member : (⟨.stack, before.registers .rsp, 8⟩ : Sequential.Read) ∈ observation.reads := by
    rw [footprint]
    exact List.mem_singleton_self _
  exact (allowed _ member).2.1

/-- Derive real present-state gates from the selected ordinary node and one
successful reference execution. No successor or future OS step is an input.
The mixed descriptor supplies guarded decoding and bounds under its own caps. -/
theorem Binding.callerOnly_ready {d : Descriptor} {node : d.graph.Index}
    {state : S} {worker : Worker} {instruction : Sequential.Instruction} {reference : Memory}
    {af : Bool} {observation : Sequential.Observation} (binding : Binding d node state worker)
    (frame : Frame d state)
    (selected : (d.graph.node node).instruction = .ordinary instruction)
    (only : Sequential.CallerOnly instruction)
    (executed : Sequential.execute (cpu worker reference) instruction af = .ok observation)
    (allowed : ∀ read ∈ observation.reads, callerRead d read) :
    OrdinaryReady state d.tid worker instruction d.profile d.family := by
  have workerValid := frame.wellFormed.2 worker (List.mem_of_getElem? binding.live)
  have fetched : decode (fetchCPU state worker) d.family = .ok (.ordinary instruction) := by
    simpa only [selected] using binding.fetched frame
  have bounds : TSO64.codeFits worker instruction.length := by
    simpa only [selected, VCGen.MixedCFG.instructionLength] using binding.codeFits frame
  have checkedReads : ∃ units, (instruction.operandReads (localCPU state worker)).mapM
      (fun read => checkRead state worker read d.profile) = .ok units := by
    rw [only.operandReads (localCPU state worker)]
    by_cases ret : instruction = .legacy .ret
    · rw [ite_eq_left ret]
      have stack : worker.context.registers .rsp = d.original.resources.callerAddress :=
        callerOnly_rsp only executed allowed ret
      have checked := (binding.current_caller frame stack).1
      refine ⟨[()], ?_⟩
      simp only [localCPU, cpu, List.mapM_cons, List.mapM_nil, checked, ok_bind, pure_ok]
    · rw [ite_eq_right ret]
      exact ⟨[], rfl⟩
  exact ⟨binding.live, binding.running, workerValid.1.1, workerValid.1.2.1,
    fetched, callerOnly_supported only, bounds, checkedReads,
    ⟨⟨worker.pending, worker.nextStore⟩, .unchanged (callerOnly_noStore only _)⟩⟩

/-- Transport the full reference observation to actual local RAM. Selection
names the current ordinary graph node; execution uses its already decoded
instruction, so only RET needs operand-memory agreement. -/
theorem Binding.execute_reference {d : Descriptor} {node : d.graph.Index}
    {state : S} {worker : Worker} {instruction : Sequential.Instruction} {reference : Memory}
    {af : Bool} {observation : Sequential.Observation} (binding : Binding d node state worker)
    (frame : Frame d state)
    (_selected : (d.graph.node node).instruction = .ordinary instruction)
    (only : Sequential.CallerOnly instruction)
    (caller : readWord reference d.original.resources.callerAddress = .ok d.callerValue)
    (executed : Sequential.execute (cpu worker reference) instruction af = .ok observation)
    (allowed : ∀ read ∈ observation.reads, callerRead d read) :
    Sequential.execute (localCPU state worker) instruction af =
      .ok (observation.mapMemory (fun _ => (localCPU state worker).memory)) := by
  have agree : instruction = .legacy .ret →
      readWord (localCPU state worker).memory ((cpu worker reference).registers .rsp) =
        readWord (cpu worker reference).memory ((cpu worker reference).registers .rsp) := by
    intro ret
    have stack : worker.context.registers .rsp = d.original.resources.callerAddress :=
      callerOnly_rsp only executed allowed ret
    have actual := (binding.current_caller frame stack).2
    change readWord (localCPU state worker).memory (worker.context.registers .rsp) =
      readWord reference (worker.context.registers .rsp)
    rw [actual, stack, caller]
  have moved := only.execute_memory_eq (cpu worker reference) (localCPU state worker).memory af agree
  rw [executed] at moved
  exact moved

/-- Build the ordinary head using current local code, authenticated decoding,
resource authority and the complete transported reference observation. -/
theorem Binding.callerOnly_head {d : Descriptor} {node : d.graph.Index}
    {state : S} {worker : Worker} {instruction : Sequential.Instruction} {reference : Memory}
    {af : Bool} {observation : Sequential.Observation} (binding : Binding d node state worker)
    (frame : Frame d state)
    (selected : (d.graph.node node).instruction = .ordinary instruction)
    (only : Sequential.CallerOnly instruction)
    (policy : d.policy state = authorityCallerPolicy d state)
    (caller : readWord reference d.original.resources.callerAddress = .ok d.callerValue)
    (executed : Sequential.execute (cpu worker reference) instruction af = .ok observation)
    (allowed : ∀ read ∈ observation.reads, callerRead d read) :
    VCGen.Effects.Head d.bytes d.base (d.policy state) (Sequential.FlagChoices.uniform af)
      (localCPU state worker) instruction
      (observation.mapMemory (fun _ => (localCPU state worker).memory)) := by
  have moved := binding.execute_reference frame selected only caller executed allowed
  have actual : Sequential.stepWith (Sequential.FlagChoices.uniform af) (localCPU state worker) =
      .ok (observation.mapMemory (fun _ => (localCPU state worker).memory)) := by
    rw [Sequential.stepWith_eq_executeWith _ (binding.ordinaryDecoded frame selected),
      Sequential.executeWith_uniform _ _ af only.boolChoiceProfile]
    exact moved
  rw [policy]
  refine ⟨binding.localCode frame, frame.current_resources binding,
    binding.ordinaryDecoded frame selected, actual, allowed, only, ?_⟩
  intro _final _returned
  exact frame.current_resources binding

/-- The real current FIFO and a semantic finish yield the existing mixed
issue evidence, including its actual step and full-CPU reification. -/
theorem OrdinaryIssued.of_callerOnly_reference {d : Descriptor} {node : d.graph.Index}
    {state : S} {worker : Worker} {instruction : Sequential.Instruction} {reference : Memory}
    {af : Bool} {observation : Sequential.Observation} {result : S × O}
    (frame : Frame d state) (binding : Binding d node state worker)
    (selected : (d.graph.node node).instruction = .ordinary instruction)
    (only : Sequential.CallerOnly instruction)
    (policy : d.policy state = authorityCallerPolicy d state)
    (caller : readWord reference d.original.resources.callerAddress = .ok d.callerValue)
    (executed : Sequential.execute (cpu worker reference) instruction af = .ok observation)
    (allowed : ∀ read ∈ observation.reads, callerRead d read)
    (finish : FinishEffect state d.tid worker worker.pending
      (observation.mapMemory (fun _ => (localCPU state worker).memory)) result worker.nextStore) :
    OrdinaryIssued d node state af result
      (observation.mapMemory (fun _ => (localCPU state worker).memory)) := by
  exact OrdinaryIssued.of_head frame binding selected
    (binding.callerOnly_ready frame selected only executed allowed)
    (binding.callerOnly_head frame selected only policy caller executed allowed)
    (.unchanged (callerOnly_noStore only _)) finish

#print axioms callerRead
#print axioms authorityCallerPolicy
#print axioms callerOnly_supported
#print axioms callerOnly_noStore
#print axioms Frame.current_resources
#print axioms Binding.current_caller
#print axioms callerOnly_rsp
#print axioms Binding.callerOnly_ready
#print axioms Binding.execute_reference
#print axioms Binding.callerOnly_head
#print axioms OrdinaryIssued.of_callerOnly_reference

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
