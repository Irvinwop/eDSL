/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterAssertions
import EDSL.OS.TSO64.Increment64
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Shared current LOCK-increment continuation for the frozen GCC ADD
and Clang INC nodes.

The existing mixed head owns dispatch, blocking and native enabledness. Only
its actual current selected machine effect is summarized here; the complete
observation, typed tag and joint effect remain available. The old value comes
from current RAM, and ADD/INC flags are not identified. The incoming history
predicate does not assert a connected origin trace.

Inherits long-mode/CET-off, coherent scalar WB RAM, stable translation/no-alias
and protected resource/atomic lifetime assumptions from the imported model.
No progress, physical LOCK/compiler refinement, complete worker annotation or
new corpus credit is asserted.
-/

namespace EDSL.Corpus.V1.CounterCommon
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

/-- Consequences of one actual current increment, at its complete native issue
position. The existential preserves the exact selected triple and the entire
joint effect; `Increment64.Effect` includes all GPRs, current old/new RAM and
the actual encoding's byte-length RIP. The installed worker retains resources
and running phase, while its context is the actual machine output. -/
structure IncrementStep {c : Compiler} (site : Site c) (call : Call)
    (node : (descriptor site call).graph.Index) (before : S) (worker : Worker)
    (history : Log) (af : Bool) (instruction : AddRMW64.Instruction)
    (output : World × Atomics64.FetchAddEvent) (machine : AddRMW64.Observation) : Prop where
  selected : ((descriptor site call).graph.node node).instruction = .locked instruction
  tagged : (.locked instruction : Decoded .arithmetic) = tag c
  effect : ∃ identifier handle cell,
    atomicFor before.world worker.resources call.address = some (identifier, handle, cell) ∧
    handle.cell = call.target ∧
    Increment64.Effect before.world worker.resources.actor identifier
      (sharedCPU before worker) instruction output machine
  issued : Mixed.AtomicIssued (descriptor site call) node before af
    (install before site.tid output.1 { worker with context := .ofCPU machine.state },
      .rmw site.tid output.2) output machine
  eventOK : EventOK site call output.2
  frame : Mixed.Frame (descriptor site call)
    (install before site.tid output.1 { worker with context := .ofCPU machine.state })
  live : (install before site.tid output.1
    { worker with context := .ofCPU machine.state }).workers[site.tid]? =
      some { worker with context := .ofCPU machine.state }
  resources : ({ worker with context := .ofCPU machine.state } : Worker).resources =
    site.original.resources
  running : ({ worker with context := .ofCPU machine.state } : Worker).phase = .running
  data : LiveData site call
    (install before site.tid output.1 { worker with context := .ofCPU machine.state })
    (.ofCPU machine.state)
  increments : OwnIncrements site call
    (Mixed.issueLog (descriptor site call) before history af
      (install before site.tid output.1 { worker with context := .ofCPU machine.state },
        .rmw site.tid output.2))
  count : Mixed.Counts.logRMW site.tid
    (Mixed.issueLog (descriptor site call) before history af
      (install before site.tid output.1 { worker with context := .ofCPU machine.state },
        .rmw site.tid output.2)) = Mixed.Counts.logRMW site.tid history + 1

/-- Thin specialization of `Mixed.One` at the actual selected locked node.
The tag, unit-increment classification and RDI operand are explicit local
compiler facts. Entry admits a well-formed nonempty FIFO: that branch remains
`True` in the existing head, without invoking the retirement continuation.
No future execution, enabledness or empty-FIFO premise is required. -/
theorem oneLocked {c : Compiler} {site : Site c} {call : Call}
    {node : (descriptor site call).graph.Index} {before : S} {worker : Worker}
    {history : Log} {instruction : AddRMW64.Instruction}
    {K : Bool → (S × O) → Mixed.Retirement → Prop}
    (frame : Mixed.Frame (descriptor site call) before)
    (binding : Mixed.Binding (descriptor site call) node before worker)
    (data : LiveData site call before worker.context)
    (increments : OwnIncrements site call history)
    (selected : ((descriptor site call).graph.node node).instruction = .locked instruction)
    (tagged : (.locked instruction : Decoded .arithmetic) = tag c)
    (increment : Increment64.IsIncrement instruction)
    (operand : instruction.base = .rdi)
    (continuation : ∀ (af : Bool) (output : World × Atomics64.FetchAddEvent)
        (machine : AddRMW64.Observation),
      IncrementStep site call node before worker history af instruction output machine →
      K af (install before site.tid output.1 { worker with context := .ofCPU machine.state },
        .rmw site.tid output.2) (.rmw output machine)) :
    Mixed.One (descriptor site call) node before K := by
  refine ⟨worker, binding, ?_⟩
  simp only [selected]
  by_cases empty : worker.pending = []
  · rw [ite_eq_left empty]
    obtain ⟨identifier, handle, cell, chosen, target⟩ := data.selected
    have currentChosen : atomicFor before.world worker.resources call.address =
        some (identifier, handle, cell) := by
      simpa only [binding.resources, descriptor] using chosen
    have pointer : (sharedCPU before worker).registers instruction.base = call.address := by
      change worker.context.registers instruction.base = call.address
      rw [operand]
      exact data.pointer
    have selectedOperand : atomicFor before.world worker.resources
        ((sharedCPU before worker).registers
          ((descriptor site call).family.embed instruction).base) =
          some (identifier, handle, cell) := by
      change atomicFor before.world worker.resources
        ((sharedCPU before worker).registers instruction.base) = _
      rw [pointer]
      exact currentChosen
    refine ⟨identifier, handle, cell, selectedOperand, ?_⟩
    intro af output machine effect
    apply continuation af output machine
    have summary : Increment64.Effect before.world worker.resources.actor identifier
        (sharedCPU before worker) instruction output machine :=
      Increment64.Effect.of_effect effect increment
    have authority := atomicFor_sound currentChosen
    obtain ⟨_cellLive, _valid, actor, _handleId, eventCell, address,
        _cellAddress, _old, _readback⟩ :=
      summary.selected handle cell call.address authority.2.1 pointer
    have eventOK : EventOK site call output.2 := by
      refine ⟨?_, eventCell.trans target, address, summary.delta, summary.after⟩
      simpa only [binding.resources, descriptor] using actor
    have issued := Mixed.AtomicIssued.of_effect (af := af)
      frame binding selected empty selectedOperand effect
    have registers : machine.state.registers = worker.context.registers := summary.registers
    have flags : machine.state.flags &&& ~~~arithmeticFlagMask =
        worker.context.flags &&& ~~~arithmeticFlagMask :=
      (RMWFamily.MachineEffect.arithmetic (family := .arithmetic) effect).nonarithmetic_flags
    have saved : Saved site (.ofCPU machine.state) := by
      refine ⟨?_, ?_⟩
      · intro register member
        change machine.state.registers register = _
        rw [registers]
        exact data.saved.1 register member
      · change machine.state.flags &&& ~~~arithmeticFlagMask = _
        exact flags.trans data.saved.2
    refine {
      selected := selected
      tagged := tagged
      effect := ⟨identifier, handle, cell, currentChosen, target, summary⟩
      issued := issued
      eventOK := eventOK
      frame := frame.step issued.actual
      live := ?_
      resources := binding.resources
      running := binding.running
      data := ?_
      increments := increments.snoc_increment (selected.trans tagged) eventOK issued
      count := ?_ }
    · change (before.workers.set site.tid
        { worker with context := .ofCPU machine.state })[site.tid]? = _
      exact List.getElem?_set_self (List.getElem_of_getElem? binding.live).1
    · refine ⟨?_, ?_, saved, data.selected.origin issued.origin⟩
      · change machine.state.registers .rdi = call.address
        rw [registers]
        exact data.pointer
      · change machine.state.registers .rsp = site.original.resources.callerAddress
        rw [registers]
        exact data.stack
    · exact Mixed.Counts.logRMW_snoc_rmw site.tid history before
        (install before site.tid output.1 { worker with context := .ofCPU machine.state })
        af output.2
  · rw [ite_eq_right empty]
    trivial

#print axioms IncrementStep
#print axioms oneLocked

end EDSL.Corpus.V1.CounterCommon

#audit_edsl
