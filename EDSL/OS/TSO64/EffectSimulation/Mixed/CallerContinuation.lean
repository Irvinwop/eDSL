/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.CallerOnly

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
A current ordinary-node continuation for the existing mixed VCG. Clients prove
only execution, protected reads and their continuation for every flag choice.
The adapter derives current authority, readiness and the unchanged queue from
caller-only instruction effects. Both ordinary and returned results retain the
full observation and actual installed worker. No future scheduler step or empty
FIFO is an input. Imported target and resource assumptions remain in force;
this is a one-step adapter, not a program or progress theorem.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

/-- The real ordinary finish with the subject's existing pending queue and
store counter. Unsupported result constructors fail closed. -/
def callerContinuation (d : Descriptor) (state : S) (worker : Worker)
    (K : Bool → (S × O) → Retirement → Prop) (af : Bool)
    (observation : Sequential.Observation) : Prop :=
  match observation.result with
  | .next output =>
    K af (install state d.tid state.world {worker with context := .ofCPU output},
      .ordinary d.tid) (.ordinary observation)
  | .returned output =>
    K af (install state d.tid state.world
      {worker with context := .ofCPU output, phase := .returned},
      .returned d.tid) (.ordinary observation)
  | _ => False

/-- Lift CPU execution and its actual finish to the existing generated mixed
obligation. The selected node and current frame supply decoding and authority;
no separate memory bound or saved RAM value is introduced. -/
theorem One.of_callerContinuation {d : Descriptor} {node : d.graph.Index}
    {state : S} {worker : Worker} {instruction : Sequential.Instruction}
    {K : Bool → (S × O) → Retirement → Prop}
    (frame : Frame d state) (binding : Binding d node state worker)
    (selected : (d.graph.node node).instruction = .ordinary instruction)
    (only : Sequential.CallerOnly instruction)
    (policy : d.policy state = authorityCallerPolicy d state)
    (execute : ∀ af, ∃ observation,
      Sequential.execute (localCPU state worker) instruction af = .ok observation ∧
      (∀ read ∈ observation.reads, callerRead d read) ∧
      callerContinuation d state worker K af observation) :
    One d node state K := by
  refine ⟨worker, binding, ?_⟩
  rw [selected]
  obtain ⟨first, firstStep, firstReads, _firstCont⟩ := execute false
  have ready := binding.callerOnly_ready (reference := (localCPU state worker).memory)
    frame selected only firstStep firstReads
  refine ⟨ready, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [policy]
    exact frame.current_resources binding
  · intro af
    obtain ⟨observation, executed, allowed, continuation⟩ := execute af
    rw [Sequential.executeWith_uniform _ _ af only.boolChoiceProfile, executed]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [policy, authorityCallerPolicy] using allowed
    · rw [policy]
      exact only
    · intro _final _returned
      rw [policy]
      exact frame.current_resources binding
    · intro request
      cases outcome : observation.result with
      | next _ => simp only [ne_eq, reduceCtorEq, not_false_eq_true]
      | returned _ => simp only [ne_eq, reduceCtorEq, not_false_eq_true]
      | atomic _ _ => simp only [callerContinuation, outcome] at continuation
      | syscall _ => simp only [callerContinuation, outcome] at continuation
    · refine ⟨?_, ?_⟩
      · cases outcome : observation.result with
        | next output => exact ⟨output, Or.inl outcome⟩
        | returned output => exact ⟨output, Or.inr outcome⟩
        | atomic _ _ => simp only [callerContinuation, outcome] at continuation
        | syscall _ => simp only [callerContinuation, outcome] at continuation
      · intro update result queue finish
        have cursor : update = ⟨worker.pending, worker.nextStore⟩ := by
          cases queue with
          | unchanged _ => rfl
          | enqueued intent _ =>
            have noStore := callerOnly_noStore only (localCPU state worker)
            rw [noStore] at intent
            cases intent
        subst update
        cases finish with
        | next outcome => simpa only [callerContinuation, outcome] using continuation
        | returned outcome => simpa only [callerContinuation, outcome] using continuation

#print axioms callerContinuation
#print axioms One.of_callerContinuation

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
