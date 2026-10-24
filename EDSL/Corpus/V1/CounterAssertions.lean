/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterHistory
import EDSL.OS.TSO64.EffectSimulation.Mixed.Completion

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Shared cut invariants and void-return assertions for the frozen counter workers.
Compiler annotations supply only local register/count arithmetic. All own RMW
history witnesses and the Nat count survive authenticated idle positions;
returned contexts retain their ABI facts without freezing shared RAM or FIFO.
These assertions are not compiler annotations or complete function certificates.
The imported target/resource assumptions and conditional finite-run scope remain.
-/

namespace EDSL.Corpus.V1.CounterCommon
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

/-- Compiler-local arithmetic is independent of current shared memory and is
parameterized by the exact Nat count of the entire unfiltered history. -/
def Inv {c : Compiler} (site : Site c) (call : Call)
    (arithmeticFact : (descriptor site call).graph.Index → Context → Nat → Prop) :
    Mixed.CutAssertion (descriptor site call) := fun node state history =>
  ∃ worker, Mixed.Binding (descriptor site call) node state worker ∧
    LiveData site call state worker.context ∧ OwnIncrements site call history ∧
    arithmeticFact node worker.context (Mixed.Counts.logRMW site.tid history)

/-- Authenticate the current bound worker while preserving compiler-local
arithmetic, exact history count and historical increment witnesses. -/
theorem Inv.idle {c : Compiler} {site : Site c} {call : Call}
    {arithmeticFact : (descriptor site call).graph.Index → Context → Nat → Prop}
    {node : (descriptor site call).graph.Index} {before after : S} {history extended : Log}
    (idle : Mixed.Idle site.profile site.tid (before, history) (after, extended) .arithmetic)
    (prior : Inv site call arithmeticFact node before history) :
    Inv site call arithmeticFact node after extended := by
  obtain ⟨worker, binding, data, increments, arithmetic⟩ := prior
  obtain ⟨current, currentBinding, currentData, sameContext⟩ :=
    binding_liveData_idle binding data idle
  refine ⟨current, currentBinding, currentData, increments.idle idle, ?_⟩
  rw [sameContext, Mixed.Counts.logRMW_idle idle]
  exact arithmetic

/-- Establish a cut assertion using present admission and independent initial
local arithmetic. No generated block or successful future run is an input. -/
theorem Pre.inv {c : Compiler} {site : Site c} {call : Call} {state : S}
    {arithmeticFact : (descriptor site call).graph.Index → Context → Nat → Prop}
    {node : (descriptor site call).graph.Index} (pre : Pre site call state)
    (offset : ((descriptor site call).graph.node node).offset = 0)
    (initial : arithmeticFact node site.original.context 0) : Inv site call arithmeticFact node state [] :=
  ⟨site.original, pre.binding offset, pre.liveData, OwnIncrements.nil site call, initial⟩

/-- Void-call result at this current state and full log. RSP uses modular Word
addition; no canonical/nonwrapping post-stack or RAX-value promise is made. -/
structure Post {c : Compiler} (site : Site c) (call : Call)
    (state : S) (history : Log) : Prop where
  increments : OwnIncrements site call history
  count : Mixed.Counts.logRMW site.tid history = call.iterations.toNat
  returned : ∃ worker, state.workers[site.tid]? = some worker ∧
    worker.resources = site.original.resources ∧ worker.phase = .returned ∧
    worker.context.rip = call.returnAddress ∧
    worker.context.registers .rsp = site.original.context.registers .rsp + 8 ∧
    Saved site worker.context

/-- A complete returned worker's assertion remains true after arbitrary
native peer/drain idle suffixes, including changing RAM and pending entries. -/
theorem stablePost {c : Compiler} (site : Site c) (call : Call) :
    Mixed.PostIdleStable (descriptor site call) (Post site call) := by
  intro before after history extended idle prior
  refine ⟨prior.increments.idle idle, ?_, ?_⟩
  · exact (Mixed.Counts.logRMW_idle idle).trans prior.count
  · obtain ⟨worker, live, resources, phase, pc, stack, saved⟩ := prior.returned
    obtain ⟨current, currentLive, retained⟩ := idle.saved live
    refine ⟨current, currentLive, retained.resources.trans resources,
      retained.phase.trans phase, ?_, ?_, ?_⟩
    · exact (congrArg Context.rip retained.context).trans pc
    · simpa only [retained.context] using stack
    · simpa only [retained.context] using saved

/-- Given separately proved compiler annotations and current Entry, a real
finite returned schedule has exactly the independently requested number of
own RMW observations. This supplies no annotations, fairness or termination. -/
theorem completed_count {c : Compiler} {site : Site c} {call : Call}
    (annotations : Mixed.Annotations (descriptor site call) (Post site call))
    {initial final : S} {node : (descriptor site call).graph.Index}
    (entry : Mixed.Entry annotations initial node)
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions site.profile .arithmetic = .ok (final, observations))
    {worker : Worker} (live : final.workers[site.tid]? = some worker)
    (returned : worker.phase = .returned) :
    Mixed.Counts.countRMW site.tid observations = call.iterations.toNat := by
  obtain ⟨next, _related, _trace, _authentic, post, _actions, sameObservations⟩ :=
    annotations.schedule_completion entry (stablePost site call) actual live returned
  rw [← sameObservations]
  exact post.count

#print axioms Inv
#print axioms Inv.idle
#print axioms Pre.inv
#print axioms Post
#print axioms stablePost
#print axioms completed_count

end EDSL.Corpus.V1.CounterCommon

#audit_edsl
