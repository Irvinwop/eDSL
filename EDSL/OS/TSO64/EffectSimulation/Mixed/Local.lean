/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.Simulation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Local invariant rules generate the existing finite mixed blocks. Retirement
continuations retain their actual fresh ordinary head, queue and finish, or
their coupled atomic effect through the exact selected handle. Nonempty locked
FIFOs retain the existing vacuous obligation and supply no retirement evidence.

Authenticated idle extensions transport the frame, binding and local invariant.
Only noncut successors recurse, using the checked graph's strict depth decrease;
cut arrivals retain the invariant and ordinary returns retain the supplied Post.
The imported native target, resource, synchronization, translation and protected
loan contracts remain assumptions. There is no new evaluator, origin-to-step
converse, fairness, termination or physical refinement claim.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

/-- Enrich every actual retiring continuation without changing current-step
admissions or inventing an effect for a blocked locked instruction. -/
theorem One.enrich {d : Descriptor} {node : d.graph.Index} {state : S}
    {K : Bool → (S × O) → Retirement → Prop}
    (frame : Frame d state) (one : One d node state K) :
    One d node state (fun af result retirement =>
      RetiredEvidence d node state af result retirement ∧ K af result retirement) := by
  obtain ⟨worker, binding, generated⟩ := one
  refine ⟨worker, binding, ?_⟩
  cases selected : (d.graph.node node).instruction with
  | ordinary instruction =>
    simp only [selected] at generated ⊢
    obtain ⟨ready, vc⟩ := generated
    refine ⟨ready, ?_⟩
    have code := binding.localCode frame
    have decoded := binding.ordinaryDecoded frame selected
    have heads := (VCGen.Effects.oneStep_iff_head code decoded).mp vc
    apply (VCGen.Effects.oneStep_iff_head code decoded).mpr
    refine ⟨heads.1, ?_⟩
    intro af
    obtain ⟨observation, head, noSyscall, outcome, continuation⟩ := heads.2 af
    refine ⟨observation, head, noSyscall, outcome, ?_⟩
    intro update result queue finish
    exact ⟨.ordinary (OrdinaryIssued.of_head frame binding selected ready head queue finish),
      continuation update result queue finish⟩
  | locked instruction =>
    simp only [selected] at generated ⊢
    by_cases empty : worker.pending = []
    · rw [ite_eq_left empty] at generated ⊢
      obtain ⟨identifier, handle, cell, chosen, continuation⟩ := generated
      refine ⟨identifier, handle, cell, chosen, ?_⟩
      intro af output machine effect
      exact ⟨.rmw (AtomicIssued.of_effect (af := af)
        frame binding selected empty chosen effect),
        continuation af output machine effect⟩
    · simp only [ite_eq_right empty]

/-- One-step preservation at every graph node, closed under actual idle
extensions. These rules do not assume a future block or successful schedule. -/
structure LocalRules (d : Descriptor) (Post : Assertion) where
  Inv : CutAssertion d
  idle : ∀ {node : d.graph.Index} {before after : S} {history extended : Log},
    Idle d.profile d.tid (before, history) (after, extended) d.family →
    Inv node before history → Inv node after extended
  step : ∀ (node : d.graph.Index) (state : S) (history : Log) (worker : Worker),
    Frame d state → Binding d node state worker → Inv node state history →
    One d node state (Follow d Post Inv Inv node state history)

/-- Finite block generation uses depth only at interior retiring edges.
Idle closure and blocked attempts consume no fuel. -/
private theorem LocalRules.rwp_of_depth {d : Descriptor} {Post : Assertion}
    (rules : LocalRules d Post) :
    ∀ (fuel : Nat) (node : d.graph.Index) (state : S) (history : Log) (worker : Worker),
      (d.graph.node node).depth < fuel →
      Frame d state → Binding d node state worker → rules.Inv node state history →
      rwp d Post rules.Inv fuel node state history := by
  intro fuel
  induction fuel with
  | zero =>
    intro node state history worker bounded
    exact False.elim (Nat.not_lt_zero _ bounded)
  | succ fuel ih =>
    intro node state history worker bounded frame binding invariant
    change IdleBox d.profile d.tid (fun current past => Frame d current ∧
      One d node current
        (Follow d Post rules.Inv (rwp d Post rules.Inv fuel) node current past))
      state history d.family
    intro current past idle
    have currentFrame := frame.idle idle
    obtain ⟨currentWorker, live, saved⟩ := idle.saved binding.live
    have currentBinding : Binding d node current currentWorker :=
      ⟨live, saved.resources.trans binding.resources, saved.phase.trans binding.running,
        (congrArg Context.rip saved.context).trans binding.pc⟩
    have currentInvariant := rules.idle idle invariant
    refine ⟨currentFrame, ?_⟩
    apply One.mono (one := One.enrich currentFrame
      (rules.step node current past currentWorker currentFrame currentBinding currentInvariant))
    intro af result retirement enriched
    obtain ⟨retired, follows⟩ := enriched
    have afterFrame := retired.frame currentFrame
    have advance : ∀ (rip : Word),
        (∀ destination : d.graph.Index,
          rip = d.base + BitVec.ofNat 64 (d.graph.node destination).offset →
          ∃ successor : Worker, Binding d destination result.1 successor) →
        jump d rules.Inv rules.Inv node rip result.1 (issueLog d current past af result) →
        jump d rules.Inv (rwp d Post rules.Inv fuel) node rip result.1
          (issueLog d current past af result) := by
      intro rip bindings following
      obtain ⟨destination, edge, pc, nextInvariant⟩ := following
      refine ⟨destination, edge, pc, ?_⟩
      have next : rules.Inv destination result.1 (issueLog d current past af result) := by
        simpa only [ite_self] using nextInvariant
      cases cut : (d.graph.node destination).cutpoint with
      | true => simpa [cut] using next
      | false =>
        have smaller : (d.graph.node destination).depth < fuel :=
          Nat.lt_of_lt_of_le (d.structural.decreases node destination edge cut)
            (Nat.lt_succ_iff.mp bounded)
        obtain ⟨successor, successorBinding⟩ := bindings destination pc
        simpa [cut] using
          ih destination result.1 (issueLog d current past af result) successor
            smaller afterFrame successorBinding next
    cases retirement with
    | ordinary observation =>
      cases retired with
      | ordinary issued =>
        cases outcome : observation.result with
        | returned output => simpa only [Follow, outcome] using follows
        | atomic event output => simp only [Follow, outcome] at follows
        | syscall request => simp only [Follow, outcome] at follows
        | next output =>
          simp only [Follow, outcome] at follows ⊢
          exact advance output.rip
            (fun _destination pc => afterFrame.next_binding issued.reifies outcome pc) follows
    | rmw output machine =>
      cases retired with
      | rmw issued =>
        change jump d rules.Inv rules.Inv node machine.state.rip result.1
          (issueLog d current past af result) at follows
        change jump d rules.Inv (rwp d Post rules.Inv fuel) node machine.state.rip result.1
          (issueLog d current past af result)
        exact advance machine.state.rip
          (fun _destination pc => afterFrame.atomic_next_binding issued pc) follows

/-- Generate the existing depth-plus-one cut blocks. The invariant projection
is definitionally the supplied local invariant. -/
def LocalRules.annotations {d : Descriptor} {Post : Assertion}
    (rules : LocalRules d Post) : Annotations d Post where
  Inv := rules.Inv
  blocks := by
    intro cut state history worker _cutpoint frame binding invariant
    exact rules.rwp_of_depth ((d.graph.node cut).depth + 1) cut state history worker
      (Nat.lt_succ_self _) frame binding invariant

#print axioms One.enrich
#print axioms LocalRules
#print axioms LocalRules.rwp_of_depth
#print axioms LocalRules.annotations

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
