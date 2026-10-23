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
Completion at the entire final history of an actual finite production schedule.
`Post` is an assertion of the current state and log. Its stability under every
same-profile, same-family authenticated idle extension is an explicit premise;
an immutable response assertion alone does not assert anything about later RAM.

The invariant is trivial while running and asserts current `Post` once done.
Actual return establishes it, and authenticated passive positions transport it.
A final live returned worker excludes running control using the current binding
in a positive residual; zero fuel is false. The existing checked schedule fold
retains every position, including blocked attempts and drains, and both full
projections. Entry has no future-run premise; the supplied successful schedule
is a premise of the corollary only.

The imported target, resource, synchronization, translation and protected-loan
contracts remain assumptions. This is conditional finite-run completion, with
no fairness, termination, progress, hardware, ABI or corpus claim.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

/-- Current `Post` survives every authenticated idle extension at this exact
profile, subject and family. Arbitrary memory-dependent assertions need a proof. -/
def PostIdleStable (d : Descriptor) (Post : Assertion) : Prop :=
  ∀ {before after : S} {history extended : Log},
    Idle d.profile d.tid (before, history) (after, extended) d.family →
    Post before history → Post after extended

/-- Done asserts `Post` at the current state and entire current history. -/
def CompletionInvariant {d : Descriptor} {initial : S} {Post : Assertion}
    (ghost : Ghost d initial Post) : Prop :=
  match ghost.control with
  | .running _ _ => True
  | .done _ => Post ghost.current ghost.history

/-- Only the real return establishes `Post`; later passive positions use their
actual quietness and origin to obtain the authenticated idle extension. -/
theorem Advance.completionInvariant {d : Descriptor} {initial : S} {Post : Assertion}
    {before after : Ghost d initial Post} {action : Action} {seen : O}
    (advanced : Advance d initial Post before action seen after)
    (stable : PostIdleStable d Post) :
    CompletionInvariant before → CompletionInvariant after := by
  intro invariant
  cases advanced with
  | @passive _ _ _ _ _ control quiet origin =>
    cases control with
    | running _node _fuel => exact True.intro
    | done _response => exact stable (Idle.step quiet origin) invariant
  | blocked _actual => exact True.intro
  | next _issued _outcome _edge _pc => exact True.intro
  | rmw _issued _edge _pc => exact True.intro
  | returned response => exact response.post

/-- Preserve the current-state invariant through all actual lifted positions. -/
theorem liftTrace_completionInvariant {d : Descriptor} {initial : S} {Post : Assertion}
    {before after : Ghost d initial Post} {actions : List Action} {observations : List O}
    (trace : LiftTrace (Advance d initial Post) before actions observations after)
    (stable : PostIdleStable d Post) :
    CompletionInvariant before → CompletionInvariant after := by
  induction trace with
  | nil => exact id
  | cons head _tail ih =>
    intro invariant
    exact ih (head.completionInvariant stable invariant)

/-- A related running residual cannot describe this actual returned worker.
The done invariant therefore gives `Post` at the entire current history. -/
theorem Related.post_of_returned {d : Descriptor} {initial state : S} {Post : Assertion}
    {annotations : Annotations d Post} {ghost : Ghost d initial Post} {worker : Worker}
    (related : Related annotations state ghost) (invariant : CompletionInvariant ghost)
    (live : state.workers[d.tid]? = some worker) (returned : worker.phase = .returned) :
    Post state ghost.history := by
  rcases ghost with ⟨current, history, control⟩
  obtain ⟨sameState, retained⟩ := related
  change state = current at sameState
  subst current
  cases control with
  | running node fuel =>
    cases fuel with
    | zero => exact False.elim retained.generated
    | succ fuel =>
      obtain ⟨boundWorker, currentBinding, _generated⟩ := (rwp.here retained.generated).2
      have sameWorker : boundWorker = worker :=
        Option.some.inj (currentBinding.live.symm.trans live)
      have phases := currentBinding.running.symm.trans
        ((congrArg Worker.phase sameWorker).trans returned)
      cases phases
  | done _response => exact invariant

/-- Independent Entry, explicit idle stability, an actual finite successful
production schedule and its actual final live returned worker yield current
`Post`. The ghost, full lifted trace and both original projections are retained. -/
theorem Annotations.schedule_completion {d : Descriptor} {initial final : S} {Post : Assertion}
    (annotations : Annotations d Post) {node : d.graph.Index}
    (entry : Entry annotations initial node) (stable : PostIdleStable d Post)
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions d.profile d.family = .ok (final, observations))
    {worker : Worker} (live : final.workers[d.tid]? = some worker)
    (returned : worker.phase = .returned) :
    ∃ next, Related annotations final next ∧
      LiftTrace (Advance d initial Post) (initialGhost d initial Post node)
        actions observations next ∧
      OriginTrace d.profile initial next.history final d.family ∧
      Post final next.history ∧
      next.history.map Tick.action = actions ∧
      next.history.map (fun tick => tick.result.2) = observations := by
  obtain ⟨next, related, lifted, authentic, actionsEq, observationsEq⟩ :=
    annotations.schedule entry actual
  have invariant : CompletionInvariant next :=
    liftTrace_completionInvariant lifted stable (show
      CompletionInvariant (initialGhost d initial Post node) from True.intro)
  exact ⟨next, related, lifted, authentic,
    related.post_of_returned invariant live returned, actionsEq, observationsEq⟩

#print axioms PostIdleStable
#print axioms CompletionInvariant
#print axioms Advance.completionInvariant
#print axioms liftTrace_completionInvariant
#print axioms Related.post_of_returned
#print axioms Annotations.schedule_completion

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
