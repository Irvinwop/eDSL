/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.Simulation
import EDSL.OS.TSO64.EffectSimulation.Mixed.CallerOnly
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Current checked own-issue evidence and caller-only queue preservation, for the
descriptor's actual family and profile. Relatedness retains the imported
target, ownership, protected-loan and synchronization contracts. The policy
equality is required only at the current prestate. Worker identity is obtained
from the actual scheduler-slot lookup, without identifying tid with actor.

Pending entries need not be empty. Ordinary retirement and RET preserve those
exact entries, their occurrence counter, resources and world; phase and context
may change. No future-run, cohort closure, final-sum, join, fairness, compiler
refinement or physical-hardware claim is made.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

/-- Invert the checked simulation's actual advance, retaining its exact head.
No native-origin converse or replacement execution is used. -/
theorem Annotations.ordinaryIssued_of_step
    {d : Descriptor} {initial before after : S} {Post : Assertion}
    (annotations : Annotations d Post) {ghost : Ghost d initial Post}
    {af : Bool} {seen : O} (related : Related annotations before ghost)
    (actual : TSO64.step before (.issue d.tid af) d.profile d.family = .ok (after, seen))
    (ordinary : seen = .ordinary d.tid ∨ seen = .returned d.tid) :
    ∃ node observation, OrdinaryIssued d node before af (after, seen) observation := by
  obtain ⟨next, advanced, nextRelated⟩ :=
    annotations.simulation.lift related.frame.wellFormed related actual
  have current : before = ghost.current := related.1
  have successor : after = next.current := nextRelated.1
  rw [current, successor]
  cases advanced with
  | passive quiet _origin => exact False.elim (quiet rfl)
  | blocked _actual => rcases ordinary with label | label <;> cases label
  | next issued _outcome _edge _pc => exact ⟨_, _, issued⟩
  | rmw _issued _edge _pc => rcases ordinary with label | label <;> cases label
  | returned response => exact ⟨response.node, response.observation, response.issued⟩

/-- Invert the production queue effect: caller-only instructions cannot enqueue.
The equality retains a possibly nonempty current FIFO and its exact counter. -/
theorem callerOnly_queue_unchanged
    {before : S} {worker : Worker} {instruction : Sequential.Instruction}
    {update : Queue.Cursor} {profile : Profile}
    (only : Sequential.CallerOnly instruction)
    (queue : QueueEffect before worker instruction update profile) :
    update = ⟨worker.pending, worker.nextStore⟩ := by
  cases queue with
  | unchanged _intent => rfl
  | enqueued intent _admission =>
    rw [callerOnly_noStore only (localCPU before worker)] at intent
    cases intent

/-- The actual selected instruction and head, with their real queue/finish
effects normalized to the prior live worker's unchanged cursor. -/
theorem OrdinaryIssued.callerOnly_effect
    {d : Descriptor} {node : d.graph.Index} {before : S} {af : Bool}
    {result : S × O} {observation : Sequential.Observation} {worker : Worker}
    (issued : OrdinaryIssued d node before af result observation)
    (policy : d.policy before = authorityCallerPolicy d before)
    (live : before.workers[d.tid]? = some worker) :
    ∃ instruction,
      (d.graph.node node).instruction = .ordinary instruction ∧
      Sequential.CallerOnly instruction ∧
      VCGen.Effects.Head d.bytes d.base (d.policy before) (Sequential.FlagChoices.uniform af)
        (localCPU before worker) instruction observation ∧
      QueueEffect before worker instruction ⟨worker.pending, worker.nextStore⟩ d.profile ∧
      FinishEffect before d.tid worker worker.pending observation result worker.nextStore := by
  obtain ⟨prior, instruction, update, binding, selected, _ready, head, queue, finish⟩ :=
    issued.witnesses
  have same : prior = worker := Option.some.inj (binding.live.symm.trans live)
  subst prior
  have only : Sequential.CallerOnly instruction := by
    have effect := head.effect
    rw [policy] at effect
    exact effect
  have unchanged := callerOnly_queue_unchanged only queue
  subst update
  exact ⟨instruction, selected, only, head, queue, finish⟩

/-- Invert the real finish, including RET. Retain current world, resources,
FIFO and next-store counter, without constraining successor phase or context. -/
theorem OrdinaryIssued.callerOnly_preserves
    {d : Descriptor} {node : d.graph.Index} {before : S} {af : Bool}
    {result : S × O} {observation : Sequential.Observation} {worker : Worker}
    (issued : OrdinaryIssued d node before af result observation)
    (policy : d.policy before = authorityCallerPolicy d before)
    (live : before.workers[d.tid]? = some worker) :
    result.1.world = before.world ∧
      ∃ current, result.1.workers[d.tid]? = some current ∧
        current.pending = worker.pending ∧ current.nextStore = worker.nextStore ∧
        current.resources = worker.resources := by
  obtain ⟨_instruction, _selected, _only, _head, _queue, finish⟩ :=
    issued.callerOnly_effect policy live
  refine ⟨issued.world, ?_⟩
  cases finish with
  | @next output _ _outcome =>
    exact ⟨{ worker with context := .ofCPU output },
      List.getElem?_set_self (List.getElem_of_getElem? live).1, rfl, rfl, rfl⟩
  | @returned output _ _outcome =>
    exact ⟨{ worker with context := .ofCPU output, phase := .returned },
      List.getElem?_set_self (List.getElem_of_getElem? live).1, rfl, rfl, rfl⟩

/-- One actual own ordinary/return step from an annotated prestate preserves
the current subject's queue, counter, resources and world under caller policy. -/
theorem Annotations.callerOnly_preserves_of_step
    {d : Descriptor} {initial before after : S} {Post : Assertion}
    (annotations : Annotations d Post) {ghost : Ghost d initial Post}
    {af : Bool} {seen : O} {worker : Worker}
    (related : Related annotations before ghost)
    (actual : TSO64.step before (.issue d.tid af) d.profile d.family = .ok (after, seen))
    (ordinary : seen = .ordinary d.tid ∨ seen = .returned d.tid)
    (policy : d.policy before = authorityCallerPolicy d before)
    (live : before.workers[d.tid]? = some worker) :
    after.world = before.world ∧
      ∃ current, after.workers[d.tid]? = some current ∧
        current.pending = worker.pending ∧ current.nextStore = worker.nextStore ∧
        current.resources = worker.resources := by
  obtain ⟨_node, _observation, issued⟩ :=
    annotations.ordinaryIssued_of_step related actual ordinary
  exact issued.callerOnly_preserves policy live

#print axioms Annotations.ordinaryIssued_of_step
#print axioms callerOnly_queue_unchanged
#print axioms OrdinaryIssued.callerOnly_effect
#print axioms OrdinaryIssued.callerOnly_preserves
#print axioms Annotations.callerOnly_preserves_of_step

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
