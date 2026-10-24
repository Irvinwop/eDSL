/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterCohortClosure
import EDSL.Corpus.V1.CounterCohort
import EDSL.OS.TSO64.LifecycleSchedule

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Actual administrative cleanup of completed compiler-worker cohorts.
The resource names and pairwise separation come from independent original
input manifests; current validity, returned phase and empty queues concern the
real terminal state. Every successful schedule retains the ordered resource
records, so the original separation transports without a future-state oracle.
Cohort closure derives current empty queues from present initial admission and
the actual schedule. Production retireAll executes against successive current
worlds, preserving current RAM and resources and revoking logical capabilities.
No return-time RAM snapshot is restored. No constructive program completion,
native join, physical hardware/compiler refinement or corpus credit is asserted.
-/

namespace EDSL.Corpus.V1.CounterCommon
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

/-- The actual completed annotation authenticates the original resource record,
including code/caller loans, grants and atomic handles, under arithmetic TSO64. -/
theorem Pre.completed_resources {c : Compiler} {site : Site c} {call : Call}
    {initial final : S} (pre : Pre site call initial)
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions site.profile .arithmetic = .ok (final, observations))
    {worker : Worker} (live : final.workers[site.tid]? = some worker)
    (returned : worker.phase = .returned) : worker.resources = site.original.resources := by
  obtain ⟨node, entry⟩ := checkedEntry pre
  obtain ⟨_next, _related, _trace, _authentic, post, _actions, _observations⟩ :=
    (checkedAnnotations pre).schedule_completion entry (stablePost site call) actual live returned
  obtain ⟨current, currentLive, resources, _phase, _pc, _stack, _saved⟩ := post.returned
  have same : worker = current := Option.some.inj (live.symm.trans currentLive)
  exact (congrArg Worker.resources same).trans resources

/-- Independent original cleanup shape plus actual current returned/empty facts
constructs the production cleanup Ready predicate. Current authority is derived
from successful execution, rather than copied from an earlier world. -/
theorem Pre.retirement_ready {c : Compiler} {site : Site c} {call : Call}
    {initial final : S} (pre : Pre site call initial)
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions site.profile .arithmetic = .ok (final, observations))
    {worker : Worker} (live : final.workers[site.tid]? = some worker)
    (returned : worker.phase = .returned) (empty : worker.pending = [])
    {identifier : Atomics64.HandleId64}
    (singleton : site.original.resources.atomics = [identifier])
    (distinct : site.original.resources.code.identifier ≠ site.original.resources.caller.identifier) :
    Lifecycle.Ready final.world worker identifier := by
  have retained := pre.completed_resources actual live returned
  have valid := TSO64.schedule_wellFormed pre.admitted.wellFormed actual
  refine ⟨returned, empty, ?_, (valid.2 worker (List.mem_of_getElem? live)).1, ?_⟩
  · rw [retained]
    exact singleton
  · rw [retained]
    exact distinct

/-- A finite independent cleanup shape, with no future-success requirement. -/
def CleanupShape {c : Compiler} (site : Site c) : Prop :=
  ∃ identifier, site.original.resources.atomics = [identifier] ∧
    site.original.resources.code.identifier ≠ site.original.resources.caller.identifier

/-- Every actual final worker receives current cleanup admission. Initial
Entries and empty queues come from the checked counter cohort adapter; the
caller supplies only original cleanup shapes and actual terminal returnedness.
This constructs Ready predicates, not cleanup operations or native join rights. -/
theorem counterCohort_retirement_ready {ι : Type} {initial final : S}
    (subjects : ι → CohortSubject initial)
    (covered : (counterCohort subjects).Covers initial) (empty : Quiescent initial)
    (shapes : ∀ subject, CleanupShape (subjects subject).site)
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions .ownedOnly .arithmetic = .ok (final, observations))
    (returned : ∀ worker ∈ final.workers, worker.phase = .returned) :
    ∀ worker ∈ final.workers, ∃ identifier, Lifecycle.Ready final.world worker identifier := by
  obtain ⟨finalEmpty, finalCovered, _current, _retiring⟩ :=
    counterCohort_closed subjects covered empty actual
  intro worker member
  obtain ⟨tid, live⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨subject, subjectTid⟩ := finalCovered tid worker live
  change (subjects subject).site.tid = tid at subjectTid
  have subjectLive : final.workers[(subjects subject).site.tid]? = some worker := by
    rw [subjectTid]
    exact live
  have subjectRun : TSO64.schedule initial actions (subjects subject).site.profile .arithmetic =
      .ok (final, observations) := by
    rw [(subjects subject).ownedOnly]
    exact actual
  obtain ⟨identifier, singleton, distinct⟩ := shapes subject
  exact ⟨identifier, (subjects subject).pre.retirement_ready subjectRun subjectLive
    (returned worker member) (finalEmpty worker member) singleton distinct⟩

/-- A checked cohort's actual all-returned endpoint admits successful production
cleanup from only present original shapes, separation and empty queues. Current
Ready and separation are derived from that same execution. Each removal checks
its actual successor world; every current byte, permission, ownership resource
and registered cell is retained. This is logical capability revocation, not a
native join or a construction of the terminating instruction schedule. -/
theorem counterCohort_retireAll {ι : Type} {initial final : S}
    (subjects : ι → CohortSubject initial)
    (valid : WellFormed initial .ownedOnly)
    (covered : (counterCohort subjects).Covers initial) (empty : Quiescent initial)
    (shapes : ∀ subject, CleanupShape (subjects subject).site)
    (separate : initial.workers.reverse.Pairwise
      (fun retiring peer => Lifecycle.Separate retiring.resources peer.resources))
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions .ownedOnly .arithmetic = .ok (final, observations))
    (returned : ∀ worker ∈ final.workers, worker.phase = .returned) :
    ∃ result, Lifecycle.retireAll final = .ok result ∧ WellFormed result.1 .ownedOnly ∧
      result.1.workers = [] ∧ result.2 = final.workers.reverse.map Worker.context ∧
      result.1.world.legacy.shared.resources = final.world.legacy.shared.resources ∧
      result.1.world.cells = final.world.cells ∧ published result.1.world = published final.world ∧
      (∃ labels, Atomics64.History final.world labels result.1.world) ∧
      ∀ worker ∈ final.workers, Lifecycle.WorkerRevoked result.1.world worker := by
  exact Lifecycle.retireAll_ready (TSO64.schedule_wellFormed valid actual)
    (counterCohort_retirement_ready subjects covered empty shapes actual returned)
    (schedule_retirement_separate actual separate)

/-- Preserve the independent two-counter contract through actual production
cleanup. Both original compiler admissions, profiles, exact scheduler slots,
worker universe, actual returned workers, registered target, target equations
and initial RAM read are retained. The added cleanup inputs concern only
original shape/separation and initial empty queues. The two admissions construct
the exhaustive checked cohort; no future empty/separation/cleanup-success fact
is supplied. The modular sum is read from the actual cleanup world's CURRENT
RAM. No native completion, actor authentication or corpus credit is asserted. -/
theorem two_completed_retired_total {leftCompiler rightCompiler : Compiler}
    {left : Site leftCompiler} {right : Site rightCompiler} {leftCall rightCall : Call}
    {initial final : S}
    (leftPre : Pre left leftCall initial) (rightPre : Pre right rightCall initial)
    (leftProfile : left.profile = .ownedOnly) (rightProfile : right.profile = .ownedOnly)
    (leftSlot : left.tid = 0) (rightSlot : right.tid = 1)
    (workerUniverse : initial.workers.length = 2)
    (empty : Quiescent initial) (leftShape : CleanupShape left) (rightShape : CleanupShape right)
    (separate : initial.workers.reverse.Pairwise
      (fun retiring peer => Lifecycle.Separate retiring.resources peer.resources))
    {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions .ownedOnly .arithmetic = .ok (final, observations))
    {leftWorker rightWorker : Worker}
    (leftLive : final.workers[left.tid]? = some leftWorker)
    (rightLive : final.workers[right.tid]? = some rightWorker)
    (leftReturned : leftWorker.phase = .returned) (rightReturned : rightWorker.phase = .returned)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (registered : initial.world.cells target = some cell)
    (leftTarget : leftCall.target = target) (rightTarget : rightCall.target = target)
    (prior : Word)
    (readBefore : loadQWord (AddressSpace.toMemory initial.world.legacy.shared.resources.space)
      cell.address = .ok prior) :
    ∃ result value,
      Lifecycle.retireAll final = .ok result ∧ WellFormed result.1 .ownedOnly ∧
      result.1.workers = [] ∧ result.2 = final.workers.reverse.map Worker.context ∧
      result.1.world.legacy.shared.resources = final.world.legacy.shared.resources ∧
      result.1.world.cells = final.world.cells ∧ published result.1.world = published final.world ∧
      (∃ labels, Atomics64.History final.world labels result.1.world) ∧
      (∀ worker ∈ final.workers, Lifecycle.WorkerRevoked result.1.world worker) ∧
      loadQWord (AddressSpace.toMemory result.1.world.legacy.shared.resources.space)
        cell.address = .ok value ∧
      value.toNat =
        (prior.toNat + leftCall.iterations.toNat + rightCall.iterations.toNat) % 2^64 := by
  let subjects : Bool → CohortSubject initial := fun side =>
    match side with
    | false => ⟨leftCompiler, left, leftCall, leftPre, leftProfile⟩
    | true => ⟨rightCompiler, right, rightCall, rightPre, rightProfile⟩
  have covered : (counterCohort subjects).Covers initial := by
    intro tid worker live
    have bound := (List.getElem_of_getElem? live).1
    rw [workerUniverse] at bound
    have slot : tid = 0 ∨ tid = 1 := by omega
    rcases slot with atLeft | atRight
    · refine ⟨false, ?_⟩
      change left.tid = tid
      exact leftSlot.trans atLeft.symm
    · refine ⟨true, ?_⟩
      change right.tid = tid
      exact rightSlot.trans atRight.symm
  have shapes : ∀ subject, CleanupShape (subjects subject).site := by
    intro subject
    cases subject with
    | false => exact leftShape
    | true => exact rightShape
  have valid : WellFormed initial .ownedOnly := by
    simpa only [descriptor, leftProfile] using leftPre.admitted.wellFormed
  have finalLength : final.workers.length = 2 :=
    (ScheduleTrace.workers_length actual).trans workerUniverse
  have returned : ∀ worker ∈ final.workers, worker.phase = .returned := by
    intro worker member
    obtain ⟨tid, live⟩ := List.mem_iff_getElem?.mp member
    have bound := (List.getElem_of_getElem? live).1
    rw [finalLength] at bound
    have slot : tid = 0 ∨ tid = 1 := by omega
    rcases slot with atLeft | atRight
    · have atSite : final.workers[left.tid]? = some worker := by
        rw [leftSlot, ← atLeft]
        exact live
      have same : worker = leftWorker := Option.some.inj (atSite.symm.trans leftLive)
      exact (congrArg Worker.phase same).trans leftReturned
    · have atSite : final.workers[right.tid]? = some worker := by
        rw [rightSlot, ← atRight]
        exact live
      have same : worker = rightWorker := Option.some.inj (atSite.symm.trans rightLive)
      exact (congrArg Worker.phase same).trans rightReturned
  obtain ⟨result, success, afterValid, workers, contexts, resources, cells, ram,
      history, revoked⟩ :=
    counterCohort_retireAll subjects valid covered empty shapes separate actual returned
  obtain ⟨value, readAfter, total⟩ :=
    two_completed_total leftPre rightPre leftProfile rightProfile leftSlot rightSlot
      workerUniverse actual leftLive rightLive leftReturned rightReturned target cell
      registered leftTarget rightTarget prior readBefore
  refine ⟨result, value, success, afterValid, workers, contexts, resources, cells, ram,
    history, revoked, ?_, total⟩
  change loadQWord (published result.1.world) cell.address = .ok value
  rw [ram]
  exact readAfter

#print axioms Pre.completed_resources
#print axioms Pre.retirement_ready
#print axioms CleanupShape
#print axioms counterCohort_retirement_ready
#print axioms counterCohort_retireAll
#print axioms two_completed_retired_total

end EDSL.Corpus.V1.CounterCommon

#audit_edsl
