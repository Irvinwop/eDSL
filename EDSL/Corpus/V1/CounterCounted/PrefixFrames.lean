/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterCounted.PrefixMemory
import EDSL.OS.TSO64.EffectSimulation.Mixed.IssuePreservation

set_option warningAsError true
set_option autoImplicit false

/-!
Original-slot resource, selection, protected-caller and void ABI frames for
every successful prefix of independently admitted counted calls. The exact
collectively lifted trace preserves each slot's next-store counter through
ordinary issues, locked issues, returns and passive positions. Running local
invariants retain the saved flag mask; done control uses Post transported to
the actual current endpoint by its independently proved idle stability.

Returned frames use the original scalar entry's clear DF and canonical
post-pop stack, the actual returned worker and its actual collected RAX. No
value is prescribed for that caller-saved register. Counts and other memory
effects come from the existing same-run prefix theorems. Admission adds no
future no-enqueue, manager-construction, fairness or completion premise.

The final prefixes theorem has the complete independent Claim.prefixes type.
It supplies neither the other Claim fields nor corpus or native credit. The
imported represented-memory, protected-resource, CET-off and translation
assumptions remain; no physical CPU/OS or compiler refinement is asserted.
-/

namespace EDSL.Corpus.V1.CounterCounted
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

/-- Actual locked installation changes the context without consuming an
ordinary-store occurrence number. The source is the same live slot. -/
private theorem atomic_nextStore
    {d : Mixed.Descriptor} {node : d.graph.Index} {before : TSO64.State}
    {af : Bool} {result : TSO64.State × Observation}
    {output : World × Atomics64.FetchAddEvent} {machine : AddRMW64.Observation}
    (issued : Mixed.AtomicIssued d node before af result output machine)
    {worker : Worker} (live : before.workers[d.tid]? = some worker) :
    ∃ current, result.1.workers[d.tid]? = some current ∧
      current.nextStore = worker.nextStore := by
  obtain ⟨prior, _instruction, _identifier, _handle, _cell, binding, _selected,
    _empty, _decoded, _chosen, _changed, _executed, _effect, installed⟩ := issued.witnesses
  have same : prior = worker := Option.some.inj (binding.live.symm.trans live)
  subst prior
  rw [installed]
  exact ⟨{ worker with context := .ofCPU machine.state },
    List.getElem?_set_self (List.getElem_of_getElem? live).1, rfl⟩

/-- Preserve the counter through each exact lifted position. Passive origins
also include own drains; their saved frame retains nextStore independently
of any FIFO change. Ordinary/RET cases use the actual checked queue effect. -/
private theorem advance_nextStore
    {d : Mixed.Descriptor} {initial : TSO64.State} {Post : Mixed.Assertion}
    {before after : Mixed.Ghost d initial Post} {action : Action} {seen : Observation}
    (policy : ∀ state, d.policy state = Mixed.authorityCallerPolicy d state)
    (advanced : Mixed.Advance d initial Post before action seen after)
    {worker : Worker} (live : before.current.workers[d.tid]? = some worker) :
    ∃ current, after.current.workers[d.tid]? = some current ∧
      current.nextStore = worker.nextStore := by
  cases advanced with
  | passive quiet origin =>
    obtain ⟨current, currentLive, retained⟩ := origin_saved origin quiet live
    exact ⟨current, currentLive, retained.nextStore⟩
  | blocked _actual => exact ⟨worker, live, rfl⟩
  | next issued _outcome _edge _pc =>
    obtain ⟨_world, current, currentLive, _pending, counter, _resources⟩ :=
      issued.callerOnly_preserves (policy _) live
    exact ⟨current, currentLive, counter⟩
  | rmw issued _edge _pc => exact atomic_nextStore issued live
  | returned response =>
    obtain ⟨_world, current, currentLive, _pending, counter, _resources⟩ :=
      response.issued.callerOnly_preserves (policy _) live
    exact ⟨current, currentLive, counter⟩

/-- Fold the actual lifted prefix, allowing arbitrary initial counters and
retaining the original slot rather than choosing another execution. -/
private theorem trace_nextStore
    {d : Mixed.Descriptor} {initial : TSO64.State} {Post : Mixed.Assertion}
    {before after : Mixed.Ghost d initial Post}
    {actions : List Action} {observations : List Observation}
    (policy : ∀ state, d.policy state = Mixed.authorityCallerPolicy d state)
    (trace : LiftTrace (Mixed.Advance d initial Post) before actions observations after) :
    ∀ {worker : Worker}, before.current.workers[d.tid]? = some worker →
      ∃ current, after.current.workers[d.tid]? = some current ∧
        current.nextStore = worker.nextStore := by
  induction trace with
  | nil => intro worker live; exact ⟨worker, live, rfl⟩
  | cons head _tail ih =>
    intro worker live
    obtain ⟨middle, middleLive, first⟩ := advance_nextStore policy head live
    obtain ⟨current, currentLive, second⟩ := ih middleLive
    exact ⟨current, currentLive, second.trans first⟩

/-- Both compiler-selected current invariants expose Binding and LiveData.
No property of a generated residual is assumed to be a local invariant. -/
private theorem checked_inv_saved
    {compiler : CounterCommon.Compiler} {site : CounterCommon.Site compiler}
    {call : CounterCommon.Call} {initial state : TSO64.State} {history : Log}
    (pre : CounterCommon.Pre site call initial)
    {node : (CounterCommon.descriptor site call).graph.Index}
    (invariant : (CounterCommon.checkedRules pre).Inv node state history) :
    ∃ worker, state.workers[site.tid]? = some worker ∧
      CounterCommon.Saved site worker.context := by
  cases compiler with
  | defaultGCC =>
    obtain ⟨worker, binding, data, _increments, _arithmetic⟩ := invariant
    exact ⟨worker, binding.live, data.saved⟩
  | defaultClang =>
    obtain ⟨worker, binding, data, _increments, _arithmetic⟩ := invariant
    exact ⟨worker, binding.live, data.saved⟩

/-- Once done, saved facts come from current Post, after stable transport of
the real response through the same trace. A historical response alone would
not justify an assertion about this endpoint. -/
private theorem checked_saved
    {compiler : CounterCommon.Compiler} {site : CounterCommon.Site compiler}
    {call : CounterCommon.Call} {initial state : TSO64.State}
    (pre : CounterCommon.Pre site call initial)
    {ghost : Mixed.Ghost (CounterCommon.descriptor site call) initial
      (CounterCommon.Post site call)}
    (present : (CounterCommon.checkedRules pre).LocalRelated state ghost)
    (completion : Mixed.CompletionInvariant ghost)
    {worker : Worker} (live : state.workers[site.tid]? = some worker) :
    CounterCommon.Saved site worker.context := by
  have liveAtGhost : ghost.current.workers[site.tid]? = some worker := by
    rw [← present.1.1]
    exact live
  cases control : ghost.control with
  | running node _fuel =>
    have invariant : (CounterCommon.checkedRules pre).Inv node ghost.current ghost.history := by
      simpa only [Mixed.LocalRules.LocalAt, control] using present.2
    obtain ⟨saved, savedLive, savedFrame⟩ := checked_inv_saved pre invariant
    have same : worker = saved := Option.some.inj (liveAtGhost.symm.trans savedLive)
    simpa only [same] using savedFrame
  | done _response =>
    have post : CounterCommon.Post site call ghost.current ghost.history := by
      simpa only [Mixed.CompletionInvariant, control] using completion
    obtain ⟨saved, savedLive, _resources, _phase, _pc, _stack, savedFrame⟩ := post.returned
    have same : worker = saved := Option.some.inj (liveAtGhost.symm.trans savedLive)
    simpa only [same] using savedFrame

/-- DF is outside the independently fixed arithmetic mask. -/
private theorem direction_of_mask {before after : Word}
    (preserved : after &&& ~~~arithmeticFlagMask = before &&& ~~~arithmeticFlagMask)
    (clear : before.getLsbD 10 = false) : after.getLsbD 10 = false := by
  have mask : (~~~arithmeticFlagMask).getLsbD 10 = true := by decide +kernel
  have bit := congrArg (fun flags : Word => flags.getLsbD 10) preserved
  have same : after.getLsbD 10 = before.getLsbD 10 := by
    simpa only [BitVec.getLsbD_and, mask, Bool.and_true] using bit
  exact same.trans clear

variable {compiler : CounterCommon.Compiler} {target : Atomics64.CellId64}
  {cell : Atomics64.Cell} {before cut : TSO64.State}
  {requests : Spec.Requests before} {actions : List Action}
  {observations : List Observation}

/-- The exact independent SafePrefix.frames obligation at the actual cut.
Every current witness is aligned by its original scheduler-slot lookup;
resource actors are never identified with those slot numbers. -/
theorem prefix_frames
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : schedule before actions .ownedOnly .arithmetic = .ok (cut, observations)) :
    ∀ (slot : Fin before.workers.length) (initial : Worker),
      before.workers[slot.val]? = some initial →
      ∃ (current : Worker) (identifier : Atomics64.HandleId64) (handle : Atomics64.Handle),
        cut.workers[slot.val]? = some current ∧
        current.resources = initial.resources ∧ ResourcesValid cut.world current.resources ∧
        current.nextStore = initial.nextStore ∧
        atomicFor before.world initial.resources cell.address = some (identifier, handle, cell) ∧
        atomicFor cut.world current.resources cell.address = some (identifier, handle, cell) ∧
        handle.cell = target ∧
        CodeAt (published cut.world) (image compiler).base (image compiler).bytes ∧
        current.context.flags &&& ~~~arithmeticFlagMask =
          initial.context.flags &&& ~~~arithmeticFlagMask ∧
        (∀ continuation,
          Borrowing.loadWord64 before.world.legacy.shared initial.resources.actor
            initial.resources.caller.identifier initial.resources.callerAddress = .ok continuation →
          Borrowing.loadWord64 cut.world.legacy.shared current.resources.actor
            current.resources.caller.identifier current.resources.callerAddress = .ok continuation) ∧
        (current.phase = .returned →
          Grading.ConcurrentTask.Counted64.ReturnFrame before cut slot.val initial current ∧
          Mixed.Counts.countRMW slot.val observations = (requests slot).toNat) := by
  obtain ⟨atCut, cutCurrent, lifted⟩ :=
    (cohort pre).prefix_from_current pre.valid (current pre) actual
  obtain ⟨cutEmpty, _cutCovered, _otherCurrent, _retiring⟩ :=
    (cohort pre).toCohort.schedule_from_current ((cohort pre).covers rfl)
      ((cohort pre).current_toCohort (current pre)) pre.empty actual
  intro slot initial initialLive
  let data := slotData pre slot
  have sameInitial : initial = data.worker := Option.some.inj (initialLive.symm.trans data.live)
  subst initial
  have related : Mixed.Related (CounterCommon.checkedRules (data.pre pre.valid)).annotations
      cut (atCut slot) := (cutCurrent slot).1
  have trace : LiftTrace
      (Mixed.Advance (CounterCommon.descriptor data.site data.call) before
        (CounterCommon.Post data.site data.call))
      (ghosts pre slot) actions observations (atCut slot) :=
    ((cohort pre).rules slot).localTrace_forget ((cohort pre).localTrace lifted slot)
  obtain ⟨worker, currentLive, counter⟩ :=
    trace_nextStore ((cohort pre).callerPolicy slot) trace data.live
  have live : cut.workers[slot.val]? = some worker := by
    rw [related.1]
    exact currentLive
  obtain ⟨retained, retainedLive, retainedResources⟩ := related.frame.worker
  have sameWorker : worker = retained := Option.some.inj (live.symm.trans retainedLive)
  have resources : worker.resources = data.worker.resources :=
    (congrArg Worker.resources sameWorker).trans retainedResources
  have valid : ResourcesValid cut.world worker.resources :=
    (related.frame.wellFormed.2 worker (List.mem_of_getElem? live)).1
  have completion : Mixed.CompletionInvariant (atCut slot) :=
    Mixed.liftTrace_completionInvariant trace (CounterCommon.stablePost data.site data.call)
      (show Mixed.CompletionInvariant (ghosts pre slot) from True.intro)
  have saved : CounterCommon.Saved data.site worker.context :=
    checked_saved (data.pre pre.valid) (cutCurrent slot) completion live
  obtain ⟨identifier, handle, originalSelection, linked⟩ := data.entry.selected
  have currentSelection : atomicFor cut.world worker.resources cell.address =
      some (identifier, handle, cell) := by
    rw [resources, (schedule_stable actual).atomicFor]
    exact originalSelection
  have caller : ∀ continuation,
      Borrowing.loadWord64 before.world.legacy.shared data.worker.resources.actor
        data.worker.resources.caller.identifier data.worker.resources.callerAddress =
          .ok continuation →
      Borrowing.loadWord64 cut.world.legacy.shared worker.resources.actor
        worker.resources.caller.identifier worker.resources.callerAddress = .ok continuation := by
    intro continuation read
    have sameValue : continuation = data.continuation :=
      Except.ok.inj (read.symm.trans data.caller)
    rw [resources, sameValue]
    exact related.frame.caller
  refine ⟨worker, identifier, handle, live, resources, valid, counter,
    originalSelection, currentSelection, linked, related.frame.code, saved.2, caller, ?_⟩
  intro returned
  refine ⟨?_, completed_count pre actual slot live returned⟩
  have post : CounterCommon.Post data.site data.call cut (atCut slot).history :=
    related.post_of_returned completion live returned
  obtain ⟨final, finalLive, _finalResources, _finalPhase, pc, stack, _finalSaved⟩ := post.returned
  have sameFinal : final = worker := Option.some.inj (finalLive.symm.trans live)
  subst final
  have empty : worker.pending = [] := cutEmpty worker (List.mem_of_getElem? live)
  exact {
    initialLive := data.live
    live := live
    phase := returned
    empty := empty
    nextStore := counter
    resources := resources
    current := valid
    registers := saved.1
    flags := saved.2
    stack := stack
    stackCanonical := by rw [stack]; exact data.entry.scalar.postStackCanonical
    direction := direction_of_mask saved.2 data.entry.scalar.direction
    returnCanonical := by rw [pc]; exact data.canonical
    continuation := ⟨data.continuation, data.caller, pc⟩
    collection := by simp [TSO64.collect, live, returned, empty] }

/-- Assemble every independent prefix obligation from the same actual run. -/
theorem safePrefix
    (pre : Spec.Pre (image compiler) target cell before requests)
    (actual : schedule before actions .ownedOnly .arithmetic = .ok (cut, observations)) :
    Grading.ConcurrentTask.Counted64.SafePrefix (image compiler) target cell before requests
      (cut, observations) := by
  obtain ⟨empty, _covered, _current, _retiring⟩ :=
    (cohort pre).toCohort.schedule_from_current ((cohort pre).covers rfl)
      ((cohort pre).current_toCohort (current pre)) pre.empty actual
  exact {
    valid := schedule_wellFormed pre.valid actual
    stable := schedule_stable actual
    population := ScheduleTrace.workers_length actual
    empty := empty
    memory := prefix_memory pre actual
    frames := prefix_frames pre actual
    increments := fun _index _tid _event observed => prefix_increment pre actual observed
    counts := fun slot => (prefix_events_counts pre actual slot).2
    retiring := prefix_retired pre actual }

/-- The full forall type of the independent Claim.prefixes field, without
asserting an inhabitant of Claim or any other field. -/
theorem prefixes (compiler : CounterCommon.Compiler) :
    ∀ (before : TSO64.State) (target : Atomics64.CellId64)
      (cell : Atomics64.Cell) (requests : Spec.Requests before),
      Spec.Pre (image compiler) target cell before requests → ∀ actions actual,
      schedule before actions .ownedOnly .arithmetic = .ok actual →
      Grading.ConcurrentTask.Counted64.SafePrefix (image compiler) target cell before requests
        actual := by
  intro before target cell requests pre actions actual run
  rcases actual with ⟨cut, observations⟩
  exact safePrefix pre run

#print axioms atomic_nextStore
#print axioms advance_nextStore
#print axioms trace_nextStore
#print axioms checked_inv_saved
#print axioms checked_saved
#print axioms direction_of_mask
#print axioms prefix_frames
#print axioms safePrefix
#print axioms prefixes

end EDSL.Corpus.V1.CounterCounted

#audit_edsl
