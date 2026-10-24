/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Return
import EDSL.OS.TSO64.ScheduleTrace
import EDSL.OS.TSO64.EffectSimulation.Passive

/-!
Exact RET positions in successful production schedules, for arbitrary authority
profiles and instruction families. Scheduler tids and resource actors retain
their separate meanings. Positions refer to the complete action/observation
lists, including blocked attempts and publications.

Returned workers retain their saved context, phase, resources and next-store
counter. Their pending queues and current published/local memory may change.
Actual RET evidence comes from `Return.returned_origin`, with its current code
and original caller authority; it is never inferred from an RMW payload.

These are conditional laws about finite successful executions. They supply no
schedule success, fairness, termination, cost, ABI, compiler or native-hardware
refinement guarantee. The production model's environmental assumptions and
supported instructions remain those of the imported semantics.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.TSO64.ReturnPositions
open X86 EffectSimulation

/-- No successful own issue, including a blocked attempt, follows return. -/
theorem returned_no_issue {state : TSO64.State} {tid : Nat} {worker : Worker}
    {af : Bool} {result : TSO64.State × Observation} {profile : Profile} {family : RMWFamily}
    (live : state.workers[tid]? = some worker) (returned : worker.phase = .returned)
    (success : step state (.issue tid af) profile family = .ok result) : False := by
  cases step_origin success with
  | ordinary found running _code _caller _fetched _effect =>
    have same := Option.some.inj (found.symm.trans live)
    exact running ((congrArg Worker.phase same).trans returned)
  | blocked found running _code _caller _fetched _bounds _nonempty =>
    have same := Option.some.inj (found.symm.trans live)
    exact running ((congrArg Worker.phase same).trans returned)
  | rmw found running _code _caller _fetched _bounds _empty _grant _effect =>
    have same := Option.some.inj (found.symm.trans live)
    exact running ((congrArg Worker.phase same).trans returned)

/-- Successful actions at a returned worker are necessarily passive for it.
This is derived from the actual step, rather than imposed on the schedule. -/
theorem step_passive {state : TSO64.State} {action : Action}
    {result : TSO64.State × Observation} {profile : Profile} {family : RMWFamily}
    {tid : Nat} {worker : Worker}
    (success : step state action profile family = .ok result)
    (live : state.workers[tid]? = some worker) (returned : worker.phase = .returned) :
    passive tid action := by
  cases action with
  | issue owner af =>
    change owner ≠ tid
    intro same
    subst owner
    exact returned_no_issue live returned success
  | drain _owner => trivial

/-- The saved frame includes all drains, including the returned worker's own.
It deliberately excludes FIFO contents and reconstructed current memory. -/
theorem step_saved {state : TSO64.State} {action : Action}
    {result : TSO64.State × Observation} {profile : Profile} {family : RMWFamily}
    {tid : Nat} {prior : Worker}
    (success : step state action profile family = .ok result)
    (live : state.workers[tid]? = some prior) (returned : prior.phase = .returned) :
    ∃ current, result.1.workers[tid]? = some current ∧ SavedFrame prior current :=
  origin_saved (step_origin success) (step_passive success live returned) live

/-- A currently returned worker is saved across every successful finite
schedule. There is no quiet-schedule, well-formedness or empty-FIFO premise. -/
theorem schedule_saved {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid : Nat} {prior : Worker}
    (success : schedule state actions profile family = .ok result)
    (live : state.workers[tid]? = some prior) (returned : prior.phase = .returned) :
    ∃ current, result.1.workers[tid]? = some current ∧ SavedFrame prior current := by
  induction actions generalizing state result prior with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    exact ⟨prior, live, .refl _⟩
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    obtain ⟨middle, middleLive, firstSaved⟩ := step_saved stepped live returned
    obtain ⟨current, currentLive, tailSaved⟩ :=
      ih following middleLive (firstSaved.phase.trans returned)
    exact ⟨current, by simpa only [same] using currentLive, firstSaved.trans tailSaved⟩

/-- Passivity of the entire successful suffix is a consequence of returned
phase, not an assumption about which actions the caller selected. -/
theorem schedule_passive {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid : Nat} {prior : Worker}
    (success : schedule state actions profile family = .ok result)
    (live : state.workers[tid]? = some prior) (returned : prior.phase = .returned) :
    ∀ action ∈ actions, passive tid action := by
  induction actions generalizing state result prior with
  | nil => simp
  | cons action rest ih =>
    obtain ⟨first, _tail, stepped, following, _same⟩ := schedule_cons_ok success
    obtain ⟨middle, middleLive, saved⟩ := step_saved stepped live returned
    have quiet := step_passive stepped live returned
    have remaining := ih following middleLive (saved.phase.trans returned)
    intro selected member
    rcases List.mem_cons.mp member with same | later
    · subst selected
      exact quiet
    · exact remaining selected later

/-- Every original action position excludes a successful own issue. -/
theorem schedule_no_issue {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid index : Nat} {af : Bool} {prior : Worker}
    (success : schedule state actions profile family = .ok result)
    (live : state.workers[tid]? = some prior) (returned : prior.phase = .returned) :
    actions[index]? ≠ some (.issue tid af) := by
  intro found
  have quiet := schedule_passive success live returned (.issue tid af) (List.mem_of_getElem? found)
  exact quiet rfl

/-- The tid of a real RMW label is its issuing scheduler slot. Nothing here
identifies that slot with the event's resource actor. -/
theorem rmw_issue {state after : TSO64.State} {action : Action}
    {tid : Nat} {event : Atomics64.FetchAddEvent} {profile : Profile} {family : RMWFamily}
    (success : step state action profile family = .ok (after, .rmw tid event)) :
    ∃ af, action = .issue tid af := by
  cases step_origin success with
  | ordinary _live _running _code _caller _fetched effect =>
    cases effect with
    | intro _supported _bounds _decoded _reads _queue _executed finish => cases finish
  | rmw => exact ⟨_, rfl⟩

theorem returned_no_rmw {state after : TSO64.State} {action : Action}
    {tid : Nat} {worker : Worker} {event : Atomics64.FetchAddEvent}
    {profile : Profile} {family : RMWFamily}
    (live : state.workers[tid]? = some worker) (returned : worker.phase = .returned)
    (success : step state action profile family = .ok (after, .rmw tid event)) : False := by
  obtain ⟨af, issued⟩ := rmw_issue success
  rw [issued] at success
  exact returned_no_issue live returned success

/-- A second response is excluded using its actual RET origin. -/
theorem returned_no_return {state after : TSO64.State} {action : Action}
    {tid : Nat} {worker : Worker} {profile : Profile} {family : RMWFamily}
    (valid : WellFormed state profile)
    (live : state.workers[tid]? = some worker) (returned : worker.phase = .returned)
    (success : step state action profile family = .ok (after, .returned tid)) : False := by
  obtain ⟨_value, _projected, origin⟩ := Return.returned_origin valid success
  obtain ⟨af, _prior, _output, _observation, issued, _rest⟩ := origin
  rw [issued] at success
  exact returned_no_issue live returned success

theorem schedule_no_rmw {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid index : Nat} {prior : Worker} {event : Atomics64.FetchAddEvent}
    (success : schedule state actions profile family = .ok result)
    (live : state.workers[tid]? = some prior) (returned : prior.phase = .returned) :
    result.2[index]? ≠ some (.rmw tid event) := by
  intro found
  obtain ⟨_before, _action, _after, prefixRun, _actionAt, stepped⟩ :=
    ScheduleTrace.observation_at success found
  obtain ⟨current, currentLive, saved⟩ := schedule_saved prefixRun live returned
  exact returned_no_rmw currentLive (saved.phase.trans returned) stepped

theorem schedule_no_return {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid index : Nat} {prior : Worker}
    (valid : WellFormed state profile)
    (success : schedule state actions profile family = .ok result)
    (live : state.workers[tid]? = some prior) (returned : prior.phase = .returned) :
    result.2[index]? ≠ some (.returned tid) := by
  intro found
  obtain ⟨_before, _action, _after, prefixRun, _actionAt, stepped⟩ :=
    ScheduleTrace.observation_at success found
  obtain ⟨current, currentLive, saved⟩ := schedule_saved prefixRun live returned
  exact returned_no_return (schedule_wellFormed valid prefixRun)
    currentLive (saved.phase.trans returned) stepped

private theorem drop_at {α : Type} {entries : List α} {index : Nat} {entry : α}
    (found : entries[index]? = some entry) :
    entries.drop index = entry :: entries.drop (index + 1) := by
  obtain ⟨bound, selected⟩ := List.getElem_of_getElem? found
  simpa only [selected] using (List.drop_eq_getElem_cons bound)

/-- Consume one actual position of the exact suffix supplied by
`ScheduleTrace.suffix`. The successor is the real step result. -/
private theorem observation_cut {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {index : Nat} {observation : Observation}
    (success : schedule state actions profile family = .ok result)
    (found : result.2[index]? = some observation) :
    ∃ before action after,
      schedule state (actions.take index) profile family = .ok (before, result.2.take index) ∧
      actions[index]? = some action ∧
      step before action profile family = .ok (after, observation) ∧
      schedule after (actions.drop (index + 1)) profile family =
        .ok (result.1, result.2.drop (index + 1)) := by
  obtain ⟨before, action, after, prefixRun, actionAt, stepped⟩ :=
    ScheduleTrace.observation_at success found
  have remaining := (ScheduleTrace.suffix success prefixRun).2
  rw [drop_at actionAt] at remaining
  obtain ⟨first, tail, firstStep, tailRun, whole⟩ := schedule_cons_ok remaining
  have firstEq : first = (after, observation) := Except.ok.inj (firstStep.symm.trans stepped)
  subst first
  have tailEq : tail = (result.1, result.2.drop (index + 1)) := by
    apply Prod.ext
    · exact (congrArg Prod.fst whole).symm
    · have observationsEq : observation :: result.2.drop (index + 1) = observation :: tail.2 := by
        simpa only [drop_at found] using congrArg Prod.snd whole
      exact (List.cons.inj observationsEq).2.symm
  exact ⟨before, action, after, prefixRun, actionAt, stepped,
    tailRun.trans (congrArg Except.ok tailEq)⟩

/-- An actual returned label supplies its exact prefix, selected action,
checked RET origin and remaining successful suffix. Caller authority is checked
at the actual prefix world by the imported response theorem. -/
theorem returned_at {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid index : Nat} (valid : WellFormed state profile)
    (success : schedule state actions profile family = .ok result)
    (found : result.2[index]? = some (.returned tid)) :
    ∃ before action after value,
      schedule state (actions.take index) profile family = .ok (before, result.2.take index) ∧
      actions[index]? = some action ∧
      step before action profile family = .ok (after, .returned tid) ∧
      Return.ReturnOrigin before action (after, .returned tid) tid value profile family ∧
      schedule after (actions.drop (index + 1)) profile family =
        .ok (result.1, result.2.drop (index + 1)) := by
  obtain ⟨before, action, after, prefixRun, actionAt, stepped, suffixRun⟩ :=
    observation_cut success found
  obtain ⟨value, _projected, origin⟩ :=
    Return.returned_origin (schedule_wellFormed valid prefixRun) stepped
  exact ⟨before, action, after, value, prefixRun, actionAt, stepped, origin, suffixRun⟩

private theorem returned_suffix {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid index : Nat} (valid : WellFormed state profile)
    (success : schedule state actions profile family = .ok result)
    (found : result.2[index]? = some (.returned tid)) :
    ∃ after current, WellFormed after profile ∧
      schedule after (actions.drop (index + 1)) profile family =
        .ok (result.1, result.2.drop (index + 1)) ∧
      after.workers[tid]? = some current ∧ current.phase = .returned := by
  obtain ⟨_before, _action, after, _value, prefixRun, _actionAt, stepped, origin, suffixRun⟩ :=
    returned_at valid success found
  obtain ⟨_world, _prior, current, _priorLive, currentLive, _valueEq, phase,
    _resources, _pending, _nextStore⟩ := origin.frame
  exact ⟨after, current, step_wellFormed (schedule_wellFormed valid prefixRun) stepped,
    suffixRun, currentLive, phase⟩

/-- After an actual RET position, every later original action position
excludes that worker's issue, even if it would only have blocked. -/
theorem no_issue_after_return {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid index later : Nat} {af : Bool} (valid : WellFormed state profile)
    (success : schedule state actions profile family = .ok result)
    (returned : result.2[index]? = some (.returned tid)) (ordered : index < later) :
    actions[later]? ≠ some (.issue tid af) := by
  intro found
  obtain ⟨_after, _current, _validAfter, suffixRun, currentLive, phase⟩ :=
    returned_suffix valid success returned
  have localAt : (actions.drop (index + 1))[later - (index + 1)]? = some (.issue tid af) := by
    rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
    exact found
  exact schedule_no_issue suffixRun currentLive phase localAt

theorem no_rmw_after_return {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid index later : Nat} {event : Atomics64.FetchAddEvent} (valid : WellFormed state profile)
    (success : schedule state actions profile family = .ok result)
    (returned : result.2[index]? = some (.returned tid)) (ordered : index < later) :
    result.2[later]? ≠ some (.rmw tid event) := by
  intro found
  obtain ⟨_after, _current, _validAfter, suffixRun, currentLive, phase⟩ :=
    returned_suffix valid success returned
  have localAt : (result.2.drop (index + 1))[later - (index + 1)]? = some (.rmw tid event) := by
    rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
    exact found
  exact schedule_no_rmw suffixRun currentLive phase localAt

theorem no_return_after_return {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid index later : Nat} (valid : WellFormed state profile)
    (success : schedule state actions profile family = .ok result)
    (returned : result.2[index]? = some (.returned tid)) (ordered : index < later) :
    result.2[later]? ≠ some (.returned tid) := by
  intro found
  obtain ⟨_after, _current, validAfter, suffixRun, currentLive, phase⟩ :=
    returned_suffix valid success returned
  have localAt : (result.2.drop (index + 1))[later - (index + 1)]? = some (.returned tid) := by
    rw [List.getElem?_drop, Nat.add_sub_of_le (by omega)]
    exact found
  exact schedule_no_return validAfter suffixRun currentLive phase localAt

/-- A worker has at most one actual returned label in the complete trace. -/
theorem returned_unique {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid index other : Nat} (valid : WellFormed state profile)
    (success : schedule state actions profile family = .ok result)
    (first : result.2[index]? = some (.returned tid))
    (second : result.2[other]? = some (.returned tid)) : other = index := by
  by_cases same : other = index
  · exact same
  · by_cases later : index < other
    · exact False.elim (no_return_after_return valid success first later second)
    · exact False.elim (no_return_after_return valid success second (by omega) first)

/-- Every own RMW observation precedes the actual RET, using indices in the
original observation list. No cell, delta, payload or call-count restriction. -/
theorem rmw_before_return {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid rmwIndex returnIndex : Nat} {event : Atomics64.FetchAddEvent}
    (valid : WellFormed state profile)
    (success : schedule state actions profile family = .ok result)
    (rmw : result.2[rmwIndex]? = some (.rmw tid event))
    (returned : result.2[returnIndex]? = some (.returned tid)) : rmwIndex < returnIndex := by
  by_cases before : rmwIndex < returnIndex
  · exact before
  · by_cases same : rmwIndex = returnIndex
    · subst rmwIndex
      have impossible : Observation.rmw tid event = .returned tid :=
        Option.some.inj (rmw.symm.trans returned)
      cases impossible
    · exact False.elim (no_rmw_after_return valid success returned (by omega) rmw)

private theorem install_phase {state : TSO64.State} {owner tid : Nat} {world : World}
    {subject prior replacement : Worker} {observation : Observation}
    (subjectLive : state.workers[owner]? = some subject)
    (priorLive : state.workers[tid]? = some prior)
    (phase : replacement.phase = subject.phase ∨ observation = .returned owner) :
    ∃ current, (install state owner world replacement).workers[tid]? = some current ∧
      (current.phase = prior.phase ∨ observation = .returned tid) := by
  by_cases same : tid = owner
  · subst tid
    have priorEq : prior = subject := Option.some.inj (priorLive.symm.trans subjectLive)
    subst prior
    exact ⟨replacement, List.getElem?_set_self (List.getElem_of_getElem? subjectLive).1, phase⟩
  · exact ⟨prior, (install_peer same).trans priorLive, .inl rfl⟩

/-- Inversion of native phase transitions: the slot survives, and its phase
can change only at its own returned observation. The conclusion is derived
from every actual origin and both ordinary finish constructors. -/
theorem step_phase_or_return {state : TSO64.State} {action : Action}
    {result : TSO64.State × Observation} {profile : Profile} {family : RMWFamily}
    {tid : Nat} {prior : Worker}
    (success : step state action profile family = .ok result)
    (live : state.workers[tid]? = some prior) :
    ∃ current, result.1.workers[tid]? = some current ∧
      (current.phase = prior.phase ∨ result.2 = .returned tid) := by
  cases step_origin success with
  | ordinary subjectLive _running _code _caller _fetched effect =>
    cases effect with
    | intro _supported _bounds _decoded _reads _queue _executed finish =>
      cases finish with
      | next _outcome => exact install_phase subjectLive live (.inl rfl)
      | returned _outcome => exact install_phase subjectLive live (.inr rfl)
  | blocked => exact ⟨prior, live, .inl rfl⟩
  | rmw subjectLive _running _code _caller _fetched _bounds _empty _grant _effect =>
    exact install_phase subjectLive live (.inl rfl)
  | drained subjectLive _fifo _gate _changed _effect =>
    exact install_phase subjectLive live (.inl rfl)

/-- Final returned phase of an initially nonreturned slot forces a real
returned observation. No return position or desired ordering is a premise. -/
theorem returned_label_of_final {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid : Nat} {prior current : Worker}
    (success : schedule state actions profile family = .ok result)
    (live : state.workers[tid]? = some prior) (running : prior.phase ≠ .returned)
    (finalLive : result.1.workers[tid]? = some current) (returned : current.phase = .returned) :
    ∃ index : Nat, result.2[index]? = some (Observation.returned tid) := by
  induction actions generalizing state result prior with
  | nil =>
    have same : (state, []) = result := Except.ok.inj success
    subst result
    have workerEq : prior = current := Option.some.inj (live.symm.trans finalLive)
    exact False.elim (running ((congrArg Worker.phase workerEq).trans returned))
  | cons action rest ih =>
    obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
    obtain ⟨middle, middleLive, phaseOrReturn⟩ := step_phase_or_return stepped live
    by_cases observed : first.2 = .returned tid
    · refine ⟨0, ?_⟩
      simpa only [same, List.getElem?_cons_zero, Option.some.injEq] using observed
    · have middleRunning : middle.phase ≠ .returned := by
        intro phase
        rcases phaseOrReturn with unchanged | response
        · exact running (unchanged.symm.trans phase)
        · exact observed response
      have tailLive : tail.1.workers[tid]? = some current := by
        simpa only [same] using finalLive
      obtain ⟨index, found⟩ := ih following middleLive middleRunning tailLive
      exact ⟨index + 1, by simpa only [same, List.getElem?_cons_succ] using found⟩

/-- An initially running worker that ends returned has a unique original RET
position, with the actual machine/resource origin and exact prefix and suffix.
No manager, counter, invocation classification or actor/tid equation is used. -/
theorem returned_position_of_final {state : TSO64.State} {actions : List Action}
    {result : TSO64.State × List Observation} {profile : Profile} {family : RMWFamily}
    {tid : Nat} {prior current : Worker} (valid : WellFormed state profile)
    (success : schedule state actions profile family = .ok result)
    (live : state.workers[tid]? = some prior) (running : prior.phase = .running)
    (finalLive : result.1.workers[tid]? = some current) (returned : current.phase = .returned) :
    ∃ index, index < actions.length ∧ result.2[index]? = some (.returned tid) ∧
      (∀ other, result.2[other]? = some (.returned tid) → other = index) ∧
      ∃ before action after value,
        schedule state (actions.take index) profile family = .ok (before, result.2.take index) ∧
        actions[index]? = some action ∧
        step before action profile family = .ok (after, .returned tid) ∧
        Return.ReturnOrigin before action (after, .returned tid) tid value profile family ∧
        schedule after (actions.drop (index + 1)) profile family =
          .ok (result.1, result.2.drop (index + 1)) := by
  have notReturned : prior.phase ≠ .returned := by
    intro phase
    have impossible : Phase.running = Phase.returned := running.symm.trans phase
    cases impossible
  obtain ⟨index, found⟩ := returned_label_of_final success live notReturned finalLive returned
  have bound : index < actions.length := by
    rw [← ScheduleTrace.length success]
    exact (List.getElem_of_getElem? found).1
  exact ⟨index, bound, found, fun _ other => returned_unique valid success found other,
    returned_at valid success found⟩

end EDSL.OS.TSO64.ReturnPositions

#print axioms EDSL.OS.TSO64.ReturnPositions.returned_no_issue
#print axioms EDSL.OS.TSO64.ReturnPositions.step_passive
#print axioms EDSL.OS.TSO64.ReturnPositions.step_saved
#print axioms EDSL.OS.TSO64.ReturnPositions.schedule_saved
#print axioms EDSL.OS.TSO64.ReturnPositions.schedule_passive
#print axioms EDSL.OS.TSO64.ReturnPositions.schedule_no_issue
#print axioms EDSL.OS.TSO64.ReturnPositions.rmw_issue
#print axioms EDSL.OS.TSO64.ReturnPositions.returned_no_rmw
#print axioms EDSL.OS.TSO64.ReturnPositions.returned_no_return
#print axioms EDSL.OS.TSO64.ReturnPositions.schedule_no_rmw
#print axioms EDSL.OS.TSO64.ReturnPositions.schedule_no_return
#print axioms EDSL.OS.TSO64.ReturnPositions.returned_at
#print axioms EDSL.OS.TSO64.ReturnPositions.no_issue_after_return
#print axioms EDSL.OS.TSO64.ReturnPositions.no_rmw_after_return
#print axioms EDSL.OS.TSO64.ReturnPositions.no_return_after_return
#print axioms EDSL.OS.TSO64.ReturnPositions.returned_unique
#print axioms EDSL.OS.TSO64.ReturnPositions.rmw_before_return
#print axioms EDSL.OS.TSO64.ReturnPositions.step_phase_or_return
#print axioms EDSL.OS.TSO64.ReturnPositions.returned_label_of_final
#print axioms EDSL.OS.TSO64.ReturnPositions.returned_position_of_final
#audit_edsl
