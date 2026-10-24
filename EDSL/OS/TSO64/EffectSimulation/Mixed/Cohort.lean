/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.IssuePreservation
import EDSL.OS.TSO64.ScheduleTrace
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Caller-only cohort closure over actual production TSO64 steps and schedules.
Descriptors and annotations share a family/profile, but retain their individual
graphs, assertions, resources and ghosts. The policy law concerns source
descriptors at arbitrary current states; it mentions no execution or success.
Coverage accounts for every current live scheduler slot, independently of
worker actor identities. Independent Entries admit the initial state.

Ordinary/RET preservation uses the checked current `OrdinaryIssued` bridge in
IssuePreservation. Native atomic origins preserve the issuing queue. Initially
empty queues therefore remain empty, so successful drains and blocked attempts
are impossible. The fold advances every subject through the same actual step
and shared actual prefix state. It never identifies separately produced ghost
histories, nor uses native origins as a converse to checked execution.

These are conditional successful finite-run theorems under the imported target,
OS authority, lifetime, synchronization and translation contracts. No enabled
schedule, termination, final counter value, releasing join, compiler refinement
or physical-hardware refinement is established here. The index type may be a
finite enumeration; injectivity and counting are unnecessary for closure.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed
open X86

/-- Independently annotated subjects at one common production family/profile.
The policy equation is source data, not a future no-enqueue assumption. -/
structure Cohort (ι : Type) (profile : Profile) (family : RMWFamily) where
  descriptor : ι → Descriptor
  post : ι → Assertion
  annotations : ∀ subject : ι, Annotations (descriptor subject) (post subject)
  profile_eq : ∀ subject : ι, (descriptor subject).profile = profile
  family_eq : ∀ subject : ι, (descriptor subject).family = family
  callerPolicy : ∀ (subject : ι) (state : S),
    (descriptor subject).policy state = authorityCallerPolicy (descriptor subject) state

variable {ι : Type} {profile : Profile} {family : RMWFamily}

/-- Exhaustive current slots; no scheduler tid is identified with an actor. -/
def Cohort.Covers (cohort : Cohort ι profile family) (state : S) : Prop :=
  ∀ (tid : Nat) (worker : Worker), state.workers[tid]? = some worker →
    ∃ subject : ι, (cohort.descriptor subject).tid = tid

/-- Each subject retains its own current ghost from the same initial state.
No equality between different subjects' stateful histories is required. -/
def Cohort.Current (cohort : Cohort ι profile family) (initial state : S) : Prop :=
  ∀ subject : ι,
    ∃ ghost : Ghost (cohort.descriptor subject) initial (cohort.post subject),
      Related (cohort.annotations subject) state ghost

/-- Only present admissions, bindings and independent cut assertions. -/
def Cohort.Entries (cohort : Cohort ι profile family) (initial : S) : Prop :=
  ∀ subject : ι, ∃ node : (cohort.descriptor subject).graph.Index,
    Entry (cohort.annotations subject) initial node

/-- An actual position is an issue by a covered subject and retires exactly
one ordinary instruction, RET or native RMW. Both lists remain unfiltered. -/
def Cohort.Retires (cohort : Cohort ι profile family) (action : Action) (seen : O) : Prop :=
  ∃ (subject : ι) (af : Bool), action = .issue (cohort.descriptor subject).tid af ∧
    (seen = .ordinary (cohort.descriptor subject).tid ∨
      seen = .returned (cohort.descriptor subject).tid ∨
      ∃ event : Atomics64.FetchAddEvent, seen = .rmw (cohort.descriptor subject).tid event)

/-- Positionwise classification of the complete original lists. This relation
records retirement labels only; it supplies no execution or scheduling rule. -/
inductive Cohort.RetirementTrace (cohort : Cohort ι profile family) :
    List Action → List O → Prop where
  | nil : RetirementTrace cohort [] []
  | cons {action : Action} {seen : O} {actions : List Action} {observations : List O}
      (head : cohort.Retires action seen)
      (tail : RetirementTrace cohort actions observations) :
      RetirementTrace cohort (action :: actions) (seen :: observations)

private theorem ordinary_labels
    {before : S} {tid : Nat} {worker : Worker} {instruction : Sequential.Instruction}
    {af : Bool} {result : S × O} {profile : Profile}
    (effect : OrdinaryEffect before tid worker instruction af result profile) :
    result.2 = .ordinary tid ∨ result.2 = .returned tid := by
  cases effect with
  | intro _supported _bounds _decoded _reads _queue _executed finish =>
    cases finish with
    | next => exact Or.inl rfl
    | returned => exact Or.inr rfl

private theorem quiescent_install {before : S} {tid : Nat} {world : World}
    {worker : Worker} (empty : Quiescent before) (ownEmpty : worker.pending = []) :
    Quiescent (install before tid world worker) := by
  intro current member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact empty current old
  · exact ownEmpty

/-- An actual own-issue queue frame plus the production peer frame covers all
successor workers, including workers other than the current subject. -/
private theorem quiescent_issue {before after : S} {tid : Nat} {af : Bool} {seen : O}
    {profile : Profile} {family : RMWFamily} {current : Worker}
    (empty : Quiescent before)
    (actual : TSO64.step before (.issue tid af) profile family = .ok (after, seen))
    (installed : after.workers[tid]? = some current) (ownEmpty : current.pending = []) :
    Quiescent after := by
  intro worker member
  obtain ⟨thread, live⟩ := List.mem_iff_getElem?.mp member
  by_cases own : thread = tid
  · subst thread
    have same : worker = current := Option.some.inj (live.symm.trans installed)
    exact (congrArg Worker.pending same).trans ownEmpty
  · exact empty worker (List.mem_of_getElem? ((step_peer actual own).symm.trans live))

/-- Present Entries initialize all current ghosts without any future premise. -/
theorem Cohort.current_of_entries (cohort : Cohort ι profile family) {initial : S}
    (entries : cohort.Entries initial) : cohort.Current initial initial := by
  intro subject
  obtain ⟨node, entry⟩ := entries subject
  exact ⟨initialGhost (cohort.descriptor subject) initial (cohort.post subject) node,
    entry.related⟩

/-- Transport coverage using only the fixed universe of scheduler slots. -/
theorem Cohort.covers_of_length (cohort : Cohort ι profile family) {before after : S}
    (covered : cohort.Covers before) (length : after.workers.length = before.workers.length) :
    cohort.Covers after := by
  intro tid worker live
  have bound := (List.getElem_of_getElem? live).1
  rw [length] at bound
  exact covered tid (before.workers[tid]'bound) (List.getElem?_eq_getElem bound)

/-- A successful production step retains exhaustive slot coverage. -/
theorem Cohort.covers_step (cohort : Cohort ι profile family)
    {before after : S} {action : Action} {seen : O}
    (covered : cohort.Covers before)
    (actual : TSO64.step before action profile family = .ok (after, seen)) :
    cohort.Covers after := by
  have singletonRun : TSO64.schedule before [action] profile family = .ok (after, [seen]) := by
    simp only [TSO64.schedule, actual, ok_bind, pure_ok]
  exact cohort.covers_of_length covered (ScheduleTrace.workers_length singletonRun)

/-- Lift the same current actual step independently for every subject.
No projection equality is used to identify stateful ghost histories. -/
theorem Cohort.current_step (cohort : Cohort ι profile family)
    {initial before after : S} {action : Action} {seen : O}
    (current : cohort.Current initial before)
    (actual : TSO64.step before action profile family = .ok (after, seen)) :
    cohort.Current initial after := by
  intro subject
  obtain ⟨_ghost, related⟩ := current subject
  have selected : TSO64.step before action (cohort.descriptor subject).profile
      (cohort.descriptor subject).family = .ok (after, seen) := by
    simpa only [cohort.profile_eq subject, cohort.family_eq subject] using actual
  obtain ⟨next, _advance, nextRelated⟩ :=
    (cohort.annotations subject).simulation.lift related.frame.wellFormed related selected
  exact ⟨next, nextRelated⟩

/-- Minimal closure law for one current actual step. Ordinary and RET cases
consume current typed checked evidence through IssuePreservation; there is no
caller-supplied no-enqueue predicate or premise about a later successful run. -/
theorem Cohort.step_closed (cohort : Cohort ι profile family)
    {initial before after : S} {action : Action} {seen : O}
    (covered : cohort.Covers before) (current : cohort.Current initial before)
    (empty : Quiescent before)
    (actual : TSO64.step before action profile family = .ok (after, seen)) :
    Quiescent after ∧ cohort.Covers after ∧ cohort.Current initial after ∧
      cohort.Retires action seen := by
  have closed : Quiescent after ∧ cohort.Retires action seen := by
    cases action with
    | issue tid af =>
      cases step_origin actual with
      | ordinary live _running _code _caller _fetched effect =>
        have labels := ordinary_labels effect
        obtain ⟨subject, subjectTid⟩ := covered tid _ live
        obtain ⟨_ghost, related⟩ := current subject
        have selected : TSO64.step before (.issue (cohort.descriptor subject).tid af)
            (cohort.descriptor subject).profile (cohort.descriptor subject).family =
              .ok (after, seen) := by
          simpa only [subjectTid, cohort.profile_eq subject, cohort.family_eq subject] using actual
        have ownLabels : seen = .ordinary (cohort.descriptor subject).tid ∨
            seen = .returned (cohort.descriptor subject).tid := by
          simpa only [subjectTid] using labels
        obtain ⟨_world, installedWorker, installedLive, pending, _counter, _resources⟩ :=
          (cohort.annotations subject).callerOnly_preserves_of_step related selected ownLabels
            (cohort.callerPolicy subject before) (by simpa only [subjectTid] using live)
        have ownEmpty : installedWorker.pending = [] :=
          pending.trans (empty _ (List.mem_of_getElem? live))
        have atTid : after.workers[tid]? = some installedWorker := by
          simpa only [subjectTid] using installedLive
        refine ⟨quiescent_issue empty actual atTid ownEmpty, subject, af, ?_, ?_⟩
        · rw [subjectTid]
        · rcases ownLabels with ordinary | returned
          · exact Or.inl ordinary
          · exact Or.inr (Or.inl returned)
      | blocked live _running _code _caller _fetched _bounds nonempty =>
        exact False.elim (nonempty (empty _ (List.mem_of_getElem? live)))
      | rmw live _running _code _caller _fetched _bounds ownEmpty _grant _effect =>
        obtain ⟨subject, subjectTid⟩ := covered tid _ live
        refine ⟨quiescent_install empty ownEmpty, subject, af, ?_, ?_⟩
        · rw [subjectTid]
        · exact Or.inr (Or.inr ⟨_, by rw [subjectTid]⟩)
    | drain _tid =>
      cases step_origin actual with
      | drained live fifo _gate _changed _effect =>
        have ownEmpty := empty _ (List.mem_of_getElem? live)
        rw [ownEmpty] at fifo
        cases fifo
  exact ⟨closed.1, cohort.covers_step covered actual, cohort.current_step current actual, closed.2⟩

/-- The classification excludes blocked/drained observations by construction. -/
theorem Cohort.Retires.retired {cohort : Cohort ι profile family} {action : Action} {seen : O}
    (retiring : cohort.Retires action seen) : seen.retired = 1 := by
  obtain ⟨_subject, _af, _issued, labels⟩ := retiring
  rcases labels with rfl | rfl | ⟨_event, rfl⟩ <;> rfl

/-- Fold one-step closure over the actual schedule, with one shared actual
intermediate state at every recursive call and one current ghost per subject. -/
theorem Cohort.schedule_from_current (cohort : Cohort ι profile family)
    {initial before final : S} {actions : List Action} {observations : List O}
    (covered : cohort.Covers before) (current : cohort.Current initial before)
    (empty : Quiescent before)
    (actual : TSO64.schedule before actions profile family = .ok (final, observations)) :
    Quiescent final ∧ cohort.Covers final ∧ cohort.Current initial final ∧
      cohort.RetirementTrace actions observations := by
  induction actions generalizing before final observations with
  | nil =>
    have same : (before, []) = (final, observations) := Except.ok.inj actual
    have finalEq : before = final := congrArg Prod.fst same
    have observationsEq : [] = observations := congrArg Prod.snd same
    subst final
    subst observations
    exact ⟨empty, covered, current, .nil⟩
  | cons action rest ih =>
    obtain ⟨⟨middle, seen⟩, ⟨last, tail⟩, stepped, scheduled, same⟩ :=
      schedule_cons_ok actual
    obtain ⟨middleEmpty, middleCovered, middleCurrent, retiring⟩ :=
      cohort.step_closed covered current empty stepped
    obtain ⟨lastEmpty, lastCovered, lastCurrent, restRetiring⟩ :=
      ih middleCovered middleCurrent middleEmpty scheduled
    have finalEq : final = last := congrArg Prod.fst same
    have observationsEq : observations = seen :: tail := congrArg Prod.snd same
    rw [finalEq, observationsEq]
    exact ⟨lastEmpty, lastCovered, lastCurrent, .cons retiring restRetiring⟩

/-- Public initial-state API: independently admitted Entries, exhaustive
initial slots and empty initial FIFOs derive closure of a successful schedule. -/
theorem Cohort.schedule (cohort : Cohort ι profile family)
    {initial final : S} {actions : List Action} {observations : List O}
    (covered : cohort.Covers initial) (entries : cohort.Entries initial)
    (empty : Quiescent initial)
    (actual : TSO64.schedule initial actions profile family = .ok (final, observations)) :
    Quiescent final ∧ cohort.Covers final ∧ cohort.Current initial final ∧
      cohort.RetirementTrace actions observations :=
  cohort.schedule_from_current covered (cohort.current_of_entries entries) empty actual

/-- Every actual prefix has derived empty FIFOs and current relatedness for
every subject, including past-end cuts. The exact prefix/suffix executions are
retained; no independently produced stateful histories are identified. -/
theorem Cohort.schedule_cut (cohort : Cohort ι profile family)
    {initial final : S} {actions : List Action} {observations : List O}
    (covered : cohort.Covers initial) (entries : cohort.Entries initial)
    (empty : Quiescent initial)
    (actual : TSO64.schedule initial actions profile family = .ok (final, observations))
    (index : Nat) :
    ∃ before,
      TSO64.schedule initial (actions.take index) profile family =
        .ok (before, observations.take index) ∧
      TSO64.schedule before (actions.drop index) profile family =
        .ok (final, observations.drop index) ∧
      Quiescent before ∧ cohort.Covers before ∧ cohort.Current initial before ∧
      cohort.RetirementTrace (actions.take index) (observations.take index) := by
  obtain ⟨before, prefixRun, suffixRun⟩ := ScheduleTrace.cut actual index
  obtain ⟨prefixEmpty, prefixCovered, prefixCurrent, prefixRetiring⟩ :=
    cohort.schedule covered entries empty prefixRun
  exact ⟨before, prefixRun, suffixRun, prefixEmpty, prefixCovered, prefixCurrent, prefixRetiring⟩

#print axioms Cohort
#print axioms Cohort.Covers
#print axioms Cohort.Current
#print axioms Cohort.Entries
#print axioms Cohort.Retires
#print axioms Cohort.RetirementTrace
#print axioms ordinary_labels
#print axioms quiescent_install
#print axioms quiescent_issue
#print axioms Cohort.current_of_entries
#print axioms Cohort.covers_of_length
#print axioms Cohort.covers_step
#print axioms Cohort.current_step
#print axioms Cohort.step_closed
#print axioms Cohort.Retires.retired
#print axioms Cohort.schedule_from_current
#print axioms Cohort.schedule
#print axioms Cohort.schedule_cut

end EDSL.OS.TSO64.EffectSimulation.Mixed

#audit_edsl
