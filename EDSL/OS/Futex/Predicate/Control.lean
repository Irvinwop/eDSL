/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Effects
import EDSL.OS.Futex.Predicate.LoopControl

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86

/-- An unchanged actual slot retains its own control. Legacy publication and
loop snapshot knowledge use separate consequences of the actual RAM effect. -/
theorem Kind.Control.frame {cohort : Cohort} {kind : Kind} {worker : Nat}
    {before after : Suspend.State} {actual : TSO.Worker}
    (control : Kind.Control cohort kind worker before actual)
    (pending : after.pending worker = before.pending worker)
    (publication : kind.Published before.machine.memory → kind.Published after.machine.memory)
    (word : loadDWord before.machine.memory cohort.registration.address = .ok 1 →
      loadDWord after.machine.memory cohort.registration.address = .ok 1) :
    Kind.Control cohort kind worker after actual := by
  cases kind with
  | waitLoop client => exact LoopControl.frame control pending word
  | legacy client => exact Clients.WorkerControl.frame control pending publication

/-- Every successful actual issue preserves every real slot. The selected
loop LOAD learns its value from current RAM; peers retain stale-zero cuts. -/
theorem issue_control {cohort : Cohort} {state : Futex.State} {after : Suspend.State}
    {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.issue state.suspended worker = .ok (after, observation)) :
    Control cohort after := by
  have publication := issue_publication admitted actual
  have word := fun published => issue_preserves_published_word admitted published actual
  cases atWorker : state.suspended.machine.workers[worker]? with
  | none => simp [Suspend.issue, atWorker] at actual
  | some before =>
    obtain ⟨kind, member, control⟩ := admitted.control worker before atWorker
    have selected : ∃ current, after.machine.workers[worker]? = some current ∧
        Kind.Control cohort kind worker after current := by
      cases kind with
      | waitLoop client =>
        exact LoopControl.issue_selected control atWorker
          (admitted.currentCode worker (.waitLoop client) member)
          (admitted.static.descriptors worker (.waitLoop client) member).1 admitted.word
          (fun point _ => admitted.loop_ready member point) actual
      | legacy client =>
        exact Clients.WorkerControl.issue_selected control atWorker
          (admitted.currentCode worker (.legacy client) member)
          (admitted.stackViews worker before (.legacy client) atWorker member)
          (admitted.protected worker (.legacy client) member).2.2.2.2.1
          (publication worker (.legacy client) member) actual
    obtain ⟨selected, selectedAt, selectedControl⟩ := selected
    intro query current atAfter
    by_cases own : worker = query
    · subst query
      cases Option.some.inj (selectedAt.symm.trans atAfter)
      exact ⟨kind, member, selectedControl⟩
    · obtain ⟨other, otherAt, otherControl⟩ :=
        admitted.control query current ((Suspend.issue_peer own actual).symm.trans atAfter)
      exact ⟨other, otherAt, otherControl.frame (issue_pending_peer (Ne.symm own) actual)
        (publication query other otherAt) word⟩

/-- A loop's actual FIFO is empty, so a successful selected drain must belong
to a legacy producer. Returned producer FIFOs remain included. -/
theorem drain_control {cohort : Cohort} {state : Futex.State} {after : Suspend.State}
    {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (after, observation)) :
    Control cohort after := by
  obtain ⟨_, _, drained, _⟩ := Suspend.drain_ok _ _ _ actual
  obtain ⟨before, head, tail, _, atWorker, buffer, _⟩ := TSO.drain_ok _ _ _ drained
  obtain ⟨kind, member, control⟩ := admitted.control worker before atWorker
  have selected : ∃ current, after.machine.workers[worker]? = some current ∧
      Kind.Control cohort kind worker after current := by
    cases kind with
    | waitLoop client => simp [LoopControl.fifo_empty control] at buffer
    | legacy client => exact Clients.WorkerControl.drain_selected control atWorker actual
  obtain ⟨selected, selectedAt, selectedControl⟩ := selected
  intro query current atAfter
  by_cases own : worker = query
  · subst query
    cases Option.some.inj (selectedAt.symm.trans atAfter)
    exact ⟨kind, member, selectedControl⟩
  · obtain ⟨other, otherAt, otherControl⟩ :=
      admitted.control query current ((Suspend.drain_peer own actual).symm.trans atAfter)
    refine ⟨other, otherAt, otherControl.frame ?_
      (drain_publication admitted actual query other otherAt) ?_⟩
    · rw [Suspend.drain_pending actual]
    · intro published
      exact (drain_preserves_word admitted actual).trans published

/-- A small selected-client proof for an actual legacy slot. Its exact saved
Family determines the resumed context and operation-typed result. -/
theorem legacy_resume_selected {cohort : Cohort} {client : Clients.Client}
    {state after : Suspend.State} {worker invocation : Nat} {before : TSO.Worker}
    {operation : Op} {flags rcx r11 : Word}
    (control : Clients.WorkerControl client worker state before)
    (atWorker : state.machine.workers[worker]? = some before)
    (descriptor : Clients.Descriptor cohort.legacyEnvironment worker client)
    (outcome : Outcome operation)
    (classified : ∀ saved, state.pending worker = some saved → classify saved.request = .ok operation)
    (actual : Suspend.resume state worker invocation outcome.raw flags rcx r11 = .ok after) :
    ∃ selected, after.machine.workers[worker]? = some selected ∧
      Clients.WorkerControl client worker after selected := by
  obtain ⟨selected, saved, found, _, pending, _, _, _, same⟩ :=
    Suspend.resume_ok _ _ _ _ _ _ _ _ actual
  cases Option.some.inj (atWorker.symm.trans found)
  have family : client.Family saved.request :=
    Kind.Control.pending_family (cohort := cohort) (kind := .legacy client) control pending
  have operationEq : client.operation = operation :=
    Except.ok.inj ((Clients.family_classifies descriptor family).1.symm.trans (classified saved pending))
  cases operationEq
  have publication : client.Published state.machine.memory := by
    cases control with
    | running _ _ _ _ free _ => simp [free] at pending
    | resumed _ _ _ _ _ _ _ free _ _ => simp [free] at pending
    | returned _ _ _ _ _ _ _ free _ _ => simp [free] at pending
    | peerReturned _ _ _ free _ => simp [free] at pending
    | entered _ _ _ _ _ _ _ published => exact published
  refine ⟨⟨client.resumed outcome.raw flags rcx r11, false, []⟩, ?_,
    .resumed outcome flags rcx r11 family.1 rfl rfl (Suspend.resume_consumed actual) rfl ?_⟩
  · rw [same, Clients.family_resume family state.machine.memory outcome.raw flags rcx r11]
    exact List.getElem?_set_self (List.getElem_of_getElem? atWorker).1
  · rw [Suspend.resume_memory actual]
    exact publication

/-- Actual typed resumption preserves heterogeneous controls, arbitrary full
service clobbers, and all peer records. The loop resumes at its real point19. -/
theorem resume_control {cohort : Cohort} {state after : Suspend.State} {operation : Op}
    (control : Control cohort state) (static : Static cohort)
    (outcome : Outcome operation) {worker invocation : Nat} {flags rcx r11 : Word}
    (classified : ∀ saved, state.pending worker = some saved → classify saved.request = .ok operation)
    (actual : Suspend.resume state worker invocation outcome.raw flags rcx r11 = .ok after) :
    Control cohort after := by
  obtain ⟨before, _, atWorker, _⟩ := Suspend.resume_ok _ _ _ _ _ _ _ _ actual
  obtain ⟨kind, member, controlled⟩ := control worker before atWorker
  have selected : ∃ current, after.machine.workers[worker]? = some current ∧
      Kind.Control cohort kind worker after current := by
    cases kind with
    | waitLoop client =>
      obtain ⟨selected, found, _, next⟩ := LoopControl.resume_selected controlled atWorker actual
      exact ⟨selected, found, next⟩
    | legacy client =>
      exact legacy_resume_selected controlled atWorker
        (static.descriptors worker (.legacy client) member).1 outcome classified actual
  obtain ⟨selected, selectedAt, selectedControl⟩ := selected
  intro query current atAfter
  by_cases own : worker = query
  · subst query
    cases Option.some.inj (selectedAt.symm.trans atAfter)
    exact ⟨kind, member, selectedControl⟩
  · obtain ⟨other, otherAt, otherControl⟩ :=
      control query current ((Suspend.resume_peer own actual).symm.trans atAfter)
    refine ⟨other, otherAt, otherControl.frame ?_ ?_ ?_⟩
    · simp [Suspend.resume_pending actual, Ne.symm own]
    · rw [Suspend.resume_memory actual]
      exact id
    · rw [Suspend.resume_memory actual]
      exact id

/-- Service changes physical controls only through its actual ready typed
resume. Other service actions preserve the whole suspended state. -/
theorem service_control {cohort : Cohort} {state after : Futex.State} {action : Futex.Action}
    (control : Control cohort state.suspended) (static : Static cohort)
    (valid : Futex.WellFormed cohort.profile.service state)
    (actual : Futex.step cohort.profile.service state action = .ok after) :
    Control cohort after.suspended := by
  cases action with
  | compare invocation => rw [(compareWait_stutter actual).1]; exact control
  | wake invocation selected => rw [(wakeOne_stutter actual).1]; exact control
  | retry invocation => rw [(retryQueued_stutter actual).1]; exact control
  | spurious invocation => rw [(spuriousReady_stutter actual).1]; exact control
  | idle => cases Except.ok.inj actual; exact control
  | resume invocation flags rcx r11 =>
    obtain ⟨call, outcome, _, _, _, _, atCall, _, _, completed, _, same⟩ := resumeReady_effect actual
    have typed : ∀ saved, state.suspended.pending call.worker = some saved →
        classify saved.request = .ok call.op := by
      obtain ⟨captured, atSaved, _, _, classified⟩ := (valid.calls invocation call atCall).saved
      intro saved pending
      cases Option.some.inj (atSaved.symm.trans pending)
      exact classified
    rw [same]
    exact resume_control control static outcome typed completed

end EDSL.OS.Futex.Predicate

#audit_edsl
