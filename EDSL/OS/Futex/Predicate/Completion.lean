/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Completion.Steps

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86
namespace Completion

/-- Each nonterminal current cut constructs one actual selected issue or one
service action for its own current call, with a strictly smaller action bound.
No drain of this worker or any peer is selected. -/
theorem Cut.progress {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} {count : Nat} (cut : Cut client worker state count)
    (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker) (flags rcx r11 : Word) :
    (∃ actual, state.suspended.machine.workers[worker]? = some actual ∧ actual.returned = true) ∨
    ∃ after next action observation,
      CompletionAction worker state action ∧
      Runtime.step cohort.profile state action = .ok (after, observation) ∧
      Admitted cohort after ∧ Cut client worker after next ∧ next + 1 ≤ count ∧
      PrivateFrame worker state.suspended after.suspended ∧
      Futex.Notification.NoQueuedWait after worker := by
  cases cut with
  | @running point running =>
    apply Or.inr
    by_cases call : point = .syscall
    · subst point
      obtain ⟨after, count, step, valid, next, bound, frame, afterClear⟩ :=
        capture_step admitted member clear running
      exact ⟨after, count, .issue worker, _, rfl, step, valid, next,
        Nat.succ_le_succ bound, frame, afterClear⟩
    · by_cases done : ∃ observed, point = .done observed
      · obtain ⟨observed, rfl⟩ := done
        obtain ⟨after, step, valid, next, frame, afterClear⟩ :=
          return_step admitted member clear running
        exact ⟨after, 0, .issue worker, _, rfl, step, valid, next,
          by simp only [remaining]; decide, frame, afterClear⟩
      · obtain ⟨after, point, step, valid, next, bound, frame, afterClear⟩ :=
          ordinary_step admitted member published clear running call
            (fun observed same => done ⟨observed, same⟩)
        exact ⟨after, remaining point, .issue worker, _, rfl, step, valid, next, bound, frame, afterClear⟩
  | @entered saved pin pending found =>
    obtain ⟨after, step, valid, next, frame, afterClear⟩ :=
      compare_step admitted member published clear pending found
    exact .inr ⟨after, 8, .service (.compare saved.identifier), _, ⟨_, found, rfl, rfl⟩,
      step, valid, next, by decide, frame, afterClear⟩
  | @ready saved pin outcome origin pending found =>
    obtain ⟨after, raw, step, valid, next, frame, afterClear⟩ :=
      resume_step admitted member published clear pending found flags rcx r11
    exact .inr ⟨after, remaining (.resumed raw), .service (.resume saved.identifier flags rcx r11), _,
      ⟨_, found, rfl, rfl⟩, step, valid, next,
      by simp only [remaining]; decide, frame, afterClear⟩
  | returned found done => exact .inl ⟨_, found, done⟩

/-- Strong induction assembles real steps, rather than assuming a successful
future suffix. Every terminal witness is discharged by independent Returns.
The historical context of an already resumed or returned worker is retained. -/
theorem complete_cut_selected {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} {count : Nat} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker)
    (cut : Cut client worker state count) (flags rcx r11 : Word) :
    ∃ after, SelectedCompletesWithin count cohort worker client state after := by
  induction count using Nat.strongRecOn generalizing state with
  | ind count ih =>
    rcases cut.progress admitted member published clear flags rcx r11 with
      ⟨actual, selected, done⟩ | ⟨middle, next, action, observation, chosen, step, valid, nextCut,
        bound, frame, afterClear⟩
    · exact ⟨state, [], [], actual, .nil, Nat.zero_le _,
        admitted.returned_sound member selected done, admitted, PrivateFrame.refl _ _⟩
    · have smaller : next < count := Nat.lt_of_lt_of_le (Nat.lt_succ_self next) bound
      have afterPublished : loadDWord middle.suspended.machine.memory cohort.registration.address = .ok 1 := by
        rw [frame.1]
        exact published
      obtain ⟨after, completed⟩ := ih next smaller valid afterPublished afterClear nextCut
      exact ⟨after, (completed.prepend chosen step frame).mono bound⟩

theorem complete_cut {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} {count : Nat} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker)
    (cut : Cut client worker state count) (flags rcx r11 : Word) :
    ∃ after, CompletesWithin count cohort worker client state after := by
  obtain ⟨after, completed⟩ := complete_cut_selected admitted member published clear cut flags rcx r11
  exact ⟨after, completed.forget⟩

/-- Sharp per-point bounds include the stale zero snapshot and the exact
postresume MOV/CMP/backedge/reload sequence. This witness keeps the actual
current context and imposes no fresh clobber premise on already-resumed code. -/
theorem running_completion {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} {point : Point} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker)
    (running : RunningAt client worker state.suspended point) (flags rcx r11 : Word) :
    ∃ after, CompletesWithin (remaining point) cohort worker client state after :=
  complete_cut admitted member published clear (.running running) flags rcx r11

end Completion

/-- The same universal bound with an explicit certificate that every suffix
step selects this loop or its own actual current WAIT0 compare/resume. -/
theorem constructive_completion_selected_with {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker) (flags rcx r11 : Word) :
    ∃ after, SelectedCompletesWithin 14 cohort worker client state after := by
  obtain ⟨count, bound, cut⟩ := Completion.current_cut admitted member clear
  obtain ⟨after, completed⟩ := Completion.complete_cut_selected admitted member published clear cut flags rcx r11
  exact ⟨after, completed.mono bound⟩

/-- Universal postnotification completion across every currently admitted
cut, including stale LOAD0/CMP0/body, entered, ready, already resumed, done and
returned. A queued call is excluded by the actual NoQueuedWait premise.
Only future service resumes choose these clobbers. The fourteen-action bound
is a finite modeled execution bound, with no fairness or timing assumption. -/
theorem constructive_completion_with {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker) (flags rcx r11 : Word) :
    ∃ after, CompletesWithin 14 cohort worker client state after := by
  obtain ⟨after, completed⟩ := constructive_completion_selected_with admitted member published clear flags rcx r11
  exact ⟨after, completed.forget⟩

/-- Existence of an actual completed suffix, without any future execution or
scheduler-success premise. No peer drain is required, and returned peers may
retain their entire original nonempty FIFO. -/
theorem constructive_completion {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker) :
    ∃ after, CompletesWithin 14 cohort worker client state after :=
  constructive_completion_with admitted member published clear 0 0 0

/-- A worker that has already returned completes with the empty actual trace.
Its full historical context is used; no fresh syscall clobber tuple is chosen. -/
theorem returned_completion {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} {actual : TSO.Worker} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (selected : state.suspended.machine.workers[worker]? = some actual)
    (done : actual.returned = true) : CompletesWithin 0 cohort worker client state state :=
  ⟨[], [], actual, .nil, Nat.zero_le _, admitted.returned_sound member selected done,
    admitted, PrivateFrame.refl _ _⟩

end EDSL.OS.Futex.Predicate

#audit_edsl
