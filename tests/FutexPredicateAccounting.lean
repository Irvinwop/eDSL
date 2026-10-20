/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.FutexPredicate
import EDSL.FutexPredicateCertificate

set_option warningAsError true

namespace EDSL.Tests.FutexPredicateAccounting
open X86 OS OS.Futex OS.Futex.Predicate Examples.FutexPredicate
open Examples.Futex (checked checked_ok)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem prepared_valid : Predicate.Admitted cohort prepared.1 :=
  initial_admitted.schedule (result := prepared) (checked_ok _ _)

private theorem published_valid : Predicate.Admitted cohort lateWoken.1 :=
  prepared_valid.schedule (result := lateWoken) (checked_ok _ _)

/-- This current LOAD is reached after the real publisher has retired XCHG
and completed its empty WAKE. The loop has not issued or acquired a call pin. -/
private theorem current_load : Completion.RunningAt waiter 0 lateWoken.1.suspended .load := by
  refine ⟨_, rfl, Running.initial waiter, rfl, rfl, rfl⟩

private theorem artifact :
    EDSL.FutexPredicateCertificate.Specification Predicate.bytes cohort lateWoken.1 0 waiter :=
  EDSL.FutexPredicateCertificate.sound _ (by decide) published_valid rfl
    (published_valid.currentCode 0 (.waitLoop waiter) rfl)

/-- Any accepted returning extension of this genuinely reached state obeys
the lower bound, without supplying a desired future suffix as a premise. -/
theorem every_return_costs_four {after : Futex.State} {actual : TSO.Worker}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (trace : Runtime.Trace profile lateWoken.1 actions observations after)
    (returned : Predicate.Returns waiter 65536 after.suspended 0 actual) :
    4 ≤ Accounting.retiredInstructions 0 observations :=
  artifact.fastpath_lower_bound rfl current_load trace returned

/-- Attainment retains the same literal artifact and whole RAM/peer frames.
It constructs execution; no observed returning trace is an input. -/
theorem four_is_attained : ∃ after actual,
    Runtime.Trace profile lateWoken.1 (Accounting.fastActions 0) (Accounting.fastObservations 0) after ∧
    Accounting.retiredInstructions 0 (Accounting.fastObservations 0) = 4 ∧
    Predicate.Returns waiter 65536 after.suspended 0 actual ∧
    EDSL.FutexPredicateCertificate.Specification Predicate.bytes cohort after 0 waiter ∧
    PrivateFrame 0 lateWoken.1.suspended after.suspended :=
  artifact.fastpath_attains rfl current_load

/-- The actual late-W1 execution retires LOAD/CMP/JNZ/RET. Its result is
checked through preserved admission, rather than installing a final worker. -/
theorem observed_fastpath : ∃ actual,
    Predicate.Returns waiter 65536 lateReturned.1.suspended 0 actual ∧
    Accounting.retiredInstructions 0 lateReturned.2 = 4 := by
  have valid := published_valid.schedule (result := lateReturned) (checked_ok _ _)
  let actual := (lateReturned.1.suspended.machine.workers[0]?).get (by rfl)
  exact ⟨actual, valid.returned_sound rfl (by rfl) (by rfl), rfl⟩

/-- Actual SYSCALL capture counts once. A parked selection and a service
comparison do not retire a second user instruction. This distinguishes the
metric from Runtime-action or scheduler-selection counts. -/
theorem syscall_and_park_costs :
    Accounting.retiredInstructions 0 entered.2 = 6 ∧
    Accounting.retiredInstructions 0
      [.physical ((checked (Suspend.issue queued.1.suspended 0) (by rfl)).2)] = 0 ∧
    Accounting.retiredInstructions 0 queued.2 = 0 := by
  exact ⟨rfl, rfl, rfl⟩

end EDSL.Tests.FutexPredicateAccounting

#audit_edsl
