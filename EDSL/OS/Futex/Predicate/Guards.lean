/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Admission
import EDSL.OS.Futex.Predicate.Decode
import EDSL.OS.Futex.ClientControlProgress
import EDSL.OS.Futex.ClientLiftCore

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86 AddressSpace

/-- A live keeper's current well-formed handle retains physical alignment and
complete canonical word addressability. A saved pointer alone is insufficient. -/
theorem Admitted.word_aligned {cohort : Cohort} {state : Futex.State}
    (admitted : Admitted cohort state) : atomicAddressable cohort.registration.address = true := by
  obtain ⟨allocation, allocated, owner, epoch, contains, aligned, writable⟩ :=
    (admitted.runtime.service.authority.handles _ _ admitted.keeper).2
  exact aligned

/-- Real load/branch/return guards follow from present resources and explicit
static code targets. No field assumes that a future instruction succeeds. -/
theorem Admitted.loop_ready {cohort : Cohort} {state : Futex.State} {worker : Nat} {client : Client}
    (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client)) (point : Point) :
    Ready client point state.suspended.machine.memory := by
  have descriptor := admitted.static.descriptors worker (.waitLoop client) member
  have targets := admitted.static.loopTargets worker client member
  have protection := admitted.protected worker (.waitLoop client) member
  cases point with
  | load =>
    refine ⟨?_, ?_⟩
    · rw [descriptor.1]
      exact admitted.word_aligned
    · rcases admitted.word with zero | one
      · exact ⟨0, by rw [descriptor.1]; exact zero⟩
      · exact ⟨1, by rw [descriptor.1]; exact one⟩
  | branch observed => exact fun _ => targets.2
  | retryBranch => exact targets.1
  | done observed => exact ⟨protection.2.2.2.1, protection.2.2.2.2.1⟩
  | compare _ | number | operation | syscall | resumed _ | retryCompare => trivial

/-- An actual current SYSCALL is classified by its selected control and exact
present code. The loop carries its real historical private context. -/
theorem Control.current_syscall_family {cohort : Cohort} {state : Futex.State}
    (control : Control cohort state.suspended) (protection : Protected cohort state)
    {worker : Nat} {actual : TSO.Worker}
    (found : state.suspended.machine.workers[worker]? = some actual)
    (live : actual.returned = false) (free : state.suspended.pending worker = none)
    (decoded : decodeAt (TSO.sharedState state.suspended.machine actual) = .ok .syscall) :
    CallFamily cohort worker (Clients.LiftCore.entryRequest state.suspended actual) := by
  obtain ⟨kind, member, controlled⟩ := control worker actual found
  refine ⟨kind, member, ?_⟩
  have code := (protection worker kind member).2.2.1
  cases kind with
  | waitLoop client =>
    cases controlled with
    | running point current _ _ _ _ =>
      have expected := decode_point current code
      have same : point.instruction = .syscall := Except.ok.inj (expected.symm.trans decoded)
      have atSyscall := Point.syscall_only same
      subst point
      exact ⟨current, rfl⟩
    | entered saved pending _ _ _ _ _ => simp [free] at pending
    | returned _ _ _ _ _ done _ _ => simp [live] at done
  | legacy client =>
    cases controlled with
    | running stage supported context _ _ _ =>
      have expected := Clients.decode_stage client stage state.suspended.machine.memory supported code
      rw [TSO.sharedState, context] at decoded
      have same := Except.ok.inj (expected.symm.trans decoded)
      obtain ⟨caller, callContext⟩ := Clients.stage_syscall supported same
      refine ⟨caller, ?_⟩
      simp only [Clients.LiftCore.entryRequest, Clients.Client.request, TSO.sharedState,
        context, callContext, MachineThreads.contextState]
    | entered saved pending _ _ _ _ _ _ => simp [free] at pending
    | resumed outcome flags rcx r11 caller context _ _ _ _ =>
      have expected := Clients.decode_resumed client state.suspended.machine.memory
        outcome.raw flags rcx r11 caller code
      rw [TSO.sharedState, context] at decoded
      cases expected.symm.trans decoded
    | returned _ _ _ _ _ _ done _ _ _ => simp [live] at done
    | peerReturned _ _ done _ _ => simp [live] at done

/-- Current keeper, target and actual decoded call family enable generic
fresh capture; no successful future capture is assumed in admission. -/
theorem entry_support {cohort : Cohort} {state : Futex.State}
    (admitted : Admitted cohort state) : Clients.LiftCore.EntrySupport cohort.profile state := by
  refine ⟨cohort.registration, admitted.registration, admitted.keeper, admitted.target, ?_⟩
  intro worker actual found live free decoded
  obtain ⟨kind, member, family⟩ :=
    Control.current_syscall_family admitted.control admitted.protected found live free decoded
  exact ⟨kind.operation, Kind.family_classifies (admitted.static.descriptors worker kind member) family⟩

/-- A returned producer's current FIFO head carries the same grant as any
other head. This guard concerns the observed effect, not future replay. -/
theorem drain_ready {cohort : Cohort} {state : Futex.State} {suspended : Suspend.State}
    {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (suspended, observation)) :
    Physical.Ready cohort.profile state.authority observation := by
  obtain ⟨machine, observed, drained, same⟩ := Suspend.drain_ok _ _ _ actual
  obtain ⟨selected, head, tail, memory, found, buffer, committed, installed⟩ := TSO.drain_ok _ _ _ drained
  have observedEq := congrArg Prod.snd same
  have drainedEq := congrArg Prod.snd installed
  dsimp only at observedEq drainedEq
  rw [observedEq, drainedEq]
  exact admitted.fifo worker selected found head (by simp [buffer])

/-- Present FIFO authority positively enables exact managed drain replay. -/
theorem drain_enabled {cohort : Cohort} {state : Futex.State} {suspended : Suspend.State}
    {worker : Nat} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (actual : Suspend.drain state.suspended worker = .ok (suspended, observation)) :
    ∃ after, Physical.drain cohort.profile state worker = .ok (after, observation) ∧
      after.suspended = suspended ∧ Runtime.Invariant cohort.profile after ∧
      Atomics.History state.authority after.authority :=
  Clients.LiftCore.drain_enabled admitted.runtime (drain_ready admitted actual) actual

end EDSL.OS.Futex.Predicate

#audit_edsl
