/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Cohort

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86 AddressSpace

theorem Kind.family_classifies {cohort : Cohort} {worker : Nat} {kind : Kind}
    {request : SyscallRequest} (descriptor : Descriptor cohort worker kind)
    (family : kind.Family request) :
    classify request = .ok kind.operation ∧ request.user.registers .rdi = cohort.registration.address := by
  cases kind with
  | waitLoop client =>
    refine ⟨Family.classifies descriptor.2.1 family, ?_⟩
    exact family.1.rdi.trans descriptor.1
  | legacy client => exact Clients.family_classifies descriptor.1 family

theorem Kind.family_rsp {kind : Kind} {request : SyscallRequest}
    (family : kind.Family request) :
    request.user.registers .rsp = kind.binding.entry.registers .rsp := by
  cases kind with
  | waitLoop client => exact family.1.rsp
  | legacy client =>
    change request.user.registers .rsp = client.entry.registers .rsp
    rw [family.2]
    simp [Clients.Client.request, Clients.Client.callContext, Clients.Stage.context,
      MachineThreads.contextState]

theorem Kind.Control.pending_family {cohort : Cohort} {kind : Kind} {worker : Nat}
    {state : Suspend.State} {actual : TSO.Worker} {saved : Suspend.Saved}
    (control : Kind.Control cohort kind worker state actual)
    (pending : state.pending worker = some saved) : kind.Family saved.request := by
  cases kind with
  | waitLoop client =>
    cases control with
    | running _ _ _ _ free _ => rw [free] at pending; cases pending
    | entered captured found _ family _ _ _ =>
      cases Option.some.inj (found.symm.trans pending)
      exact family
    | returned _ _ _ _ _ _ free _ => rw [free] at pending; cases pending
  | legacy client =>
    cases control with
    | running _ _ _ _ free _ => rw [free] at pending; cases pending
    | entered captured found _ family _ _ _ _ =>
      cases Option.some.inj (found.symm.trans pending)
      exact family
    | resumed _ _ _ _ _ _ _ free _ _ => rw [free] at pending; cases pending
    | returned _ _ _ _ _ _ _ free _ _ => rw [free] at pending; cases pending
    | peerReturned _ _ _ free _ => rw [free] at pending; cases pending

theorem Admitted.pending_family {cohort : Cohort} {state : Futex.State}
    (admitted : Admitted cohort state) {worker : Nat} {saved : Suspend.Saved}
    (pending : state.suspended.pending worker = some saved) : CallFamily cohort worker saved.request := by
  obtain ⟨actual, found, _, _, _⟩ :=
    (admitted.runtime.service.suspended.pending worker saved pending).live
  obtain ⟨kind, member, control⟩ := admitted.control worker actual found
  exact ⟨kind, member, Kind.Control.pending_family control pending⟩

/-- Actual FIFOs inherit their grants from current concrete control. Returned
producer entries are covered, while a loop has no ordinary store entry. -/
theorem Control.fifo_authorized {cohort : Cohort} {state : Futex.State}
    (control : Control cohort state.suspended) (static : Static cohort)
    (payload : ∀ worker grant, cohort.profile.payload worker = some grant → grant.Valid state.authority) :
    FIFOAuthorized cohort state := by
  intro worker actual found store queued
  obtain ⟨kind, member, controlled⟩ := control worker actual found
  cases kind with
  | waitLoop client =>
    have empty := LoopControl.fifo_empty controlled
    simp [empty] at queued
  | legacy client =>
    obtain ⟨role, same⟩ := Clients.WorkerControl.queued_store controlled queued
    obtain ⟨_, _, _, _, description⟩ := (static.descriptors worker (.legacy client) member).1
    have grantAt : ∃ grant, cohort.profile.payload worker = some grant ∧ grant.address = client.store.address := by
      rcases role with publisher | peer
      · rw [publisher] at description
        exact description.1
      · rw [peer] at description
        exact description.1
    obtain ⟨grant, grantFound, address⟩ := grantAt
    exact ⟨grant, grantFound, by rw [same]; exact address, payload worker grant grantFound⟩

/-- All workers retain the real stack view obtained through their actual
buffer, without requiring any other worker or returned peer to be quiescent. -/
def StackViews (cohort : Cohort) (state : Suspend.State) : Prop :=
  ∀ (worker : Nat) (actual : TSO.Worker) (kind : Kind),
    state.machine.workers[worker]? = some actual → cohort.clients[worker]? = some kind →
    readWord (StoreBuffer.view state.machine.memory actual.buffer) (kind.binding.entry.registers .rsp) =
      .ok kind.binding.returnTarget

theorem Admitted.stackViews {cohort : Cohort} {state : Futex.State}
    (admitted : Admitted cohort state) : StackViews cohort state.suspended := by
  intro worker actual kind found member
  apply (admitted.protected worker kind member).stackView admitted.runtime.service.authority
  intro store queued
  obtain ⟨grant, _, address, authorized⟩ := admitted.fifo worker actual found store queued
  exact ⟨grant, authorized, address⟩

theorem protected_step {cohort : Cohort} {state : Futex.State}
    {action : Runtime.Action} {result : Futex.State × Runtime.Observation}
    (runtime : Runtime.Invariant cohort.profile state) (protection : Protected cohort state)
    (actual : Runtime.step cohort.profile state action = .ok result) : Protected cohort result.1 := by
  intro worker kind member
  exact (protection worker kind member).step runtime actual

/-- The resource part of admission follows from actual runtime histories.
Current post-control and word facts are separate proof conclusions to be
established by the concrete instruction/service preservation theorem. -/
theorem Admitted.advance {cohort : Cohort} {state : Futex.State}
    {action : Runtime.Action} {result : Futex.State × Runtime.Observation}
    (admitted : Admitted cohort state)
    (actual : Runtime.step cohort.profile state action = .ok result)
    (control : Control cohort result.1.suspended) (word : WordDomain cohort result.1) :
    Admitted cohort result.1 := by
  have invariant := (Runtime.step_invariant admitted.runtime actual).1
  have resources := Runtime.step_discipline admitted.discipline actual
  have frame := Runtime.step_memory_frame admitted.runtime actual
  have grants : ∀ worker grant, cohort.profile.payload worker = some grant → grant.Valid result.1.authority := by
    intro worker grant found
    exact Clients.runtime_step_grant admitted.runtime (admitted.payload worker grant found) actual
  refine ⟨admitted.static, invariant, (Runtime.step_worker_count actual).trans admitted.slots,
    control, resources.2.2.trans admitted.registration, ?_, resources.1, ?_, grants,
    control.fifo_authorized admitted.static grants,
    protected_step admitted.runtime admitted.protected actual, word⟩
  · intro identifier handle member
    exact (resources.2.1 identifier (admitted.static.fixedBelow identifier handle member)).trans
      (admitted.fixed identifier handle member)
  · simpa only [targetSupported, invariant.memory, admitted.runtime.memory,
      TSO.dataOnly, frame.executable] using admitted.target

end EDSL.OS.Futex.Predicate

#audit_edsl
