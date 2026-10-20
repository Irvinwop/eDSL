/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientModel
import EDSL.OS.Futex.ClientResources

namespace EDSL.OS.Futex.Clients
open X86 AddressSpace

/-- Current immutable-cohort admission. No field promises future replay,
control preservation, service completion, or successful physical execution. -/
structure Admitted (cohort : Cohort) (state : State) : Prop where
  static : Static cohort
  runtime : Runtime.Invariant cohort.profile state
  slots : state.suspended.machine.workers.length = cohort.clients.length
  control : Control cohort state.suspended
  registration : state.registration = some cohort.registration
  fixed : ∀ identifier handle, (identifier, handle) ∈ cohort.fixedHandles →
    state.authority.handles identifier = some handle
  discipline : PinDiscipline cohort.pinFloor state
  target : targetSupported cohort.profile.service state.authority cohort.registration.address = true
  payload : ∀ worker grant, cohort.profile.payload worker = some grant → grant.Valid state.authority
  fifo : FIFOAuthorized cohort state
  «protected» : Protected cohort state

theorem Admitted.keeper {cohort : Cohort} {state : State} (admitted : Admitted cohort state) :
    Resources.Valid state.authority cohort.registration :=
  admitted.fixed _ _ admitted.static.keeperFixed

theorem Admitted.pending_family {cohort : Cohort} {state : State} (admitted : Admitted cohort state)
    {worker : Nat} {saved : Suspend.Saved} (pending : state.suspended.pending worker = some saved) :
    CallFamily cohort worker saved.request := by
  obtain ⟨actual, live, running, empty, context⟩ := (admitted.runtime.service.suspended.pending worker saved pending).live
  obtain ⟨client, atClient, control⟩ := admitted.control worker actual live
  cases control with
  | running stage supported context live free fifo => rw [free] at pending; cases pending
  | entered actualSaved atSaved owner family context live empty published =>
    have same := Option.some.inj (atSaved.symm.trans pending)
    subst actualSaved
    exact ⟨client, atClient, family⟩
  | resumed outcome flags rcx r11 caller context live free empty published => rw [free] at pending; cases pending
  | returned outcome flags rcx r11 caller context done free empty published => rw [free] at pending; cases pending
  | peerReturned peer context done free fifo => rw [free] at pending; cases pending

theorem Admitted.stackViews {cohort : Cohort} {state : State} (admitted : Admitted cohort state) :
    StackViews cohort state.suspended := by
  intro worker actual client live atClient
  obtain ⟨_, stack, _, read, _, _, _⟩ := admitted.protected worker client atClient
  have separate : ∀ store ∈ actual.buffer, DWordDisjoint store.address (client.entry.registers .rsp) 8 := by
    intro store queued
    obtain ⟨grant, _, address, ready⟩ := admitted.fifo worker actual live store queued
    rw [← address]
    exact ready.disjoint_hasLoan admitted.runtime.service.authority stack
  exact (StoreBuffer.view_readWord_frame _ _ _ separate).trans read

/-- Protected current code/stack resources survive actual runtime transitions.
The proof uses managed histories and the actual loan registry, rather than a
promise that a future RET or adapter action succeeds. -/
theorem protected_step {cohort : Cohort} {state : State}
    {action : Runtime.Action} {result : State × Runtime.Observation}
    (valid : Runtime.Invariant cohort.profile state) (protection : Protected cohort state)
    (success : Runtime.step cohort.profile state action = .ok result) : Protected cohort result.1 := by
  have afterInv := (Runtime.step_invariant valid success).1
  have memoryFrame := Runtime.step_memory_frame valid success
  have history := (Runtime.step_invariant valid success).2
  have sameLoans := Runtime.step_loans success
  intro worker client atClient
  obtain ⟨codeLoan, stackLoan, code, stack, target, codeSeed, stackSeed⟩ := protection worker client atClient
  have codeFrame := codeLoan.frame valid.service.authority.shared history.borrowing (congrFun sameLoans client.codeLoan)
  have stackFrame := stackLoan.frame valid.service.authority.shared history.borrowing (congrFun sameLoans client.stackLoan)
  refine ⟨codeFrame.1, stackFrame.1, memoryFrame.codeAt code, ?_, target, ?_, ?_⟩
  · rw [← valid.memory] at stack
    rw [← afterInv.memory]
    exact (readWord_congr _ _ _ (agrees_read _ _ _ _ stackFrame.2)).trans stack
  · intro offset bound
    exact (codeFrame.2 offset bound).trans (codeSeed offset bound)
  · intro offset bound
    exact (stackFrame.2 offset bound).trans (stackSeed offset bound)

end EDSL.OS.Futex.Clients
