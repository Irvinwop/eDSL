/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientNotification.Continuation.Contract

set_option warningAsError true

namespace EDSL.OS.Futex.Clients.Notification
open X86

/-- At the exact SYSCALL location the actual fresh captured invocation, pin,
and typed phase are recovered from the lifted state. No future service success
is supplied. All private resume clobbers remain caller-chosen. -/
theorem operation_finishes {cohort : Cohort} {state : State} {worker : Nat}
    {client : Client} {expected : BitVec 32} (policy : Policy cohort worker expected)
    (admitted : Admitted cohort state) (member : cohort.clients[worker]? = some client)
    (role : client.role = .wait expected)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker)
    (running : RunningAt client worker state.suspended .operation) (flags rcx r11 : Word) :
    ∃ after, FinishesWithin 4 cohort worker expected flags rcx r11 state after ∧
      Admitted cohort after := by
  obtain ⟨captured, saved, first, valid, pending, _, _, _, frame⟩ :=
    running_wait_capture_enabled admitted member role running
  obtain ⟨after, finished, finalValid⟩ := pending_worker_finishes policy valid
    (published_word_step admitted published first)
    (runtime_preserves policy admitted published clear first) pending flags rcx r11
  exact ⟨after, finished.prepend first frame, finalValid⟩

/-- From the second MOV, one actual instruction and the enabled operation
suffix take at most five runtime transitions. -/
theorem number_finishes {cohort : Cohort} {state : State} {worker : Nat}
    {client : Client} {expected : BitVec 32} (policy : Policy cohort worker expected)
    (admitted : Admitted cohort state) (member : cohort.clients[worker]? = some client)
    (role : client.role = .wait expected)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker)
    (running : RunningAt client worker state.suspended .number) (flags rcx r11 : Word) :
    ∃ after, FinishesWithin 5 cohort worker expected flags rcx r11 state after ∧
      Admitted cohort after := by
  obtain ⟨moved, first, valid, next, frame⟩ := running_mov_enabled admitted member
    (by simp [Stage.Valid, role] : Stage.number.Valid client.role)
    (by simp [Stage.instruction, role] : Stage.number.instruction client.role = .mov32 .rsi 128) running
  have operation : RunningAt client worker moved.suspended .operation := by
    simpa only [Stage.next] using next
  obtain ⟨after, finished, finalValid⟩ := operation_finishes policy valid member role
    (published_word_step admitted published first)
    (runtime_preserves policy admitted published clear first) operation flags rcx r11
  exact ⟨after, finished.prepend first frame, finalValid⟩

/-- The worst unentered WAIT suffix executes two MOVs, SYSCALL, mismatch
comparison, typed resume and RET: six actual runtime transitions. -/
theorem start_finishes {cohort : Cohort} {state : State} {worker : Nat}
    {client : Client} {expected : BitVec 32} (policy : Policy cohort worker expected)
    (admitted : Admitted cohort state) (member : cohort.clients[worker]? = some client)
    (role : client.role = .wait expected)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker)
    (running : RunningAt client worker state.suspended .start) (flags rcx r11 : Word) :
    ∃ after, FinishesWithin 6 cohort worker expected flags rcx r11 state after ∧
      Admitted cohort after := by
  obtain ⟨moved, first, valid, next, frame⟩ := running_mov_enabled admitted member
    (by simp [Stage.Valid, role] : Stage.start.Valid client.role)
    (by simp [Stage.instruction, role] : Stage.start.instruction client.role = .mov32 .rax 202) running
  have number : RunningAt client worker moved.suspended .number := by
    simpa only [Stage.next, role] using next
  obtain ⟨after, finished, finalValid⟩ := number_finishes policy valid member role
    (published_word_step admitted published first)
    (runtime_preserves policy admitted published clear first) number flags rcx r11
  exact ⟨after, finished.prepend first frame, finalValid⟩

/-- All supported pre-SYSCALL WAIT locations are covered. Impossible producer
or peer stages are excluded by current control, not by a new scope premise. -/
theorem running_finishes {cohort : Cohort} {state : State} {worker : Nat}
    {client : Client} {expected : BitVec 32} {stage : Stage}
    (policy : Policy cohort worker expected) (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some client) (role : client.role = .wait expected)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker)
    (supported : stage.Valid client.role) (running : RunningAt client worker state.suspended stage)
    (flags rcx r11 : Word) :
    ∃ after, FinishesWithin 6 cohort worker expected flags rcx r11 state after ∧
      Admitted cohort after := by
  cases stage with
  | start => exact start_finishes policy admitted member role published clear running flags rcx r11
  | number =>
    obtain ⟨after, finished, valid⟩ := number_finishes policy admitted member role published clear running flags rcx r11
    exact ⟨after, finished.mono (by decide), valid⟩
  | operation =>
    obtain ⟨after, finished, valid⟩ := operation_finishes policy admitted member role published clear running flags rcx r11
    exact ⟨after, finished.mono (by decide), valid⟩
  | payload | stored | exchange | exchanged _ | count => simp [Stage.Valid, role] at supported

end EDSL.OS.Futex.Clients.Notification
