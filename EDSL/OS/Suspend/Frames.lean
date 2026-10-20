/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Suspend.FramesCore
import EDSL.OS.Suspend.Invariant

/-! Memory framing for actual scheduler transitions. Full current RAM is
retained at resume, including peer changes since entry. Ordinary data values
may change during a prefix; these theorems preserve executable bytes and memory
domains and permissions. Suspend carries no loans or ownership authorization. -/

namespace EDSL.OS.Suspend
open X86

theorem WellFormed.step_memory_frame {state : State} {action : Action} {result : State × Observation}
    (valid : WellFormed state) (success : Suspend.step state action = .ok result) :
    TSO.MemoryFrame state.machine.memory result.1.machine.memory :=
  step_memory_frame_of_buffers valid.buffers success

/-- The memory guarantee needs only current valid buffers, including when
pending records do not satisfy the stronger lifecycle invariant. -/
theorem schedule_memory_frame_of_buffers {state : State} {actions : List Action}
    {result : State × List Observation} (valid : TSO.BuffersValid state.machine)
    (success : schedule state actions = .ok result) :
    TSO.MemoryFrame state.machine.memory result.1.machine.memory := by
  induction actions generalizing state result with
  | nil =>
    simp only [schedule, Except.ok.injEq] at success
    cases success
    exact .refl _
  | cons action rest ih =>
    obtain ⟨head, tail, first, following, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact (step_memory_frame_of_buffers valid first).trans
      (ih (result := tail) (buffersValid_step valid first) following)

/-- Every actual finite prefix has this frame, including prefixes ending
while a caller is parked. Successful completion of a later suffix is not needed.
Data contents may change through peers' valid stores and locked operations. -/
theorem schedule_memory_frame {state : State} {actions : List Action}
    {result : State × List Observation} (valid : WellFormed state)
    (success : schedule state actions = .ok result) :
    TSO.MemoryFrame state.machine.memory result.1.machine.memory :=
  schedule_memory_frame_of_buffers valid.buffers success

theorem Trace.memory_frame {before after : State} {actions : List Action}
    {observations : List Observation} (trace : Trace before actions observations after)
    (valid : WellFormed before) : TSO.MemoryFrame before.machine.memory after.machine.memory :=
  schedule_memory_frame valid trace.schedule

theorem step_code {state : State} {action : Action} {result : State × Observation}
    {base : Word} {bytes : List Byte} (valid : WellFormed state)
    (code : CodeAt state.machine.memory base bytes)
    (success : step state action = .ok result) : CodeAt result.1.machine.memory base bytes :=
  (valid.step_memory_frame success).codeAt code

/-- All bytes of any supplied executable image survive the actual prefix;
the image need not describe the selected worker or an expected program. -/
theorem schedule_code {state : State} {actions : List Action}
    {result : State × List Observation} {base : Word} {bytes : List Byte}
    (valid : WellFormed state) (code : CodeAt state.machine.memory base bytes)
    (success : schedule state actions = .ok result) : CodeAt result.1.machine.memory base bytes :=
  (schedule_memory_frame valid success).codeAt code

theorem Trace.code {before after : State} {actions : List Action}
    {observations : List Observation} {base : Word} {bytes : List Byte}
    (trace : Trace before actions observations after) (valid : WellFormed before)
    (code : CodeAt before.machine.memory base bytes) : CodeAt after.machine.memory base bytes :=
  (trace.memory_frame valid).codeAt code

/-- An actual captured entry image has a frame through any actual following
prefix. The full entry/current memory equality is derived only at capture;
subsequent ordinary data values need not remain equal. -/
theorem entered_schedule_memory_frame {state captured : State} {identifier invocation : Nat}
    {actions : List Action} {result : State × List Observation} (valid : WellFormed state)
    (entered : issue state identifier = .ok (captured, .entered identifier invocation))
    (following : schedule captured actions = .ok result) :
    ∃ saved, captured.pending identifier = some saved ∧ saved.identifier = invocation ∧
      saved.request.user.memory = state.machine.memory ∧
      TSO.MemoryFrame saved.request.user.memory result.1.machine.memory := by
  obtain ⟨saved, pending, invocationEq, entry, current⟩ := entered_saved_memory entered
  refine ⟨saved, pending, invocationEq, entry, ?_⟩
  rw [entry, ← current]
  exact schedule_memory_frame (valid.issue entered) following

theorem entered_schedule_code {state captured : State} {identifier invocation : Nat}
    {actions : List Action} {result : State × List Observation} {base : Word} {bytes : List Byte}
    (valid : WellFormed state) (code : CodeAt state.machine.memory base bytes)
    (entered : issue state identifier = .ok (captured, .entered identifier invocation))
    (following : schedule captured actions = .ok result) :
    CodeAt result.1.machine.memory base bytes := by
  obtain ⟨saved, _, _, entry, frame⟩ := entered_schedule_memory_frame valid entered following
  exact frame.codeAt (by rw [entry]; exact code)

/-- Current executable-byte evidence survives a real prefix and its actual
resumption. Peers may have nonempty FIFOs and may change ordinary data. -/
theorem schedule_resume_code {state after : State} {actions : List Action}
    {result : State × List Observation} {identifier invocation : Nat}
    {raw flags rcx r11 base : Word} {bytes : List Byte}
    (valid : WellFormed state) (code : CodeAt state.machine.memory base bytes)
    (scheduled : schedule state actions = .ok result)
    (resumed : resume result.1 identifier invocation raw flags rcx r11 = .ok after) :
    after.machine.memory = result.1.machine.memory ∧ CodeAt after.machine.memory base bytes :=
  ⟨resume_memory_eq resumed, resume_code (schedule_code valid code scheduled) resumed⟩

end EDSL.OS.Suspend

#audit_edsl
