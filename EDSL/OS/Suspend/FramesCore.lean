/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Suspend.Invariant
import EDSL.OS.Suspend.Trace

namespace EDSL.OS.Suspend
open X86

/-- Capturing an actual request retains the complete current RAM. The saved
request's historical memory is not installed into the machine. -/
theorem capture_memory (state : State) (identifier : Nat) (request : SyscallRequest) :
    (capture state identifier request).machine.memory = state.machine.memory := rfl

/-- Resumption retains every current byte and both permission functions.
This is independent of the saved request's entry-memory contents. -/
theorem resume_memory_eq {state after : State} {identifier invocation : Nat}
    {raw flags rcx r11 : Word}
    (success : resume state identifier invocation raw flags rcx r11 = .ok after) :
    after.machine.memory = state.machine.memory :=
  resume_memory success

theorem resume_memory_frame {state after : State} {identifier invocation : Nat}
    {raw flags rcx r11 : Word}
    (success : resume state identifier invocation raw flags rcx r11 = .ok after) :
    TSO.MemoryFrame state.machine.memory after.machine.memory := by
  rw [resume_memory_eq success]
  exact .refl _

/-- Only drains need buffer validity for this memory frame. No pending-call
condition, peer queue emptiness, or future transition is assumed. -/
theorem step_memory_frame_of_buffers {state : State} {action : Action}
    {result : State × Observation} (valid : TSO.BuffersValid state.machine)
    (success : step state action = .ok result) :
    TSO.MemoryFrame state.machine.memory result.1.machine.memory :=
  step_memory_frame valid success

/-- Actual entry leaves the whole current memory untouched. -/
theorem entered_memory_eq {state after : State} {identifier invocation : Nat}
    (success : issue state identifier = .ok (after, .entered identifier invocation)) :
    after.machine.memory = state.machine.memory := by
  cases issue_effect _ _ _ success with
  | entered => rfl

/-- Selecting a parked caller is a full memory stutter. -/
theorem parked_memory_eq {state after : State} {identifier invocation : Nat}
    (success : issue state identifier = .ok (after, .parked identifier invocation)) :
    after.machine.memory = state.machine.memory := by
  cases issue_effect _ _ _ success with
  | parked => rfl

/-- The entry snapshot is bound to actual current RAM using the request
produced by actual SYSCALL execution, rather than an arbitrary saved image. -/
theorem entered_saved_memory {state after : State} {identifier invocation : Nat}
    (success : issue state identifier = .ok (after, .entered identifier invocation)) :
    ∃ saved, after.pending identifier = some saved ∧ saved.identifier = invocation ∧
      saved.request.user.memory = state.machine.memory ∧
      after.machine.memory = state.machine.memory := by
  cases issue_effect _ _ _ success with
  | @entered worker request _ _ _ _ _ _ _ user _ =>
    refine ⟨⟨state.nextCall, identifier, request⟩, ?_, rfl, ?_, rfl⟩
    · simp [capture]
    · rw [user]
      rfl

/-- Entry and parked selections preserve complete current executable images. -/
theorem entered_code {state after : State} {identifier invocation : Nat}
    {base : Word} {bytes : List Byte} (code : CodeAt state.machine.memory base bytes)
    (success : issue state identifier = .ok (after, .entered identifier invocation)) :
    CodeAt after.machine.memory base bytes := by
  rw [entered_memory_eq success]
  exact code

theorem parked_code {state after : State} {identifier invocation : Nat}
    {base : Word} {bytes : List Byte} (code : CodeAt state.machine.memory base bytes)
    (success : issue state identifier = .ok (after, .parked identifier invocation)) :
    CodeAt after.machine.memory base bytes := by
  rw [parked_memory_eq success]
  exact code

/-- Resume takes code evidence on current RAM, regardless of the entry image. -/
theorem resume_code {state after : State} {identifier invocation : Nat}
    {raw flags rcx r11 base : Word} {bytes : List Byte}
    (code : CodeAt state.machine.memory base bytes)
    (success : resume state identifier invocation raw flags rcx r11 = .ok after) :
    CodeAt after.machine.memory base bytes := by
  rw [resume_memory_eq success]
  exact code

end EDSL.OS.Suspend

#audit_edsl
