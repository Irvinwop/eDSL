/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGTransport
import EDSL.X86.Sequential.MachineChoices

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.Sequential.CFG

/-- Every admitted vector execution returns or continues with complete memory
preserved. Vector-only instruction families discharge the shared register-effect
interface; clients do not repeat instruction-specific proof cases. -/
theorem executeWith_memory {initial : State} {instruction : Instruction}
    {choices : FlagChoices} {observation : Observation}
    (allowed : readOnly instruction = true)
    (success : executeWith initial instruction choices = .ok observation) :
    match observation.result with
    | .next after | .returned after => after.memory = initial.memory
    | .atomic _ _ | .syscall _ => False := by
  rcases executeWith_effect initial instruction choices with single | ⟨after, actual, _, memory⟩
  · rw [executeWith_eq_execute initial instruction choices single] at success
    obtain ⟨after, next | ⟨returned, _⟩⟩ := execute_result allowed success
    · rw [next]
      exact execute_next_memory allowed success next
    · rw [returned]
      exact execute_returned_memory allowed success returned
  · rw [actual] at success
    cases success
    exact memory

theorem executeWith_next_memory {initial final : State} {instruction : Instruction}
    {choices : FlagChoices} {observation : Observation}
    (allowed : readOnly instruction = true)
    (success : executeWith initial instruction choices = .ok observation)
    (next : observation.result = .next final) : final.memory = initial.memory := by
  have framed := executeWith_memory allowed success
  rwa [next] at framed

end EDSL.X86.Sequential.CFG
