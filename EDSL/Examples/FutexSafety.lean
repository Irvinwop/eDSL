/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Futex
import EDSL.OS.Futex.LoanFrames

namespace EDSL.Examples.Futex
open X86 OS OS.AddressSpace

/-- The actual adopted/borrowed initial cohort supplies a nonempty instance of
both the generic current-call invariant and entire-RAM coupling. -/
theorem initial_invariant : OS.Futex.Runtime.Invariant profile initial :=
  ⟨initial_valid, initial_memory_coupled⟩

/-- Every successful mixed physical/service prefix of this exact cohort keeps
its live call bindings, unique pins and queue eligibility, with exact RAM and
managed authority histories. This does not assert every physical prefix has a
successful adapter replay or that any wait eventually completes. -/
theorem every_prefix {actions : List OS.Futex.Runtime.Action}
    {result : OS.Futex.State × List OS.Futex.Runtime.Observation}
    (success : OS.Futex.Runtime.schedule profile initial actions = .ok result) :
    OS.Futex.Runtime.Invariant profile result.1 ∧ Atomics.History initial.authority result.1.authority :=
  OS.Futex.Runtime.schedule_invariant initial_invariant success

/-- Complete eight-byte return-stack authority survives every accepted active
prefix. A word reservation alone would not establish this stack frame. -/
theorem waiter_stack_frame {actions : List OS.Futex.Runtime.Action}
    {result : OS.Futex.State × List OS.Futex.Runtime.Observation}
    (success : OS.Futex.Runtime.schedule profile initial actions = .ok result) :
    Threads.HasLoan result.1.authority.shared 9 1 ⟨32768, 8⟩ ∧
      AgreesOn result.1.authority.shared.resources.space initial.authority.shared.resources.space 32768 8 := by
  have loan : Threads.HasLoan initial.authority.shared 9 1 ⟨32768, 8⟩ :=
    ⟨_, rfl, rfl, rfl⟩
  exact OS.Futex.Runtime.loan_frame initial_invariant success loan

/-- The exact registered word satisfies the configured complete userspace
interval and non-executable storage checks before any syscall is captured. -/
theorem initial_target_supported :
    OS.Futex.targetSupported profile.service initial.authority registration.address = true := by rfl

end EDSL.Examples.Futex
