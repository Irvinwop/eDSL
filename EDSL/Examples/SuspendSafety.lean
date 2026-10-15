/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Suspend
import EDSL.OS.Suspend.Composition

namespace EDSL.Examples.Suspend
open X86 OS

/-- This byte-bound pending call admits an infinite parked trace; it needs no
invented service completion or fairness premise. -/
def parked_call (replacement : BitVec 32) : OS.Suspend.InfiniteTrace (entered replacement).1 :=
  OS.Suspend.parked_forever ((initial_valid replacement).issue (entered_ok replacement))
    (identifier := 0) (saved := ⟨0, 0, entryRequest⟩) (by rfl)

/-- The concrete actual call cannot be completed a second time after any
successful continuation, including later invocations and arbitrary peers. -/
theorem consumed_call_never_resumes (replacement : BitVec 32) (raw flags rcx r11 : Word)
    {actions : List OS.Suspend.Action} {result : OS.Suspend.State × List OS.Suspend.Observation}
    (success : OS.Suspend.schedule (resumed replacement raw flags rcx r11) actions = .ok result)
    (query : Nat) (value choices savedRcx savedR11 : Word) :
    ¬ ∃ after, OS.Suspend.resume result.1 query 0 value choices savedRcx savedR11 = .ok after :=
  OS.Suspend.consumed_identity_never_resumes (exchanged_valid replacement)
    (resumed_ok replacement raw flags rcx r11) success query value choices savedRcx savedR11

end EDSL.Examples.Suspend
