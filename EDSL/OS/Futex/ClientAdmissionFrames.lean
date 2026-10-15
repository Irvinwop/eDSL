/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientAdmission
import EDSL.OS.Futex.ClientFIFO

namespace EDSL.OS.Futex.Clients
open X86

/-- The resource half of current admission is preserved by actual adapter
steps. The remaining control conclusion is supplied by the independently
proved concrete control transition, not stored as an admission callback. -/
theorem Admitted.advance {cohort : Cohort} {state : State}
    {action : Runtime.Action} {result : State × Runtime.Observation}
    (admitted : Admitted cohort state) (success : Runtime.step cohort.profile state action = .ok result)
    (control : Control cohort result.1.suspended) : Admitted cohort result.1 := by
  have invariant := (Runtime.step_invariant admitted.runtime success).1
  have resources := Runtime.step_discipline admitted.discipline success
  have frame := Runtime.step_memory_frame admitted.runtime success
  have grants : ∀ worker grant, cohort.profile.payload worker = some grant → grant.Valid result.1.authority := by
    intro worker grant found
    exact runtime_step_grant admitted.runtime (admitted.payload worker grant found) success
  refine ⟨admitted.static, invariant, (Runtime.step_worker_count success).trans admitted.slots,
    control, resources.2.2.trans admitted.registration, ?_, resources.1, ?_, grants,
    control.fifo_authorized admitted.static grants, protected_step admitted.runtime admitted.protected success⟩
  · intro identifier handle member
    exact (resources.2.1 identifier (admitted.static.fixedBelow identifier handle member)).trans
      (admitted.fixed identifier handle member)
  · simpa only [targetSupported, invariant.memory, admitted.runtime.memory,
      TSO.dataOnly, frame.executable] using admitted.target

end EDSL.OS.Futex.Clients
