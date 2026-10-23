/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import Init

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.Support
universe u v

/-- Computable equality for finite result observations. This instance is
opt-in and adds no semantics or expected values to a regression. -/
scoped instance {ε : Type u} {α : Type v} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .ok left, .ok right => decidable_of_iff (left = right) (by simp)
  | .error left, .error right => decidable_of_iff (left = right) (by simp)
  | .ok _, .error _ => isFalse (by intro impossible; cases impossible)
  | .error _, .ok _ => isFalse (by intro impossible; cases impossible)

end EDSL.Tests.Support
