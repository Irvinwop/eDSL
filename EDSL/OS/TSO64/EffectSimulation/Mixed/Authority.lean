/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.Idle
import EDSL.OS.TSO64.Stability

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Authority transport for generated mixed blocks. Metadata and permissions
remain stable along native origins even when shared byte values change.
The exact first matching atomic selector therefore survives idle interference
at a fixed address and the subject's retained resources. This does not assert
that the selected cell's current word, pending FIFO or reconstructed RAM is
unchanged.
-/

namespace EDSL.OS.TSO64
open X86

/-- Retain the complete ordered selector, rather than just grant membership. -/
theorem Stable.atomicFor {before after : World} (frame : Stable before after)
    (resources : Resources) (address : Word) :
    TSO64.atomicFor after resources address = TSO64.atomicFor before resources address := by
  simp only [TSO64.atomicFor, frame.authorize]

namespace EffectSimulation

/-- All origins preserve metadata and permissions under the same family. -/
theorem OriginTrace.stable {profile : Profile} {family : RMWFamily}
    {initial final : State} {history : Log}
    (trace : OriginTrace profile initial history final family) :
    Stable initial.world final.world := by
  induction trace with
  | nil => exact Stable.refl _
  | cons head _tail ih => exact (origin_stable head).trans ih

theorem Pause.stable {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before after : State × Log} (paused : Pause profile tid before after family) :
    Stable before.1.world after.1.world := by
  obtain ⟨_suffix, trace, _quiet, _same⟩ := paused
  exact trace.stable

namespace Mixed

theorem Idle.stable {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before after : State × Log} (idle : Idle profile tid before after family) :
    Stable before.1.world after.1.world := by
  obtain ⟨_suffix, trace, _allowed, _same⟩ := idle
  exact trace.stable

theorem Idle.authorize {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before after : State × Log} (idle : Idle profile tid before after family)
    (actor : Nat) (identifier : Atomics64.HandleId64) :
    Atomics64.authorize after.1.world actor identifier =
      Atomics64.authorize before.1.world actor identifier :=
  idle.stable.authorize actor identifier

theorem Idle.atomicFor {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before after : State × Log} (idle : Idle profile tid before after family)
    (resources : Resources) (address : Word) :
    TSO64.atomicFor after.1.world resources address =
      TSO64.atomicFor before.1.world resources address :=
  idle.stable.atomicFor resources address

/-- The live subject retains its resources and the same first selector at
a fixed address. A current data read remains a separate execution effect. -/
theorem Idle.atomic_selection {profile : Profile} {family : RMWFamily} {tid : Nat}
    {before after : State × Log} {prior : Worker}
    (idle : Idle profile tid before after family)
    (live : before.1.workers[tid]? = some prior) (address : Word) :
    ∃ current, after.1.workers[tid]? = some current ∧ SavedFrame prior current ∧
      TSO64.atomicFor after.1.world current.resources address =
        TSO64.atomicFor before.1.world prior.resources address := by
  obtain ⟨current, currentLive, saved⟩ := idle.saved live
  refine ⟨current, currentLive, saved, ?_⟩
  rw [saved.resources]
  exact idle.atomicFor prior.resources address

end Mixed
end EffectSimulation
end EDSL.OS.TSO64

#print axioms EDSL.OS.TSO64.Stable.atomicFor
#print axioms EDSL.OS.TSO64.EffectSimulation.OriginTrace.stable
#print axioms EDSL.OS.TSO64.EffectSimulation.Pause.stable
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.stable
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.authorize
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.atomicFor
#print axioms EDSL.OS.TSO64.EffectSimulation.Mixed.Idle.atomic_selection
#audit_edsl
