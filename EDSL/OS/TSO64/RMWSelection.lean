/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Run
import EDSL.Audit

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Recover the actual ordered authority selection behind a production RMW label.
The primitive's handle, actor, cell identity and operand address remain linked
to the same dispatch, even when several listed handles authorize one cell.
No equality between resource principals and scheduler thread ids is assumed.
This conditional effect theorem adds no admission, progress, compiler or
physical machine correspondence claim.
-/

namespace EDSL.OS.TSO64
open X86

/-- Every actual RMW retains its first current authorized matching handle at
its actual operand address. Membership in the resource list alone is weaker. -/
theorem rmw_selection {before after : TSO64.State} {action : Action}
    {tid : Nat} {event : Atomics64.FetchAddEvent} {profile : Profile} {family : RMWFamily}
    (actual : TSO64.step before action profile family = .ok (after, .rmw tid event)) :
    ∃ (worker : Worker) (handle : Atomics64.Handle) (cell : Atomics64.Cell),
      before.workers[tid]? = some worker ∧
      atomicFor before.world worker.resources event.arithmetic.event.address =
        some (event.handle, handle, cell) ∧
      handle.cell = event.cell ∧ cell.address = event.arithmetic.event.address ∧
      event.actor = worker.resources.actor := by
  cases action with
  | drain thread => cases step_origin actual
  | issue thread af =>
    obtain ⟨worker, live, _running, _code, _caller, instruction, _fetched, effect⟩ :=
      issue_effect actual
    cases instruction with
    | ordinary instruction =>
      cases effect with
      | intro _supported _bounds _decoded _reads _queue _executed finish => cases finish
    | locked instruction =>
      cases effect with
      | @rmw identifier handle cell output machine _bounds _empty _decoded selected changed _executed =>
        have authorized := (atomicFor_sound selected).2.1
        have operand := (atomicFor_sound selected).2.2
        have identity := Atomics64.fetchAdd_identity _ _ _ _ _ _ _ changed authorized
        have actorHandle := (Atomics64.fetchAdd_sound _ _ _ _ _ changed).2.2.2
        refine ⟨worker, handle, cell, live, ?_, identity.1.symm, identity.2.symm, actorHandle.1⟩
        simpa only [identity.2, actorHandle.2, operand] using selected

#print axioms rmw_selection

end EDSL.OS.TSO64

#audit_edsl
