/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Frames
import EDSL.OS.PlainCallAdmission64
import EDSL.X86.VCGen.PlainMethods.Footprint
import EDSL.X86.VCGen.PlainMethods.ABI

/-!
Compose independently admitted mixed load/store cohorts with the production
plain-method footprint and scalar ABI theorems. The only dynamic proof input is
an actual successful schedule. Static checked shapes remain separate from the
current-only contract, and no future cutpoint, selected reply, write-set oracle
or completion-at-RET publication premise is needed.

The conclusions are prefix and return frames, rather than the full atomic
behavior/history postcondition or a frozen final-ELF certificate.
-/

set_option autoImplicit false

namespace EDSL.OS.PlainCallFrames64
open X86 TSO64 AddressSpace Grading.ConcurrentTask.Plain64
open X86.VCGen

/-- The proof engine's footprint equals the independent input/actual-FIFO
footprint. Complete descriptors, entry widths and all initial slots survive. -/
theorem affected_iff {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) (query : Word) :
    PlainMethods.Footprint.affected (PlainCallAdmission64.invocations static pre) query ↔
      Affected before inputs query := by
  constructor
  · rintro (⟨tid, inside⟩ | ⟨tid, entry, ⟨worker, live, member⟩, inside⟩)
    · left
      refine ⟨tid, ?_⟩
      change (qwordRegion
        (PlainCallAdmission64.admission static pre tid).invocation.method.reference.cell.address
          ).Contains query at inside
      rw [(PlainCallAdmission64.admission static pre tid).descriptor] at inside
      exact inside
    · right
      exact ⟨tid, worker, entry, live, member, inside⟩
  · rintro (⟨tid, inside⟩ | ⟨tid, worker, entry, live, member, inside⟩)
    · left
      refine ⟨tid, ?_⟩
      change (qwordRegion
        (PlainCallAdmission64.admission static pre tid).invocation.method.reference.cell.address
          ).Contains query
      rw [(PlainCallAdmission64.admission static pre tid).descriptor]
      exact inside
    · right
      exact ⟨tid, entry, ⟨worker, live, member⟩, inside⟩

/-- Every actual successful prefix preserves all independent resource and
full-cell observations outside the fixed target-plus-incoming footprint. -/
theorem prefix_frame {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {actions : List Action}
    {result : TSO64.State × List Observation}
    (success : schedule before actions .sharedCell = .ok result) :
    PrefixFrame before result.1 inputs where
  valid := schedule_wellFormed pre.valid success
  stable := schedule_stable success
  population := ScheduleTrace.workers_length success
  resources := fun _ _ live => schedule_current_resources pre.valid success live
  selected := by
    intro tid
    obtain ⟨initial, live, facts⟩ := pre.entry tid
    obtain ⟨current, currentLive, retained, _valid⟩ :=
      schedule_current_resources pre.valid success live
    obtain ⟨identifier, handle, selected, target⟩ := facts.selected
    refine ⟨current, identifier, handle, currentLive, ?_, target⟩
    rw [retained]
    exact (AtomicMethods.atomicFor_stable (schedule_stable success) _ _).trans selected
  cells := by
    intro query outside
    apply PlainMethods.Footprint.cells_frame (PlainCallAdmission64.invocations static pre)
      success query
    intro affected
    exact outside ((affected_iff static pre query).mp affected)

/-- An actually returned slot has its independent scalar ABI frame relative to
its actual original worker. The observed reply comes from `all_completed`;
neither a desired reply nor an assumed later method point is a premise. -/
theorem returned_slot {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {actions : List Action}
    {result : TSO64.State × List Observation}
    (success : schedule before actions .sharedCell = .ok result)
    (tid : Fin before.workers.length) {initial final : Worker}
    (initialLive : before.workers[tid.val]? = some initial)
    (finalLive : result.1.workers[tid.val]? = some final)
    (returned : final.phase = .returned) :
    ScalarCall64.ReturnFrame before result.1 tid.val initial final := by
  let admitted := PlainCallAdmission64.admission static pre tid
  have original : admitted.invocation.initial = initial := admitted.initial_eq initialLive
  obtain ⟨_current, _reply, post, _access, _issues, _observed⟩ :=
    PlainMethods.all_completed admitted.invocation.current admitted.invocation.live
      admitted.invocation.entry success finalLive returned
  have frame := post.return_frame admitted.invocation.current admitted.invocation.live
    admitted.invocation.entry admitted.scalar (schedule_wellFormed pre.valid success) finalLive
  simpa only [original] using frame

/-- A returned cohort composes the same prefix frame and the scalar ABI frame
for every actual original slot. No final queue-emptiness is required. -/
theorem returned_cohort {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {actions : List Action}
    {result : TSO64.State × List Observation}
    (success : schedule before actions .sharedCell = .ok result)
    (returned : TSO64.Returned result.1) :
    Grading.ConcurrentTask.Plain64.ReturnFrame before result.1 inputs where
  toPrefixFrame := prefix_frame static pre success
  returned := returned
  slots := by
    intro tid initial final initialLive finalLive
    exact returned_slot static pre success tid initialLive finalLive
      (returned final (List.mem_of_getElem? finalLive))

end EDSL.OS.PlainCallFrames64

#audit_edsl
