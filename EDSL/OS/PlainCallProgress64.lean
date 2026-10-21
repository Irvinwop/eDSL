/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Progress
import EDSL.OS.PlainCallAdmission64
import EDSL.X86.VCGen.PlainMethods.Completion

/-!
Derive enabledness and a uniform own-issue bound from independent current
admission, static checked windows and the actual successful prefix. The bound
comes from actual instruction lengths and the supported 64-byte extent; it is
not another admission assumption. No desired future cutpoint is supplied.
-/

set_option autoImplicit false

namespace EDSL.OS.PlainCallProgress64
open X86 TSO64 Grading.ConcurrentTask.Plain64 X86.VCGen

/-- The proof engine counts the same independently observed issue actions. -/
theorem issues_eq (tid : Nat) (actions : List Action) :
    issues tid actions = AtomicMethods.ownIssues tid actions := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
    cases action with
    | issue thread af =>
      by_cases same : thread = tid
      · subst thread
        simpa [issues, AtomicMethods.ownIssues, AtomicMethods.ownIssue,
          Nat.add_comm] using ih
      · simpa [issues, AtomicMethods.ownIssues, AtomicMethods.ownIssue, same,
          Ne.symm same] using ih
    | drain thread =>
      simpa [issues, AtomicMethods.ownIssues, AtomicMethods.ownIssue] using ih

/-- Every padding/access/RET consumes at least one byte in the complete window.
The rule is shared by all supported operand encodings and declared padding. -/
theorem shape_issue_bound {bytes : List Byte} {operation : PlainMethods.Operation}
    {offset : Nat} {padding : List AtomicMethods.Padding}
    (shape : PlainMethods.Shape bytes operation offset padding) :
    offset + padding.length + 2 ≤ bytes.length := by
  induction shape with
  | body access ret extent =>
    have positive := operation.instruction.length_pos
    simp only [PlainMethods.Operation.length] at extent
    simp only [List.length_nil]
    omega
  | @pad offset head rest node tail ih =>
    have positive := head.instruction.length_pos
    simp only [List.length_cons]
    omega

/-- Static checked shape, independently admitted resources and the actual
prefix suffice to enable every currently running worker, for either AF. -/
theorem enabled {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {actions : List Action}
    {result : TSO64.State × List Observation}
    (success : schedule before actions .sharedCell = .ok result) : Enabled result.1 := by
  intro tid worker live running af
  have bound : tid < before.workers.length := by
    have actualBound := (List.getElem_of_getElem? live).1
    rw [ScheduleTrace.workers_length success] at actualBound
    exact actualBound
  let admitted := PlainCallAdmission64.admission static pre ⟨tid, bound⟩
  obtain ⟨current, point, actualWorker, _, actualLive, located, _, _, _⟩ :=
    PlainMethods.schedule_preserves admitted.invocation.current admitted.invocation.live
      admitted.invocation.entry success
  have same : actualWorker = worker := Option.some.inj (actualLive.symm.trans live)
  subst actualWorker
  have unfinished : point.remaining ≠ 0 := by
    intro zero
    have returned := located.zero_returned zero
    rw [running] at returned
    cases returned
  exact PlainMethods.enabled current live located unfinished af

/-- A supported complete window has at most 64 successful own issues to RET.
This is a derived uniform upper bound, with no queue-emptiness assumption. -/
theorem bounded {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {actions : List Action}
    {result : TSO64.State × List Observation}
    (success : schedule before actions .sharedCell = .ok result) :
    Bounded 64 actions result.1 := by
  intro tid worker live count
  have bound : tid < before.workers.length := by
    have actualBound := (List.getElem_of_getElem? live).1
    rw [ScheduleTrace.workers_length success] at actualBound
    exact actualBound
  let admitted := PlainCallAdmission64.admission static pre ⟨tid, bound⟩
  have shape := admitted.invocation.entry.location.2.2.2
  have limit := shape_issue_bound shape
  have size := admitted.invocation.method.size
  have enough : (PlainMethods.Point.preamble (operation := admitted.invocation.method.operation)
      0 admitted.invocation.padding).remaining ≤
      AtomicMethods.ownIssues tid actions := by
    rw [← issues_eq]
    change admitted.invocation.padding.length + 2 ≤ issues tid actions
    omega
  obtain ⟨final, reply, finalLive, located, _⟩ :=
    PlainMethods.enough_own_issues admitted.invocation.current admitted.invocation.live
      admitted.invocation.entry success enough
  have same : final = worker := Option.some.inj (finalLive.symm.trans live)
  subst final
  exact located.location.1

end EDSL.OS.PlainCallProgress64

#audit_edsl
