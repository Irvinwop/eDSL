/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.EffectSimulation.Mixed.Cohort

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Projections of caller-only cohort retirement classification. Every position
in the original successful schedule is an issue that retires one instruction;
no drain action or blocked observation is omitted from these statements.
The classification must first be derived from actual execution and current
cohort closure. These projections do not independently establish execution,
progress, fairness, cost optimality or physical machine correspondence.
-/

namespace EDSL.OS.TSO64.EffectSimulation.Mixed.Cohort.RetirementTrace

variable {ι : Type} {profile : Profile} {family : RMWFamily}
    {cohort : Cohort ι profile family} {actions : List Action} {observations : List O}

/-- A classification of the whole trace excludes every original drain action. -/
theorem no_drains (trace : cohort.RetirementTrace actions observations) :
    ∀ tid, Action.drain tid ∉ actions := by
  induction trace with
  | nil =>
    intro tid member
    cases member
  | @cons action seen rest restSeen head _tail ih =>
    intro tid member
    rcases List.mem_cons.mp member with same | later
    · obtain ⟨subject, af, issued, _label⟩ := head
      rw [issued] at same
      cases same
    · exact ih tid later

/-- Every original observation is a retirement, without filtering its tag. -/
theorem all_retired (trace : cohort.RetirementTrace actions observations) :
    ∀ seen ∈ observations, seen.retired = 1 := by
  induction trace with
  | nil =>
    intro seen member
    cases member
  | @cons action seen rest restSeen head _tail ih =>
    intro query member
    rcases List.mem_cons.mp member with same | later
    · subst query
      exact head.retired
    · exact ih query later

#print axioms no_drains
#print axioms all_retired

end EDSL.OS.TSO64.EffectSimulation.Mixed.Cohort.RetirementTrace

#audit_edsl
