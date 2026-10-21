/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.WriteEvents

/-!
Order and causality of published managed-writer metadata along observation
prefixes. Observations retain their original positions, including silent
steps. Every classified publication counts, even when its payload is unchanged.

An incoming map may be arbitrary, but monotonicity requires its stamps to lie
strictly before the supplied starting position. This is a position boundary,
not an assertion that the incoming stamps have actual pre-run origins.

These results concern the published writer map only. They establish neither a
thread's pending-own view nor acquire/release view transfer, source-call
coverage, modification-rank assignment, or C23Atomic.Legal. Execution origins
remain those of PublishedHistory.WriteAt and the actual scheduler.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.PublishedOrder
open PublishedHistory

/-- Every known incoming position predates the first observation to be folded.
No incoming stamp is assigned an invented earlier execution or initializer. -/
def Prior (offset : Nat) (writers : Writers) : Prop :=
  ∀ target stamp, writers target = some stamp → stamp.position < offset

theorem prior_empty (offset : Nat) : Prior offset empty := by
  intro target stamp impossible
  cases impossible

/-- The boundary advances by every observation, not only by publications. -/
theorem prior_after {offset : Nat} {observations : List Observation} {writers : Writers}
    (prior : Prior offset writers) :
    Prior (offset + observations.length) (after offset observations writers) := by
  intro target stamp found
  rcases after_origin found with initial | observed
  · have bound := prior target stamp initial
    omega
  · obtain ⟨index, observation, bound, selected, written, position, cell⟩ := observed
    omega

/-- Folding cannot erase an already known published writer. It can replace it
with a different full stamp, including a write of the same value. -/
theorem present_after {offset : Nat} {observations : List Observation} {writers : Writers}
    {target : Atomics64.CellId64} {stamp : Stamp}
    (present : writers target = some stamp) :
    ∃ latest, after offset observations writers target = some latest := by
  induction observations generalizing offset writers stamp with
  | nil => exact ⟨stamp, present⟩
  | cons observation rest ih =>
    have head : ∃ next, update writers offset observation target = some next := by
      cases written : writeOf observation with
      | none => exact ⟨stamp, by simpa only [update, written] using present⟩
      | some cause =>
        by_cases same : cause.cell = target
        · exact ⟨⟨offset, cause⟩, by simp only [update, written, ite_eq_left same]⟩
        · exact ⟨stamp, by simpa only [update, written, ite_eq_right same] using present⟩
    obtain ⟨next, found⟩ := head
    exact ih (offset := offset + 1) found

/-- Extending an observation stream either preserves the exact writer with
no suffix publication to its cell, or installs a strictly later actual suffix
writer. The new writer has its exact original suffix position and complete
cause, and no later suffix observation writes that cell. Multiple intervening
publications and equal payloads require no special cases. -/
theorem append_order {offset : Nat} {earlierObs suffix : List Observation} {writers : Writers}
    {target : Atomics64.CellId64} {previous : Stamp} (prior : Prior offset writers)
    (earlier : after offset earlierObs writers target = some previous) :
    ∃ latest, after offset (earlierObs ++ suffix) writers target = some latest ∧
      ((latest = previous ∧ NoWrites suffix target) ∨
        (previous.position < latest.position ∧
          ∃ index observation, index < suffix.length ∧
            suffix[index]? = some observation ∧ writeOf observation = some latest.cause ∧
            latest.position = offset + earlierObs.length + index ∧ latest.cause.cell = target ∧
            NoWrites (suffix.drop (index + 1)) target)) := by
  have bound := prior_after prior target previous earlier
  obtain ⟨latest, found⟩ := present_after (offset := offset + earlierObs.length)
    (observations := suffix) earlier
  have full : after offset (earlierObs ++ suffix) writers target = some latest := by
    rw [after_append]
    exact found
  refine ⟨latest, full, ?_⟩
  rcases after_newest found with initial | observed
  · have same : previous = latest := Option.some.inj (earlier.symm.trans initial.1)
    exact .inl ⟨same.symm, initial.2⟩
  · obtain ⟨index, observation, length, selected, written, position, cell, noLater⟩ := observed
    exact .inr ⟨by omega, index, observation, length, selected, written, position, cell, noLater⟩

/-- A known writer remains identical precisely when the appended suffix makes
no publication to that cell. Equality of values does not imply this property. -/
theorem append_same_iff {offset : Nat} {earlierObs suffix : List Observation} {writers : Writers}
    {target : Atomics64.CellId64} {stamp : Stamp} (prior : Prior offset writers)
    (earlier : after offset earlierObs writers target = some stamp) :
    after offset (earlierObs ++ suffix) writers target = some stamp ↔ NoWrites suffix target := by
  constructor
  · intro same
    obtain ⟨latest, found, unchanged | changed⟩ := append_order (suffix := suffix) prior earlier
    · exact unchanged.2
    · have equal : latest = stamp := Option.some.inj (found.symm.trans same)
      have impossible : stamp.position < stamp.position := by simpa only [equal] using changed.1
      exact False.elim (Nat.lt_irrefl _ impossible)
  · intro absent
    rw [after_append, after_noWrites absent]
    exact earlier

/-- A numerical observation-position view: absence is zero; a real stamp has
its successor position. This is not a per-cell modification rank or a
pending-store-buffer view. -/
def view (writers : Writers) (target : Atomics64.CellId64) : Nat :=
  match writers target with
  | none => 0
  | some stamp => stamp.position + 1

/-- Appending any finite suffix cannot lower the published position view. The
prior-position premise is essential for arbitrary incoming writer maps. -/
theorem append_view {offset : Nat} {earlierObs suffix : List Observation} {writers : Writers}
    (prior : Prior offset writers) (target : Atomics64.CellId64) :
    view (after offset earlierObs writers) target ≤
      view (after offset (earlierObs ++ suffix) writers) target := by
  cases earlier : after offset earlierObs writers target with
  | none =>
    simp only [view, earlier]
    exact Nat.zero_le _
  | some previous =>
    obtain ⟨latest, found, ordering⟩ := append_order (suffix := suffix) prior earlier
    have positions : previous.position ≤ latest.position := by
      rcases ordering with unchanged | changed
      · rw [unchanged.1]
        exact Nat.le_refl _
      · exact Nat.le_of_lt changed.1
    simp only [view, earlier, found]
    omega

private theorem take_split {α : Type _} (observations : List α) {first last : Nat}
    (ordered : first ≤ last) :
    observations.take last = observations.take first ++ (observations.drop first).take (last - first) := by
  calc
    observations.take last = observations.take (first + (last - first)) := by
      congr 1
      omega
    _ = _ := List.take_add

/-- Published views are monotone across any two observation prefixes. Prefix
indices may exceed the stream's length; their actual truncated lengths still
determine the correct global offset, and no positions are invented. -/
theorem prefix_view {offset : Nat} {observations : List Observation} {writers : Writers}
    (prior : Prior offset writers) {first last : Nat} (ordered : first ≤ last)
    (target : Atomics64.CellId64) :
    view (after offset (observations.take first) writers) target ≤
      view (after offset (observations.take last) writers) target := by
  rw [take_split observations ordered]
  exact append_view prior target

/-- A known writer at an earlier prefix remains present at every later
prefix, with either the identical stamp or a strictly greater position. -/
theorem prefix_order {offset : Nat} {observations : List Observation} {writers : Writers}
    (prior : Prior offset writers) {first last : Nat} (ordered : first ≤ last)
    {target : Atomics64.CellId64} {previous : Stamp}
    (earlier : after offset (observations.take first) writers target = some previous) :
    ∃ latest, after offset (observations.take last) writers target = some latest ∧
      (latest = previous ∨ previous.position < latest.position) := by
  obtain ⟨latest, found, ordering⟩ := append_order
    (suffix := (observations.drop first).take (last - first)) prior earlier
  refine ⟨latest, ?_, ?_⟩
  · simpa only [take_split observations ordered] using found
  · rcases ordering with unchanged | changed
    · exact .inl unchanged.1
    · exact .inr changed.1

/-- Every actual same-cell publication in the stream is no later than the
final writer. This causality result needs no condition on incoming stamps:
the existence of this actual publication rules out a retained boundary stamp
with no writes. It distinguishes actual write positions despite equal values. -/
theorem dominates_write {offset : Nat} {observations : List Observation} {writers : Writers}
    {target : Atomics64.CellId64} {latest : Stamp}
    (found : after offset observations writers target = some latest)
    {index : Nat} {observation : Observation} {cause : WriteCause}
    (selected : observations[index]? = some observation)
    (written : writeOf observation = some cause) (cell : cause.cell = target) :
    offset + index ≤ latest.position := by
  rcases after_newest found with initial | observed
  · exact False.elim ((initial.2 observation (List.mem_of_getElem? selected) cause written) cell)
  · obtain ⟨last, lastObservation, length, lastSelected, lastWritten, position,
      lastCell, noLater⟩ := observed
    by_cases lower : offset + index ≤ latest.position
    · exact lower
    · have afterLast : last + 1 ≤ index := by omega
      have shifted : (observations.drop (last + 1))[index - (last + 1)]? = some observation := by
        rw [List.getElem?_drop]
        have aligned : last + 1 + (index - (last + 1)) = index := by omega
        rw [aligned]
        exact selected
      exact False.elim ((noLater observation (List.mem_of_getElem? shifted) cause written) cell)

/-- The same domination property for the existing complete write enumeration.
No event is coalesced because its value or complete cause matches another. -/
theorem dominates_enumerated {offset : Nat} {observations : List Observation} {writers : Writers}
    {target : Atomics64.CellId64} {latest earlier : Stamp}
    (found : after offset observations writers target = some latest)
    (member : earlier ∈ C23Projection.writes offset observations)
    (cell : earlier.cause.cell = target) : earlier.position ≤ latest.position := by
  obtain ⟨index, observation, selected, written, position⟩ :=
    (C23Projection.mem_writes_iff offset observations earlier).mp member
  have bound := dominates_write found selected written cell
  simpa only [position] using bound

/-- A real scheduler write at an original action position cannot lie after
that run's final published writer for the same cell. Execution origin comes
from the existing actual-prefix WriteAt witness, not from equal memory bits. -/
theorem writeAt_before_final {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset : Nat}
    {writers : Writers} {target : Atomics64.CellId64} {latest earlier : Stamp}
    (witness : WriteAt state actions result profile offset earlier)
    (found : after offset result.2 writers target = some latest)
    (cell : earlier.cause.cell = target) : earlier.position ≤ latest.position := by
  have bound := dominates_write found witness.observed witness.written cell
  simpa only [witness.position] using bound

end EDSL.OS.TSO64.PublishedOrder

#audit_edsl
