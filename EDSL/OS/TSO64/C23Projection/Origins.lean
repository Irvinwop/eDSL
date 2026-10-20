/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.StoreHistory.Indexed
import EDSL.OS.TSO64.StoreHistory.Flow
import EDSL.OS.TSO64.PublishedHistory

/-!
Issue identities behind actual managed publication stamps. These execution
facts are prerequisites for constructing source event graphs; they assign no
source memory order and establish no machine-to-source preservation theorem.
An empty initial FIFO boundary excludes unrecorded pre-run store issues.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection
open X86 StoreHistory PublishedHistory

/-- A buffered publication in the actual run names an earlier issue of that
exact thread, descriptor, value and occurrence in the same complete run.
Publication position and issue position are deliberately different identities. -/
theorem buffered_issue {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset position tid occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (empty : Quiescent state) (success : schedule state actions profile = .ok result)
    (witness : WriteAt state actions result profile offset
      ⟨position, .buffered tid reference value occurrence⟩) :
    ∃ index, index < witness.index ∧
      IssuedAt profile tid (.managed reference value occurrence) index state actions result := by
  have issued : IssuedIn profile tid (.managed reference value occurrence) state
      (actions.take witness.index) (witness.before, result.2.take witness.index) := by
    rcases witness.buffered_origin with boundary | issued
    · obtain ⟨worker, live, member⟩ := boundary
      have none := empty worker (List.mem_of_getElem? live)
      rw [none] at member
      cases member
    · exact issued
  obtain ⟨index, indexed⟩ := issued.indexed
  have bound := indexed.bound
  simp only [List.length_take] at bound
  exact ⟨index, by omega, indexed.lift_prefix success⟩

/-- The original issue behind a publication is unique for its actual
thread/occurrence identity. Equal words never serve as writer identifiers. -/
theorem buffered_issue_unique {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset position tid occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (empty : Quiescent state) (success : schedule state actions profile = .ok result)
    (witness : WriteAt state actions result profile offset
      ⟨position, .buffered tid reference value occurrence⟩) :
    ∃ index, index < witness.index ∧
      IssuedAt profile tid (.managed reference value occurrence) index state actions result ∧
      ∀ otherIndex, IssuedAt profile tid (.managed reference value occurrence)
        otherIndex state actions result → otherIndex = index := by
  obtain ⟨index, before, actual⟩ := buffered_issue empty success witness
  exact ⟨index, before, actual, fun _ other => other.occurrence_index_unique actual⟩

/-- A quiescent endpoint guarantees publication of each actual issued tag.
Returning alone is insufficient. This is an existence result; distinct drain
positions and source modification-order correspondence require further facts. -/
theorem issued_is_published {state : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid index : Nat} {entry : Pending}
    (issued : IssuedAt profile tid entry index state actions result)
    (empty : Quiescent result.1) : .drained tid entry ∈ result.2 :=
  issued.forget.published_of_quiescent empty

end EDSL.OS.TSO64.C23Projection
