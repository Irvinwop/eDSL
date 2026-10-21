/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph

/-!
Structural C23 graph well-formedness follows from the finite correspondence
`Built` alone. Initial writer keys distinguish manifest rows; actual writer
keys and unique publication positions distinguish noninitial write ranks.
`AtBoundary` supplies a manifest initializer for every actual event, while
`ReadCorrespondence` supplies exactly the required source metadata. Table
shape excludes read sources outside the live event list.

This proves neither execution origins nor initialization provenance, coherence,
happens-before constraints, RMW predecessor legality, or full C23 legality.
No execution, queue-boundary, or interface-order restriction is required.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
open X86

private theorem some_key_index {α : Type} {keys : List (Option α)}
    (unique : (keys.filterMap id).Nodup) {key : α} {i j : Nat}
    (first : keys[i]? = some (some key))
    (second : keys[j]? = some (some key)) : i = j := by
  obtain ⟨firstBound, firstValue⟩ := List.getElem_of_getElem? first
  obtain ⟨secondBound, secondValue⟩ := List.getElem_of_getElem? second
  have separated : keys.Pairwise (fun a b =>
      ∀ x, a = some x → ∀ y, b = some y → x ≠ y) :=
    List.pairwise_filterMap.mp unique
  by_cases before : i < j
  · have different := List.Pairwise.rel_getElem_of_lt firstBound secondBound
      separated before key firstValue key secondValue
    exact False.elim (different rfl)
  · by_cases after : j < i
    · have different := List.Pairwise.rel_getElem_of_lt secondBound firstBound
        separated after key secondValue key firstValue
      exact False.elim (different rfl)
    · omega

private theorem initial_writer_at (inputs : Inputs) (index : Fin inputs.initials.length) :
    (writerIds inputs)[index.val]? =
      some (some (.initial inputs.initials[index.val].identifier)) := by
  unfold writerIds
  rw [List.getElem?_append_left (by simpa only [List.length_map] using index.isLt)]
  simp only [List.getElem?_map, List.getElem?_eq_getElem index.isLt, Option.map_some]

private theorem event_writer_at (inputs : Inputs) (index : Fin inputs.events.length) :
    (writerIds inputs)[inputs.initials.length + index.val]? =
      some (inputs.events[index.val].writer) := by
  unfold writerIds
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  have aligned : inputs.initials.length + index.val - inputs.initials.length = index.val := by
    omega
  simp only [List.length_map, aligned, List.getElem?_map,
    List.getElem?_eq_getElem index.isLt, Option.map_some]

private theorem publication_writer {event : AtomicTrace.Event}
    {stamp : PublishedHistory.Stamp} (matched : Publication event stamp) :
    event.writer = some (publicationKey stamp) := by
  cases access : event.access with
  | load reference value source => simp only [Publication, access] at matched
  | store reference value occurrence =>
      have parts : stamp.cause = .buffered event.tid reference value occurrence ∧
          event.position < stamp.position := by
        simpa only [Publication, access] using matched
      simp only [AtomicTrace.Event.writer, access, publicationKey, parts.1]
  | rmw changed source =>
      have parts : stamp.cause = .rmw event.tid changed ∧ stamp.position = event.position := by
        simpa only [Publication, access] using matched
      simp only [AtomicTrace.Event.writer, access, publicationKey, parts.1, parts.2]

private theorem actual_not_initial (event : AtomicTrace.Event) (orders : Orders) :
    (event.toSource orders).access.isInitial = false := by
  cases access : event.access <;>
    simp only [AtomicTrace.Event.toSource, access, Concurrency.C23Atomic.Access.isInitial]

variable {inputs : Inputs} {orders : Orders} {table : Table}

private theorem node_cases (mapped : Built inputs orders table) (index : table.Index) :
    (∃ initial : Fin inputs.initials.length,
      index.val = initial.val ∧ table.node index = initialEvent inputs.initials[initial.val]) ∨
    (∃ actual : Fin inputs.events.length,
      index.val = inputs.initials.length + actual.val ∧
        table.node index = inputs.events[actual.val].toSource orders) := by
  have lengths := congrArg List.length mapped.events_eq
  simp only [sourceEvents, List.length_append, List.length_map] at lengths
  have bound : index.val < inputs.initials.length + inputs.events.length := by
    have within := index.isLt
    omega
  by_cases inInitials : index.val < inputs.initials.length
  · let initial : Fin inputs.initials.length := ⟨index.val, inInitials⟩
    exact .inl ⟨initial, rfl, table.node_of_lookup index (mapped.initial_at initial)⟩
  · have inEvents : index.val - inputs.initials.length < inputs.events.length := by omega
    let actual : Fin inputs.events.length := ⟨index.val - inputs.initials.length, inEvents⟩
    have aligned : index.val = inputs.initials.length + actual.val := by dsimp [actual]; omega
    have lookup := mapped.event_at actual
    rw [← aligned] at lookup
    exact .inr ⟨actual, aligned, table.node_of_lookup index lookup⟩

private theorem initial_node (mapped : Built inputs orders table) (index : table.Index)
    (initial : (table.node index).access.isInitial = true) :
    ∃ slot : Fin inputs.initials.length,
      index.val = slot.val ∧ table.node index = initialEvent inputs.initials[slot.val] := by
  rcases node_cases mapped index with fromInitial | ⟨actual, _, node⟩
  · exact fromInitial
  · rw [node, actual_not_initial] at initial
    cases initial

private theorem actual_node (mapped : Built inputs orders table) (index : table.Index)
    (noninitial : (table.node index).access.isInitial = false) :
    ∃ actual : Fin inputs.events.length,
      index.val = inputs.initials.length + actual.val ∧
        table.node index = inputs.events[actual.val].toSource orders := by
  rcases node_cases mapped index with ⟨initial, _, node⟩ | fromActual
  · rw [node] at noninitial
    cases noninitial
  · exact fromActual

private theorem boundary_initial {event : AtomicTrace.Event}
    (boundary : AtBoundary inputs event) :
    ∃ initial : Fin inputs.initials.length,
      event.object = inputs.initials[initial.val].identifier := by
  cases access : event.access <;>
    simp only [AtBoundary, access] at boundary <;>
    obtain ⟨initial, object, _⟩ := boundary <;>
    exact ⟨initial, by simpa only [AtomicTrace.Event.object, access] using object⟩

private theorem initial_rank_zero (mapped : Built inputs orders table)
    (initial : Fin inputs.initials.length) : table.rank initial.val = 0 := by
  have ranked := (mapped.initial initial).2
  simp only [Concurrency.C23Atomic.Check.Table.rank, ranked, Option.getD_some]

private theorem actual_write_rank (mapped : Built inputs orders table)
    (actual : Fin inputs.events.length)
    (written : (inputs.events[actual.val].toSource orders).access.writeValue.isSome = true) :
    ∃ publication : Fin inputs.writes.length,
      Publication inputs.events[actual.val] inputs.writes[publication.val] ∧
      table.rank (inputs.initials.length + actual.val) =
        inputs.writes[publication.val].position + 1 := by
  have rank := (mapped.event actual).2.2
  have correspondence : ∃ publication : Fin inputs.writes.length,
      Publication inputs.events[actual.val] inputs.writes[publication.val] ∧
      table.ranks[inputs.initials.length + actual.val]? =
        some (inputs.writes[publication.val].position + 1) := by
    cases access : inputs.events[actual.val].access with
    | load reference value source =>
        simp [AtomicTrace.Event.toSource, access,
          Concurrency.C23Atomic.Access.writeValue] at written
    | store reference value occurrence =>
        simpa only [RankCorrespondence, access] using rank
    | rmw changed source =>
        simpa only [RankCorrespondence, access] using rank
  obtain ⟨publication, matched, ranked⟩ := correspondence
  exact ⟨publication, matched, by
    simp only [Concurrency.C23Atomic.Check.Table.rank, ranked, Option.getD_some]⟩

private theorem publication_index (mapped : Built inputs orders table)
    (first second : Fin inputs.writes.length)
    (samePosition : inputs.writes[first.val].position = inputs.writes[second.val].position) :
    first = second := by
  apply Fin.ext
  exact mapped.publication_keys.2.eq_of_getElem_eq
    (by simpa only [List.length_map] using first.isLt)
    (by simpa only [List.length_map] using second.isLt)
    (by simpa only [List.getElem_map] using samePosition)

private theorem actual_rank_unique (mapped : Built inputs orders table)
    (first second : Fin inputs.events.length)
    (firstWrite : (inputs.events[first.val].toSource orders).access.writeValue.isSome = true)
    (secondWrite : (inputs.events[second.val].toSource orders).access.writeValue.isSome = true)
    (sameRank : table.rank (inputs.initials.length + first.val) =
      table.rank (inputs.initials.length + second.val)) :
    inputs.initials.length + first.val = inputs.initials.length + second.val := by
  obtain ⟨firstPublication, firstMatched, firstRank⟩ := actual_write_rank mapped first firstWrite
  obtain ⟨secondPublication, secondMatched, secondRank⟩ := actual_write_rank mapped second secondWrite
  have samePosition : inputs.writes[firstPublication.val].position =
      inputs.writes[secondPublication.val].position := by
    rw [firstRank, secondRank] at sameRank
    omega
  have samePublication := publication_index mapped firstPublication secondPublication samePosition
  have firstKey := event_writer_at inputs first
  have secondKey := event_writer_at inputs second
  rw [publication_writer firstMatched] at firstKey
  rw [publication_writer secondMatched, ← samePublication] at secondKey
  exact some_key_index mapped.writer_keys firstKey secondKey

private theorem node_thread_kind (mapped : Built inputs orders table) (index : table.Index) :
    (table.node index).thread = none ↔ (table.node index).access.isInitial = true := by
  rcases node_cases mapped index with ⟨initial, _, node⟩ | ⟨actual, _, node⟩
  · simp [node, initialEvent, Concurrency.C23Atomic.Access.isInitial]
  · rw [node, actual_not_initial]
    simp [AtomicTrace.Event.toSource]

private theorem node_initial_unique (mapped : Built inputs orders table)
    (first second : table.Index)
    (firstInitial : (table.node first).access.isInitial = true)
    (secondInitial : (table.node second).access.isInitial = true)
    (sameObject : (table.node first).object = (table.node second).object) :
    first.val = second.val := by
  obtain ⟨firstSlot, firstIndex, firstNode⟩ := initial_node mapped first firstInitial
  obtain ⟨secondSlot, secondIndex, secondNode⟩ := initial_node mapped second secondInitial
  have sameIdentifier : inputs.initials[firstSlot.val].identifier =
      inputs.initials[secondSlot.val].identifier := by
    simpa only [firstNode, secondNode, initialEvent] using sameObject
  have firstKey := initial_writer_at inputs firstSlot
  have secondKey := initial_writer_at inputs secondSlot
  rw [← sameIdentifier] at secondKey
  have sameSlot := some_key_index mapped.writer_keys firstKey secondKey
  exact firstIndex.trans (sameSlot.trans secondIndex.symm)

private theorem node_initial_exists (mapped : Built inputs orders table) (index : table.Index) :
    ∃ initial : table.Index,
      (table.node initial).access.isInitial = true ∧
        (table.node initial).object = (table.node index).object := by
  rcases node_cases mapped index with ⟨initial, _, node⟩ | ⟨actual, _, node⟩
  · exact ⟨index, by rw [node]; rfl, rfl⟩
  · obtain ⟨initial, sameObject⟩ := boundary_initial (mapped.event actual).1
    let initialIndex : table.Index :=
      ⟨initial.val, (List.getElem_of_getElem? (mapped.initial_at initial)).1⟩
    have initialNode : table.node initialIndex = initialEvent inputs.initials[initial.val] :=
      table.node_of_lookup initialIndex (mapped.initial_at initial)
    refine ⟨initialIndex, ?_, ?_⟩
    · rw [initialNode]
      rfl
    · rw [initialNode, node]
      exact sameObject.symm

private theorem node_rank (mapped : Built inputs orders table) (index : table.Index)
    (written : (table.node index).access.writeValue.isSome = true) :
    ((table.node index).access.isInitial = true → table.rank index.val = 0) ∧
    ((table.node index).access.isInitial = false → 0 < table.rank index.val) := by
  rcases node_cases mapped index with ⟨initial, aligned, node⟩ | ⟨actual, aligned, node⟩
  · have zero : table.rank index.val = 0 := by
      rw [aligned]
      exact initial_rank_zero mapped initial
    refine ⟨fun _ => zero, ?_⟩
    intro noninitial
    rw [node] at noninitial
    cases noninitial
  · obtain ⟨publication, _, ranked⟩ := actual_write_rank mapped actual
      (by simpa only [node] using written)
    refine ⟨?_, ?_⟩
    · intro initial
      rw [node, actual_not_initial] at initial
      cases initial
    · intro _noninitial
      rw [aligned, ranked]
      exact Nat.zero_lt_succ _

private theorem node_rank_unique (mapped : Built inputs orders table)
    (first second : table.Index)
    (firstWrite : (table.node first).access.writeValue.isSome = true)
    (secondWrite : (table.node second).access.writeValue.isSome = true)
    (sameObject : (table.node first).object = (table.node second).object)
    (sameRank : table.rank first.val = table.rank second.val) : first.val = second.val := by
  by_cases firstInitial : (table.node first).access.isInitial = true
  · by_cases secondInitial : (table.node second).access.isInitial = true
    · exact node_initial_unique mapped first second firstInitial secondInitial sameObject
    · have zero := (node_rank mapped first firstWrite).1 firstInitial
      have positive := (node_rank mapped second secondWrite).2
        (Bool.eq_false_iff.mpr secondInitial)
      omega
  · by_cases secondInitial : (table.node second).access.isInitial = true
    · have positive := (node_rank mapped first firstWrite).2
        (Bool.eq_false_iff.mpr firstInitial)
      have zero := (node_rank mapped second secondWrite).1 secondInitial
      omega
    · obtain ⟨firstEvent, firstIndex, firstNode⟩ :=
        actual_node mapped first (Bool.eq_false_iff.mpr firstInitial)
      obtain ⟨secondEvent, secondIndex, secondNode⟩ :=
        actual_node mapped second (Bool.eq_false_iff.mpr secondInitial)
      have sameIndex := actual_rank_unique mapped firstEvent secondEvent
        (by simpa only [firstNode] using firstWrite)
        (by simpa only [secondNode] using secondWrite)
        (by simpa only [firstIndex, secondIndex] using sameRank)
      exact firstIndex.trans (sameIndex.trans secondIndex.symm)

private theorem node_source (mapped : Built inputs orders table) (index : table.Index) :
    match (table.node index).access.readValue with
    | none => table.source index.val = none
    | some value => ∃ writer : table.Index,
        table.source index.val = some writer.val ∧
        (table.node writer).object = (table.node index).object ∧
        (table.node writer).access.writeValue = some value := by
  rcases node_cases mapped index with ⟨initial, aligned, node⟩ | ⟨actual, aligned, node⟩
  · rw [node]
    change table.source index.val = none
    have chosen := (mapped.initial initial).1
    rw [aligned]
    simp only [Concurrency.C23Atomic.Check.Table.source, chosen, Option.getD_some]
  · rw [node]
    have correspondence := (mapped.event actual).2.1
    cases requested : inputs.events[actual.val].source with
    | none =>
        cases observed : (inputs.events[actual.val].toSource orders).access.readValue with
        | none =>
            have chosen : table.sources[inputs.initials.length + actual.val]? = some none := by
              simpa only [ReadCorrespondence, requested, observed] using correspondence
            change table.source index.val = none
            rw [aligned]
            simp only [Concurrency.C23Atomic.Check.Table.source, chosen, Option.getD_some]
        | some value =>
            simp only [ReadCorrespondence, requested, observed] at correspondence
    | some key =>
        cases observed : (inputs.events[actual.val].toSource orders).access.readValue with
        | none =>
            simp only [ReadCorrespondence, requested, observed] at correspondence
        | some value =>
            have selected : ∃ writer : table.Index,
                table.sources[inputs.initials.length + actual.val]? = some (some writer.val) ∧
                WriterAt inputs key writer.val ∧
                (table.node writer).object = inputs.events[actual.val].object ∧
                (table.node writer).access.writeValue = some value := by
              simpa only [ReadCorrespondence, requested, observed] using correspondence
            obtain ⟨writer, chosen, _, object, stored⟩ := selected
            refine ⟨writer, ?_, object, stored⟩
            rw [aligned]
            simp only [Concurrency.C23Atomic.Check.Table.source, chosen, Option.getD_some]

/-- `Built` alone supplies all seven structural well-formedness fields. The
finite-spec soundness theorem uses `Shape` for out-of-domain `noReadSource`;
no checker result, execution origin, or legality premise is assumed. -/
theorem Built.wellFormed (mapped : Built inputs orders table) :
    Concurrency.C23Atomic.WellFormed table.toCandidate := by
  refine Concurrency.C23Atomic.Check.WellFormedSpec.sound (table := table)
    ⟨mapped.shape, node_thread_kind mapped, node_initial_unique mapped,
      node_initial_exists mapped, node_rank mapped, node_rank_unique mapped,
      ?_⟩
  intro index
  have supplied := node_source mapped index
  cases read : (table.node index).access.readValue with
  | none => simpa only [read] using supplied
  | some value => simpa only [read] using supplied

end EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph

#audit_edsl
