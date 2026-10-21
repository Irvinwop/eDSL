/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph

/-!
Completeness of the existing finite graph builder from pure input adequacy.
`InputsReady` describes unique input keys, exact RF object/value witnesses,
manifest boundaries, and both directions of publication coverage. It contains
no table, computed metadata, legality, or checker-success premise.

The proofs follow the existing singleton lookups and both metadata `mapM`
passes. They establish every slot and every `Built` check before using the
unchanged `build`. Publication positions, including gaps, remain the ranks'
source. Orders are arbitrary typed interface annotations.

This module does not establish actual scan origins, native execution, semantic
legality, or corpus coverage. A caller must independently derive `InputsReady`
from its inputs' provenance before using this pure completeness result.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
open X86

/-- Pure input data adequacy, independent of any proposed or checked table. -/
structure InputsReady (inputs : Inputs) (orders : Orders) : Prop where
  writerKeys : ((writerIds inputs).filterMap id).Nodup
  publicationKeys : (inputs.writes.map publicationKey).Nodup
  publicationPositions : (inputs.writes.map (fun stamp => stamp.position)).Nodup
  boundary : ∀ slot : Fin inputs.events.length, AtBoundary inputs inputs.events[slot.val]
  reads : ∀ (slot : Fin inputs.events.length) (key : WriterId) (value : Word),
    inputs.events[slot.val].source = some key →
    (inputs.events[slot.val].toSource orders).access.readValue = some value →
    ∃ writer : Fin (sourceEvents inputs orders).length,
      WriterAt inputs key writer.val ∧
      (sourceEvents inputs orders)[writer.val].object = inputs.events[slot.val].object ∧
      (sourceEvents inputs orders)[writer.val].access.writeValue = some value
  writes : ∀ slot : Fin inputs.events.length,
    inputs.events[slot.val].writer.isSome = true →
    ∃ publication : Fin inputs.writes.length,
      Publication inputs.events[slot.val] inputs.writes[publication.val]
  complete : ∀ publication : Fin inputs.writes.length,
    ∃ slot : Fin inputs.events.length,
      Publication inputs.events[slot.val] inputs.writes[publication.val]

/-! Singleton selection uses input key uniqueness, not payload equality. -/

private theorem filter_key_singleton {α β : Type} [DecidableEq β]
    (key : α → β) (items : List α) :
    (items.map key).Nodup → ∀ item, item ∈ items →
      items.filter (fun other => decide (key other = key item)) = [item] := by
  induction items with
  | nil =>
      intro _ item member
      cases member
  | cons head tail ih =>
      intro unique item member
      have fresh : key head ∉ tail.map key ∧ (tail.map key).Nodup := by
        simpa only [List.map_cons, List.nodup_cons] using unique
      rcases List.mem_cons.mp member with same | member
      · subst item
        have absent : tail.filter (fun other => decide (key other = key head)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro other member accepted
          exact fresh.1 (List.mem_map.mpr
            ⟨other, member, of_decide_eq_true accepted⟩)
        simp [absent]
      · have different : key head ≠ key item := by
          intro same
          exact fresh.1 (List.mem_map.mpr ⟨item, member, same.symm⟩)
        simpa [List.filter_cons, different] using ih fresh.2 item member

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

/-- A present live key in a unique input key list selects its full-list index. -/
theorem writerIndex_of_unique_keys {identities : List (Option WriterId)}
    (unique : (identities.filterMap id).Nodup) {key : WriterId} {index : Nat}
    (present : identities[index]? = some (some key)) :
    writerIndex identities key = some index := by
  have bound := (List.getElem_of_getElem? present).1
  have equivalent :
      (List.range identities.length).filter
          (fun other => decide (identities[other]? = some (some key))) =
        (List.range identities.length).filter (fun other => decide (other = index)) := by
    apply List.filter_congr
    intro other _
    by_cases same : other = index
    · subst other
      simp [present]
    · have absent : identities[other]? ≠ some (some key) := by
        intro found
        exact same (some_key_index unique found present)
      simp [same, absent]
  have single :
      (List.range identities.length).filter (fun other => decide (other = index)) =
        [index] :=
    filter_key_singleton id (List.range identities.length)
      (by simpa only [List.map_id] using (List.nodup_range (n := identities.length)))
      index (List.mem_range.mpr bound)
  unfold writerIndex
  rw [equivalent, single]
  rfl

/-- A supplied publication's unique key selects that exact complete stamp. -/
theorem publicationFor_of_unique_keys {writes : List PublishedHistory.Stamp}
    (unique : (writes.map publicationKey).Nodup) (slot : Fin writes.length) :
    publicationFor writes (publicationKey writes[slot.val]) = some writes[slot.val] := by
  have single := filter_key_singleton publicationKey writes unique writes[slot.val]
    (List.getElem_mem slot.isLt)
  unfold publicationFor
  rw [single]
  rfl

private theorem event_read_cases (event : AtomicTrace.Event) (orders : Orders) :
    (event.source = none ∧ (event.toSource orders).access.readValue = none) ∨
    (∃ (key : WriterId) (value : Word),
      event.source = some key ∧ (event.toSource orders).access.readValue = some value) := by
  cases access : event.access <;>
    simp [AtomicTrace.Event.source, AtomicTrace.Event.toSource, access,
      Concurrency.C23Atomic.Access.readValue]

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

private theorem eventRank_of_publication {writes : List PublishedHistory.Stamp}
    {event : AtomicTrace.Event} (unique : (writes.map publicationKey).Nodup)
    (slot : Fin writes.length) (matched : Publication event writes[slot.val]) :
    eventRank writes event = some (writes[slot.val].position + 1) := by
  have writer := publication_writer matched
  have chosen := publicationFor_of_unique_keys unique slot
  cases access : event.access with
  | load reference value source => simp only [Publication, access] at matched
  | store reference value occurrence =>
      simp [eventRank, access, writer, publicationRank, chosen, matched]
  | rmw changed source =>
      simp [eventRank, access, writer, publicationRank, chosen, matched]

private theorem ready_source_total {inputs : Inputs} {orders : Orders}
    (ready : InputsReady inputs orders) (slot : Fin inputs.events.length) :
    ∃ source, sourceIndex (writerIds inputs) inputs.events[slot.val] = some source := by
  rcases event_read_cases inputs.events[slot.val] orders with missing |
      ⟨key, value, requested, loaded⟩
  · exact ⟨none, by simp only [sourceIndex, missing.1]⟩
  · obtain ⟨writer, selected, _object, _stored⟩ :=
      ready.reads slot key value requested loaded
    have chosen := writerIndex_of_unique_keys ready.writerKeys selected.1
    exact ⟨some writer.val, by simp only [sourceIndex, requested, chosen, Option.map_some]⟩

private theorem ready_rank_total {inputs : Inputs} {orders : Orders}
    (ready : InputsReady inputs orders) (slot : Fin inputs.events.length) :
    ∃ rank, eventRank inputs.writes inputs.events[slot.val] = some rank := by
  cases access : inputs.events[slot.val].access with
  | load reference value source =>
      exact ⟨0, by simp only [eventRank, access]⟩
  | store reference value occurrence =>
      have writing : inputs.events[slot.val].writer.isSome = true := by
        simp only [AtomicTrace.Event.writer, access, Option.isSome_some]
      obtain ⟨publication, matched⟩ := ready.writes slot writing
      exact ⟨_, eventRank_of_publication ready.publicationKeys publication matched⟩
  | rmw changed source =>
      have writing : inputs.events[slot.val].writer.isSome = true := by
        simp only [AtomicTrace.Event.writer, access, Option.isSome_some]
      obtain ⟨publication, matched⟩ := ready.writes slot writing
      exact ⟨_, eventRank_of_publication ready.publicationKeys publication matched⟩

/-! Successful `mapM` passes preserve lengths and all exact metadata slots. -/

private theorem mapM_complete {α β : Type} (resolve : α → Option β) (items : List α) :
    (∀ item, item ∈ items → ∃ value, resolve item = some value) →
    ∃ values, items.mapM resolve = some values ∧ values.length = items.length ∧
      ∀ slot : Fin items.length, values[slot.val]? = resolve items[slot.val] := by
  induction items with
  | nil =>
      intro _
      refine ⟨[], rfl, rfl, ?_⟩
      intro slot
      exact Fin.elim0 slot
  | cons head tail ih =>
      intro total
      obtain ⟨value, chosen⟩ := total head (by simp)
      obtain ⟨values, remaining, lengths, slots⟩ :=
        ih (fun item member => total item (List.mem_cons_of_mem head member))
      refine ⟨value :: values, ?_, ?_, ?_⟩
      · simp [List.mapM_cons, chosen, remaining]
      · simp only [List.length_cons, lengths]
      · intro slot
        rcases slot with ⟨index, within⟩
        cases index with
        | zero =>
            simpa only [List.getElem?_cons_zero, List.getElem_cons_zero]
              using chosen.symm
        | succ index =>
            have bound : index < tail.length := by
              simp only [List.length_cons] at within
              omega
            simpa only [List.getElem?_cons_succ, List.getElem_cons_succ]
              using slots ⟨index, bound⟩

private theorem prefix_slot {α β : Type} (front : List α) (value : β)
    (suffix : List β) (slot : Fin front.length) :
    (front.map (fun _ => value) ++ suffix)[slot.val]? = some value := by
  rw [List.getElem?_append_left (by simpa only [List.length_map] using slot.isLt)]
  simp only [List.getElem?_map, List.getElem?_eq_getElem slot.isLt, Option.map_some]

private theorem suffix_slot {α β : Type} (front : List α) (project : α → β)
    (suffix : List β) (index : Nat) :
    (front.map project ++ suffix)[front.length + index]? = suffix[index]? := by
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  have aligned : front.length + index - front.length = index := by omega
  simp only [List.length_map, aligned]

private structure ProposalRows (inputs : Inputs) (orders : Orders) (table : Table) : Prop where
  events : table.events = sourceEvents inputs orders
  shape : table.Shape
  initial : ∀ slot : Fin inputs.initials.length,
    table.sources[slot.val]? = some none ∧ table.ranks[slot.val]? = some 0
  sources : ∀ slot : Fin inputs.events.length,
    table.sources[inputs.initials.length + slot.val]? =
      sourceIndex (writerIds inputs) inputs.events[slot.val]
  ranks : ∀ slot : Fin inputs.events.length,
    table.ranks[inputs.initials.length + slot.val]? =
      eventRank inputs.writes inputs.events[slot.val]

private theorem proposal_rows {inputs : Inputs} {orders : Orders}
    (ready : InputsReady inputs orders) :
    ∃ table, proposal inputs orders = some table ∧ ProposalRows inputs orders table := by
  obtain ⟨sources, sourceSuccess, sourceLength, sourceRows⟩ :=
    mapM_complete (sourceIndex (writerIds inputs)) inputs.events (by
      intro event member
      obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
      simpa only [same] using ready_source_total ready ⟨index, bound⟩)
  obtain ⟨ranks, rankSuccess, rankLength, rankRows⟩ :=
    mapM_complete (eventRank inputs.writes) inputs.events (by
      intro event member
      obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
      simpa only [same] using ready_rank_total ready ⟨index, bound⟩)
  let table : Table := {
    events := sourceEvents inputs orders
    sources := inputs.initials.map (fun _ => none) ++ sources
    ranks := inputs.initials.map (fun _ => 0) ++ ranks
  }
  refine ⟨table, ?_, ?_⟩
  · simp [proposal, sourceSuccess, rankSuccess, table]
  · refine {
      events := rfl
      shape := ?_
      initial := ?_
      sources := ?_
      ranks := ?_
    }
    · change
        (inputs.initials.map (fun _ => (none : Option Nat)) ++ sources).length =
            (sourceEvents inputs orders).length ∧
          (inputs.initials.map (fun _ => (0 : Nat)) ++ ranks).length =
            (sourceEvents inputs orders).length
      constructor
      · simp only [sourceEvents, List.length_append, List.length_map, sourceLength]
      · simp only [sourceEvents, List.length_append, List.length_map, rankLength]
    · intro slot
      exact ⟨prefix_slot inputs.initials none sources slot,
        prefix_slot inputs.initials 0 ranks slot⟩
    · intro slot
      exact (suffix_slot inputs.initials (fun _ => none) sources slot.val).trans
        (sourceRows slot)
    · intro slot
      exact (suffix_slot inputs.initials (fun _ => 0) ranks slot.val).trans (rankRows slot)

/-! Discharge the independent structural check from the actual proposal rows. -/

private theorem rows_readCorrespondence {inputs : Inputs} {orders : Orders}
    {table : Table} (rows : ProposalRows inputs orders table)
    (ready : InputsReady inputs orders) (slot : Fin inputs.events.length) :
    ReadCorrespondence inputs orders table (inputs.initials.length + slot.val)
      inputs.events[slot.val] := by
  rcases event_read_cases inputs.events[slot.val] orders with missing |
      ⟨key, value, requested, loaded⟩
  · simpa only [ReadCorrespondence, missing.1, missing.2, sourceIndex]
      using rows.sources slot
  · obtain ⟨writer, selected, object, stored⟩ := ready.reads slot key value requested loaded
    let tableWriter : table.Index := ⟨writer.val, by
      change writer.val < table.events.length
      rw [rows.events]
      exact writer.isLt⟩
    have sameNode : table.node tableWriter = (sourceEvents inputs orders)[writer.val] := by
      simp only [Concurrency.C23Atomic.Check.Table.node, rows.events, tableWriter]
    have chosen := writerIndex_of_unique_keys ready.writerKeys selected.1
    have source : table.sources[inputs.initials.length + slot.val]? = some (some writer.val) := by
      simpa only [sourceIndex, requested, chosen, Option.map_some] using rows.sources slot
    unfold ReadCorrespondence
    rw [requested, loaded]
    exact ⟨tableWriter, source, selected,
      by simpa only [sameNode] using object,
      by simpa only [sameNode] using stored⟩

private theorem rows_rankCorrespondence {inputs : Inputs} {orders : Orders}
    {table : Table} (rows : ProposalRows inputs orders table)
    (ready : InputsReady inputs orders) (slot : Fin inputs.events.length) :
    RankCorrespondence inputs table (inputs.initials.length + slot.val)
      inputs.events[slot.val] := by
  cases access : inputs.events[slot.val].access with
  | load reference value source =>
      simpa only [RankCorrespondence, access, eventRank] using rows.ranks slot
  | store reference value occurrence =>
      simp only [RankCorrespondence, access]
      have writing : inputs.events[slot.val].writer.isSome = true := by
        simp only [AtomicTrace.Event.writer, access, Option.isSome_some]
      obtain ⟨publication, matched⟩ := ready.writes slot writing
      exact ⟨publication, matched,
        (rows.ranks slot).trans (eventRank_of_publication ready.publicationKeys publication matched)⟩
  | rmw changed source =>
      simp only [RankCorrespondence, access]
      have writing : inputs.events[slot.val].writer.isSome = true := by
        simp only [AtomicTrace.Event.writer, access, Option.isSome_some]
      obtain ⟨publication, matched⟩ := ready.writes slot writing
      exact ⟨publication, matched,
        (rows.ranks slot).trans (eventRank_of_publication ready.publicationKeys publication matched)⟩

private theorem rows_built {inputs : Inputs} {orders : Orders} {table : Table}
    (rows : ProposalRows inputs orders table) (ready : InputsReady inputs orders) :
    Built inputs orders table := by
  refine ⟨rows.events, rows.shape, ready.writerKeys,
    ⟨ready.publicationKeys, ready.publicationPositions⟩, rows.initial, ?_, ?_⟩
  · intro slot
    exact ⟨ready.boundary slot, rows_readCorrespondence rows ready slot,
      rows_rankCorrespondence rows ready slot⟩
  · intro publication
    obtain ⟨slot, matched⟩ := ready.complete publication
    exact ⟨slot, matched,
      (rows.ranks slot).trans (eventRank_of_publication ready.publicationKeys publication matched)⟩

/-- The existing executable proposal succeeds and satisfies all independent
`Built` obligations when its finite input data are adequate. -/
theorem proposal_complete {inputs : Inputs} {orders : Orders}
    (ready : InputsReady inputs orders) :
    ∃ table, proposal inputs orders = some table ∧ Built inputs orders table := by
  obtain ⟨table, proposed, rows⟩ := proposal_rows ready
  exact ⟨table, proposed, rows_built rows ready⟩

/-- The existing builder returns a fully `Built` table from pure input adequacy.
Its structural check is retained and proved to accept the computed proposal. -/
theorem build_complete {inputs : Inputs} {orders : Orders}
    (ready : InputsReady inputs orders) :
    ∃ table, build inputs orders = some table ∧ Built inputs orders table := by
  obtain ⟨table, proposed, mapped⟩ := proposal_complete ready
  refine ⟨table, ?_, mapped⟩
  simp only [build, proposed, ite_eq_left mapped]

end EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph

#audit_edsl
