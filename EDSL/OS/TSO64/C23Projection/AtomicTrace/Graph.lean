/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Initials

/-!
Construct a finite source graph from a supplied initial manifest, atomic event
list, complete managed publication list, and explicit typed interface orders.
Writer identities select RF indices before object/value agreement is checked.
Store issue positions do not supply modification ranks: actual publication
positions do. Unchanged-value stores and RMWs remain distinct modifications.

`Built` is an independently stated finite data correspondence. `build` checks
it on a computed proposal; `certify` additionally invokes the existing sound
C23 atomic-fragment checker. Neither function takes a legality, coherence, or
lookup oracle. Failure supplies no partial graph or claim of a defect.

This module does not establish input origins. A parent must connect the
manifest to successful `Initials.enumerate`, and events and all publications
to the same actual complete trace, with stable initialized objects and logical
thread instances. It must also justify the declared interface orders. There is
no source scanner dependency, MOV-order inference, source/machine preservation,
native/C frontend, or corpus coverage claim here. Ordinary stores are absent
from `AtomicTrace.Event` and are not manufactured as graph events.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
open X86

abbrev SourceEvent := Concurrency.C23Atomic.Event Atomics64.CellId64 Word
abbrev Table := Concurrency.C23Atomic.Check.Table Atomics64.CellId64 Word

/-- Data only. Constructing this record does not establish execution origins. -/
structure Inputs where
  initials : List Initials.Entry
  events : List AtomicTrace.Event
  writes : List PublishedHistory.Stamp

def initialEvent (entry : Initials.Entry) : SourceEvent :=
  ⟨none, entry.identifier, .initialize entry.value⟩

/-- Retain the entire event order, including loads between modifications. -/
def sourceEvents (inputs : Inputs) (orders : Orders) : List SourceEvent :=
  inputs.initials.map initialEvent ++ inputs.events.map (fun event => event.toSource orders)

/-- Positions in this full list are graph indices. A load consumes an index
even though its writer entry is `none`. -/
def writerIds (inputs : Inputs) : List (Option WriterId) :=
  inputs.initials.map (fun entry => some (.initial entry.identifier)) ++
    inputs.events.map AtomicTrace.Event.writer

/-- A buffered publication keeps the issue's thread/occurrence key. An RMW's
identity is its original global action position, including silent actions. -/
def publicationKey (stamp : PublishedHistory.Stamp) : WriterId :=
  match stamp.cause with
  | .buffered tid _ _ occurrence => .store tid occurrence
  | .rmw .. => .rmw stamp.position

/-- The requested identity occurs at this index and at no other live index.
This predicate describes list data, independently of the lookup algorithm. -/
def WriterAt (inputs : Inputs) (key : WriterId) (index : Nat) : Prop :=
  (writerIds inputs)[index]? = some (some key) ∧
    ∀ other : Fin (writerIds inputs).length,
      (writerIds inputs)[other.val]? = some (some key) → other.val = index

instance (inputs : Inputs) (key : WriterId) (index : Nat) :
    Decidable (WriterAt inputs key index) := by
  unfold WriterAt
  infer_instance

/-- Validate cell descriptors against the selected manifest identity. Handles
for the same cell need not be equal; authorization remains an origin obligation.
The RMW payload carries an address rather than a complete cell descriptor. -/
def AtBoundary (inputs : Inputs) (event : AtomicTrace.Event) : Prop :=
  match event.access with
  | .load reference .. | .store reference .. =>
      ∃ initial : Fin inputs.initials.length,
        reference.handle.cell = inputs.initials[initial.val].identifier ∧
        reference.cell = inputs.initials[initial.val].cell
  | .rmw changed _ =>
      ∃ initial : Fin inputs.initials.length,
        changed.cell = inputs.initials[initial.val].identifier ∧
        changed.arithmetic.event.address = inputs.initials[initial.val].cell.address

instance (inputs : Inputs) (event : AtomicTrace.Event) :
    Decidable (AtBoundary inputs event) := by
  unfold AtBoundary
  cases event.access <;> infer_instance

/-- Match the complete publication cause, including the stored word and original
reference. Buffered issue and publication positions must be strictly distinct;
an RMW event and its publication have the same action position. -/
def Publication (event : AtomicTrace.Event) (stamp : PublishedHistory.Stamp) : Prop :=
  match event.access with
  | .load .. => False
  | .store reference value occurrence =>
      stamp.cause = .buffered event.tid reference value occurrence ∧
        event.position < stamp.position
  | .rmw changed _ =>
      stamp.cause = .rmw event.tid changed ∧ stamp.position = event.position

instance (event : AtomicTrace.Event) (stamp : PublishedHistory.Stamp) :
    Decidable (Publication event stamp) := by
  unfold Publication
  cases event.access <;> infer_instance

/-- A read selects the requested writer identity and validates that writer's
object and value. Missing source slots cannot masquerade as `none`. -/
def ReadCorrespondence (inputs : Inputs) (orders : Orders) (table : Table)
    (index : Nat) (event : AtomicTrace.Event) : Prop :=
  match event.source, (event.toSource orders).access.readValue with
  | none, none => table.sources[index]? = some none
  | some key, some value =>
      ∃ writer : table.Index,
        table.sources[index]? = some (some writer.val) ∧
        WriterAt inputs key writer.val ∧
        (table.node writer).object = event.object ∧
        (table.node writer).access.writeValue = some value
  | _, _ => False

instance (inputs : Inputs) (orders : Orders) (table : Table)
    (index : Nat) (event : AtomicTrace.Event) :
    Decidable (ReadCorrespondence inputs orders table index event) := by
  unfold ReadCorrespondence
  cases event.source <;> cases (event.toSource orders).access.readValue <;> infer_instance

/-- Only initializers and loads receive rank zero. Each other rank is one plus
the position of a matching actual publication, rather than its issue position
or its index in the filtered event list. Rank gaps are intentional. -/
def RankCorrespondence (inputs : Inputs) (table : Table)
    (index : Nat) (event : AtomicTrace.Event) : Prop :=
  match event.access with
  | .load .. => table.ranks[index]? = some 0
  | .store .. | .rmw .. =>
      ∃ publication : Fin inputs.writes.length,
        Publication event inputs.writes[publication.val] ∧
        table.ranks[index]? = some (inputs.writes[publication.val].position + 1)

instance (inputs : Inputs) (table : Table) (index : Nat) (event : AtomicTrace.Event) :
    Decidable (RankCorrespondence inputs table index event) := by
  unfold RankCorrespondence
  cases event.access <;> infer_instance

/-- Structural correspondence over finite input and table data, independent of
`proposal`, `build`, and semantic `Legal`. Every supplied publication must be
represented, so an intervening equal-value write cannot be silently omitted.
Duplicate writer keys or publication positions are rejected globally, including
keys that no read happens to use. All table slots are required explicitly. -/
def Built (inputs : Inputs) (orders : Orders) (table : Table) : Prop :=
  table.events = sourceEvents inputs orders ∧
  table.Shape ∧
  ((writerIds inputs).filterMap id).Nodup ∧
  ((inputs.writes.map publicationKey).Nodup ∧
    (inputs.writes.map (fun stamp => stamp.position)).Nodup) ∧
  (∀ initial : Fin inputs.initials.length,
    table.sources[initial.val]? = some none ∧ table.ranks[initial.val]? = some 0) ∧
  (∀ index : Fin inputs.events.length,
    AtBoundary inputs inputs.events[index.val] ∧
    ReadCorrespondence inputs orders table (inputs.initials.length + index.val)
      inputs.events[index.val] ∧
    RankCorrespondence inputs table (inputs.initials.length + index.val)
      inputs.events[index.val]) ∧
  (∀ publication : Fin inputs.writes.length,
    ∃ index : Fin inputs.events.length,
      Publication inputs.events[index.val] inputs.writes[publication.val] ∧
      table.ranks[inputs.initials.length + index.val]? =
        some (inputs.writes[publication.val].position + 1))

instance (inputs : Inputs) (orders : Orders) (table : Table) :
    Decidable (Built inputs orders table) := by
  unfold Built
  infer_instance

def singletonValue {α : Type} : List α → Option α
  | [item] => some item
  | _ => none

/-- Resolve the key in the full index space, never by its payload. Both an
absent key and multiple matching indices return `none`. -/
def writerIndex (identities : List (Option WriterId)) (key : WriterId) : Option Nat :=
  singletonValue ((List.range identities.length).filter fun index =>
    decide (identities[index]? = some (some key)))

/-- Select by identity first. Full cause/value validation is a separate step. -/
def publicationFor (writes : List PublishedHistory.Stamp) (key : WriterId) :
    Option PublishedHistory.Stamp :=
  singletonValue (writes.filter fun stamp => decide (publicationKey stamp = key))

def sourceIndex (identities : List (Option WriterId))
    (event : AtomicTrace.Event) : Option (Option Nat) :=
  match event.source with
  | none => some none
  | some key => (writerIndex identities key).map some

def publicationRank (writes : List PublishedHistory.Stamp)
    (event : AtomicTrace.Event) (key : WriterId) : Option Nat := do
  let stamp ← publicationFor writes key
  if Publication event stamp then some (stamp.position + 1) else none

def eventRank (writes : List PublishedHistory.Stamp)
    (event : AtomicTrace.Event) : Option Nat :=
  match event.access with
  | .load .. => some 0
  | .store .. | .rmw .. => do
      let key ← event.writer
      publicationRank writes event key

/-- Compute all metadata. Required RF and publication lookups propagate failure;
no default index, absent source, or rank substitutes for a failed lookup. This
proposal still needs the independent structural check in `build`. -/
def proposal (inputs : Inputs) (orders : Orders) : Option Table := do
  let sources ← inputs.events.mapM (sourceIndex (writerIds inputs))
  let ranks ← inputs.events.mapM (eventRank inputs.writes)
  pure {
    events := sourceEvents inputs orders
    sources := inputs.initials.map (fun _ => none) ++ sources
    ranks := inputs.initials.map (fun _ => 0) ++ ranks
  }

/-- Build and validate a graph from data alone. This checks structural mapping,
not happens-before, coherence, no-future-RF, or RMW predecessor legality. -/
def build (inputs : Inputs) (orders : Orders) : Option Table :=
  match proposal inputs orders with
  | none => none
  | some table => if Built inputs orders table then some table else none

theorem build_sound {inputs : Inputs} {orders : Orders} {table : Table}
    (success : build inputs orders = some table) : Built inputs orders table := by
  cases proposed : proposal inputs orders with
  | none => simp [build, proposed] at success
  | some candidate =>
      by_cases mapped : Built inputs orders candidate
      · have same : candidate = table := by
          simpa only [build, proposed, ite_eq_left mapped, Option.some.injEq] using success
        subst table
        exact mapped
      · simp [build, proposed, mapped] at success

theorem Built.events_eq {inputs : Inputs} {orders : Orders} {table : Table}
    (mapped : Built inputs orders table) : table.events = sourceEvents inputs orders :=
  mapped.1

theorem Built.shape {inputs : Inputs} {orders : Orders} {table : Table}
    (mapped : Built inputs orders table) : table.Shape :=
  mapped.2.1

theorem Built.writer_keys {inputs : Inputs} {orders : Orders} {table : Table}
    (mapped : Built inputs orders table) : ((writerIds inputs).filterMap id).Nodup :=
  mapped.2.2.1

theorem Built.publication_keys {inputs : Inputs} {orders : Orders} {table : Table}
    (mapped : Built inputs orders table) :
    (inputs.writes.map publicationKey).Nodup ∧
      (inputs.writes.map (fun stamp => stamp.position)).Nodup :=
  mapped.2.2.2.1

theorem Built.initial {inputs : Inputs} {orders : Orders} {table : Table}
    (mapped : Built inputs orders table) (index : Fin inputs.initials.length) :
    table.sources[index.val]? = some none ∧ table.ranks[index.val]? = some 0 :=
  mapped.2.2.2.2.1 index

theorem Built.event {inputs : Inputs} {orders : Orders} {table : Table}
    (mapped : Built inputs orders table) (index : Fin inputs.events.length) :
    AtBoundary inputs inputs.events[index.val] ∧
      ReadCorrespondence inputs orders table (inputs.initials.length + index.val)
        inputs.events[index.val] ∧
      RankCorrespondence inputs table (inputs.initials.length + index.val)
        inputs.events[index.val] :=
  mapped.2.2.2.2.2.1 index

/-- The converse publication coverage, including its numeric rank. -/
theorem Built.publication {inputs : Inputs} {orders : Orders} {table : Table}
    (mapped : Built inputs orders table) (publication : Fin inputs.writes.length) :
    ∃ index : Fin inputs.events.length,
      Publication inputs.events[index.val] inputs.writes[publication.val] ∧
      table.ranks[inputs.initials.length + index.val]? =
        some (inputs.writes[publication.val].position + 1) :=
  mapped.2.2.2.2.2.2 publication

theorem Built.initial_at {inputs : Inputs} {orders : Orders} {table : Table}
    (mapped : Built inputs orders table) (index : Fin inputs.initials.length) :
    table.events[index.val]? = some (initialEvent inputs.initials[index.val]) := by
  rw [mapped.events_eq]
  unfold sourceEvents
  rw [List.getElem?_append_left (by simpa only [List.length_map] using index.isLt)]
  simp only [List.getElem?_map, List.getElem?_eq_getElem index.isLt, Option.map_some]

theorem Built.event_at {inputs : Inputs} {orders : Orders} {table : Table}
    (mapped : Built inputs orders table) (index : Fin inputs.events.length) :
    table.events[inputs.initials.length + index.val]? =
      some (inputs.events[index.val].toSource orders) := by
  rw [mapped.events_eq]
  unfold sourceEvents
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map]
  have aligned : inputs.initials.length + index.val - inputs.initials.length = index.val := by
    omega
  rw [aligned]
  simp only [List.getElem?_map, List.getElem?_eq_getElem index.isLt, Option.map_some]

/-- The exact requested writer key accompanies the semantic RF edge. Even
equal object/value pairs cannot select a different key or ambiguous index. -/
theorem Built.readsFrom {inputs : Inputs} {orders : Orders} {table : Table}
    (mapped : Built inputs orders table) (index : Fin inputs.events.length)
    {key : WriterId} (requested : inputs.events[index.val].source = some key) :
    ∃ writer : table.Index,
      WriterAt inputs key writer.val ∧
      Concurrency.C23Atomic.ReadsFrom table.toCandidate
        (inputs.initials.length + index.val) writer.val := by
  have source := (mapped.event index).2.1
  unfold ReadCorrespondence at source
  rw [requested] at source
  cases loaded : (inputs.events[index.val].toSource orders).access.readValue with
  | none => simp only [loaded] at source
  | some value =>
      rw [loaded] at source
      obtain ⟨writer, chosen, selected, object, stored⟩ := source
      have actualSource : table.source (inputs.initials.length + index.val) =
          some writer.val := by
        simp only [Concurrency.C23Atomic.Check.Table.source, chosen, Option.getD_some]
      refine ⟨writer, selected, actualSource, inputs.events[index.val].object, value, ?_, ?_⟩
      · exact ⟨inputs.events[index.val].toSource orders, mapped.event_at index, rfl, loaded⟩
      · exact ⟨table.node writer, table.node_lookup writer, object, stored⟩

theorem Built.load_rank {inputs : Inputs} {orders : Orders} {table : Table}
    (mapped : Built inputs orders table) (index : Fin inputs.events.length)
    {reference : Queue.ManagedRef} {value : Word} {source : WriterId}
    (loaded : inputs.events[index.val].access = .load reference value source) :
    table.ranks[inputs.initials.length + index.val]? = some 0 := by
  have rank := (mapped.event index).2.2
  simpa only [RankCorrespondence, loaded] using rank

/-- Stores use their complete buffered cause and later publication position. -/
theorem Built.store_rank {inputs : Inputs} {orders : Orders} {table : Table}
    (mapped : Built inputs orders table) (index : Fin inputs.events.length)
    {reference : Queue.ManagedRef} {value : Word} {occurrence : Nat}
    (issued : inputs.events[index.val].access = .store reference value occurrence) :
    ∃ publication : Fin inputs.writes.length,
      inputs.writes[publication.val].cause =
        .buffered inputs.events[index.val].tid reference value occurrence ∧
      inputs.events[index.val].position < inputs.writes[publication.val].position ∧
      table.ranks[inputs.initials.length + index.val]? =
        some (inputs.writes[publication.val].position + 1) := by
  have rank := (mapped.event index).2.2
  unfold RankCorrespondence at rank
  rw [issued] at rank
  obtain ⟨publication, matched, ranked⟩ := rank
  unfold Publication at matched
  rw [issued] at matched
  exact ⟨publication, matched.1, matched.2, ranked⟩

/-- An RMW's full event and thread must match its own actual stamped write. -/
theorem Built.rmw_rank {inputs : Inputs} {orders : Orders} {table : Table}
    (mapped : Built inputs orders table) (index : Fin inputs.events.length)
    {changed : Atomics64.FetchAddEvent} {source : WriterId}
    (changedAt : inputs.events[index.val].access = .rmw changed source) :
    ∃ publication : Fin inputs.writes.length,
      inputs.writes[publication.val].cause = .rmw inputs.events[index.val].tid changed ∧
      inputs.writes[publication.val].position = inputs.events[index.val].position ∧
      table.ranks[inputs.initials.length + index.val]? =
        some (inputs.writes[publication.val].position + 1) := by
  have rank := (mapped.event index).2.2
  unfold RankCorrespondence at rank
  rw [changedAt] at rank
  obtain ⟨publication, matched, ranked⟩ := rank
  unfold Publication at matched
  rw [changedAt] at matched
  exact ⟨publication, matched.1, matched.2, ranked⟩

/-- Propose the graph and HB matrix from the inputs, then use the existing
proved finite checker. No caller-supplied graph or legality premise is needed. -/
def certify (inputs : Inputs) (orders : Orders) : Option Table :=
  match build inputs orders with
  | none => none
  | some table =>
      if Concurrency.C23Atomic.Check.certify table = true then some table else none

/-- Successful certification retains structural mapping and proves exactly the
existing supplied atomic-fragment legality predicate. Input provenance is still
the parent's obligation described in this module's contract. -/
theorem certify_sound {inputs : Inputs} {orders : Orders} {table : Table}
    (success : certify inputs orders = some table) :
    Built inputs orders table ∧ Concurrency.C23Atomic.Legal table.toCandidate := by
  cases built : build inputs orders with
  | none => simp [certify, built] at success
  | some candidate =>
      by_cases checked : Concurrency.C23Atomic.Check.certify candidate = true
      · have same : candidate = table := by
          simpa only [certify, built, ite_eq_left checked, Option.some.injEq] using success
        subst table
        exact ⟨build_sound built, Concurrency.C23Atomic.Check.certify_sound candidate checked⟩
      · simp [certify, built, checked] at success

end EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
