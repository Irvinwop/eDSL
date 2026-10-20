/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Coherence

set_option autoImplicit false

namespace EDSL.Concurrency.C23Atomic.Check

/-- Finite untrusted event, source and rank tables. No graph property is a
constructor premise. Checked shape prevents unused out-of-domain RF entries. -/
structure Table (Location Value : Type) where
  events : List (Event Location Value)
  sources : List (Option Nat)
  ranks : List Nat
  deriving Repr

namespace Table
variable {Location Value : Type}

abbrev Index (table : Table Location Value) := Fin table.events.length

def source (table : Table Location Value) (index : Nat) : Option Nat :=
  (table.sources[index]?).getD none

def rank (table : Table Location Value) (index : Nat) : Nat :=
  (table.ranks[index]?).getD 0

def toCandidate (table : Table Location Value) : Candidate Location Value :=
  ⟨table.events, table.source, table.rank⟩

def node (table : Table Location Value) (index : table.Index) : Event Location Value :=
  table.events[index.val]

def Shape (table : Table Location Value) : Prop :=
  table.sources.length = table.events.length ∧ table.ranks.length = table.events.length

instance (table : Table Location Value) : Decidable table.Shape :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem node_lookup (table : Table Location Value) (index : table.Index) :
    table.toCandidate.events[index.val]? = some (table.node index) :=
  List.getElem?_eq_getElem index.isLt

theorem node_of_lookup (table : Table Location Value) (index : table.Index)
    {event : Event Location Value}
    (live : table.toCandidate.events[index.val]? = some event) : table.node index = event :=
  Option.some.inj ((table.node_lookup index).symm.trans live)

theorem live_index (table : Table Location Value) {index : Nat}
    {event : Event Location Value} (live : table.toCandidate.events[index]? = some event) :
    ∃ actual : table.Index, actual.val = index ∧ table.node actual = event := by
  obtain ⟨bound, equal⟩ := List.getElem_of_getElem? live
  exact ⟨⟨index, bound⟩, rfl, equal⟩

theorem source_outside (table : Table Location Value) (shape : table.Shape)
    {index : Nat} (outside : table.events.length ≤ index) : table.source index = none := by
  have bound : table.sources.length ≤ index := shape.1.symm ▸ outside
  simp only [source, List.getElem?_eq_none bound, Option.getD_none]

theorem reads_iff (table : Table Location Value) (index : table.Index)
    (location : Location) (value : Value) :
    Reads table.toCandidate index.val location value ↔
      (table.node index).object = location ∧ (table.node index).access.readValue = some value := by
  constructor
  · rintro ⟨event, live, object, loaded⟩
    rw [table.node_of_lookup index live]
    exact ⟨object, loaded⟩
  · rintro ⟨object, loaded⟩
    exact ⟨table.node index, table.node_lookup index, object, loaded⟩

theorem writes_iff (table : Table Location Value) (index : table.Index)
    (location : Location) (value : Value) :
    Writes table.toCandidate index.val location value ↔
      (table.node index).object = location ∧ (table.node index).access.writeValue = some value := by
  constructor
  · rintro ⟨event, live, object, stored⟩
    rw [table.node_of_lookup index live]
    exact ⟨object, stored⟩
  · rintro ⟨object, stored⟩
    exact ⟨table.node index, table.node_lookup index, object, stored⟩

theorem reads_bound (table : Table Location Value) {index : Nat}
    {location : Location} {value : Value} (read : Reads table.toCandidate index location value) :
    index < table.events.length := by
  obtain ⟨_, live, _, _⟩ := read
  exact (List.getElem_of_getElem? live).1

theorem writes_bound (table : Table Location Value) {index : Nat}
    {location : Location} {value : Value} (written : Writes table.toCandidate index location value) :
    index < table.events.length := by
  obtain ⟨_, live, _, _⟩ := written
  exact (List.getElem_of_getElem? live).1

end Table
end EDSL.Concurrency.C23Atomic.Check
