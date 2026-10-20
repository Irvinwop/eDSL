/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Model

/-!
Initial values at an already-initialized stable-object boundary come from the
complete live registry and its current published RAM. This module supplies no
C `atomic_init`/lifecycle semantics, memory orders, or native/source preservation
claim. Registry bounds are justified by `Atomics64.WellFormed` when completeness
for every live identifier is required.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace.Initials
open X86

/-- One live descriptor and the exact qword read at the initial boundary. -/
structure Entry where
  identifier : Atomics64.CellId64
  cell : Atomics64.Cell
  value : X86.Word
  deriving DecidableEq, Repr

private def scan (world : World) : List Nat → Except TSO64.Fault (List Entry)
  | [] => .ok []
  | index :: rest =>
      match world.cells ⟨index⟩ with
      | none => scan world rest
      | some cell => do
          let value ← (loadQWord (published world) cell.address).mapError TSO64.Fault.machine
          let entries ← scan world rest
          pure (⟨⟨index⟩, cell, value⟩ :: entries)

/-- Scan the entire allocated identifier interval in increasing order. Only
absent cells are skipped; the first failed live-cell read returns its exact
machine fault. Callers supply neither an object subset nor initial values. -/
def enumerate (world : World) : Except TSO64.Fault (List Entry) :=
  scan world (List.range world.nextCell)

private theorem scan_cons_live {world : World} {index : Nat} {rest : List Nat}
    {cell : Atomics64.Cell} {entries : List Entry}
    (live : world.cells ⟨index⟩ = some cell)
    (success : scan world (index :: rest) = .ok entries) :
    ∃ value tail, loadQWord (published world) cell.address = .ok value ∧
      scan world rest = .ok tail ∧ entries = ⟨⟨index⟩, cell, value⟩ :: tail := by
  cases read : loadQWord (published world) cell.address with
  | error fault => simp [scan, live, read, Except.mapError] at success
  | ok value =>
      cases scanned : scan world rest with
      | error fault => simp [scan, live, read, scanned, Except.mapError] at success
      | ok tail =>
          have same : (⟨⟨index⟩, cell, value⟩ : Entry) :: tail = entries := by
            simpa [scan, live, read, scanned, Except.mapError] using success
          exact ⟨value, tail, rfl, rfl, same.symm⟩

private theorem scan_spec (world : World) (indices : List Nat) :
    ∀ {entries : List Entry}, scan world indices = .ok entries →
      (∀ entry, entry ∈ entries ↔ entry.identifier.index ∈ indices ∧
        world.cells entry.identifier = some entry.cell ∧
        loadQWord (published world) entry.cell.address = .ok entry.value) ∧
      entries.map (fun entry => entry.identifier.index) =
        indices.filter (fun index => (world.cells ⟨index⟩).isSome) := by
  induction indices with
  | nil =>
      intro entries success
      have same : ([] : List Entry) = entries := Except.ok.inj success
      subst entries
      exact ⟨by intro entry; simp, rfl⟩
  | cons index rest ih =>
      intro entries success
      cases selected : world.cells ⟨index⟩ with
      | none =>
          have tailSuccess : scan world rest = .ok entries := by
            simpa only [scan, selected] using success
          obtain ⟨members, identifiers⟩ := ih tailSuccess
          constructor
          · intro entry
            constructor
            · intro member
              obtain ⟨inside, live, read⟩ := (members entry).mp member
              exact ⟨List.mem_cons_of_mem _ inside, live, read⟩
            · rintro ⟨inside, live, read⟩
              rcases List.mem_cons.mp inside with atHead | inTail
              · have sameIdentifier : entry.identifier = ⟨index⟩ :=
                  congrArg Atomics64.CellId64.mk atHead
                rw [sameIdentifier, selected] at live
                cases live
              · exact (members entry).mpr ⟨inTail, live, read⟩
          · simpa [List.filter_cons, selected] using identifiers
      | some cell =>
          obtain ⟨value, tail, read, tailSuccess, same⟩ := scan_cons_live selected success
          subst entries
          obtain ⟨members, identifiers⟩ := ih tailSuccess
          constructor
          · intro entry
            constructor
            · intro member
              rcases List.mem_cons.mp member with atHead | inTail
              · subst entry
                exact ⟨List.mem_cons_self, selected, read⟩
              · obtain ⟨inside, live, loaded⟩ := (members entry).mp inTail
                exact ⟨List.mem_cons_of_mem _ inside, live, loaded⟩
            · rintro ⟨inside, live, loaded⟩
              rcases List.mem_cons.mp inside with atHead | inTail
              · have sameIdentifier : entry.identifier = ⟨index⟩ :=
                  congrArg Atomics64.CellId64.mk atHead
                have sameCell : entry.cell = cell := by
                  rw [sameIdentifier, selected] at live
                  exact (Option.some.inj live).symm
                have sameValue : entry.value = value := by
                  rw [sameCell, read] at loaded
                  exact (Except.ok.inj loaded).symm
                have sameEntry : entry = ⟨⟨index⟩, cell, value⟩ := by
                  calc
                    entry = ⟨entry.identifier, entry.cell, entry.value⟩ := rfl
                    _ = ⟨⟨index⟩, cell, value⟩ := by
                      rw [sameIdentifier, sameCell, sameValue]
                exact List.mem_cons.mpr (.inl sameEntry)
              · exact List.mem_cons.mpr (.inr ((members entry).mpr ⟨inTail, live, loaded⟩))
          · simpa [List.filter_cons, selected] using congrArg (List.cons index) identifiers

/-- Successful membership has the exact registry bound, live descriptor and
current RAM value, even without a well-formedness assumption. -/
theorem enumerate_mem_iff {world : World} {entries : List Entry}
    (success : enumerate world = .ok entries) (entry : Entry) :
    entry ∈ entries ↔ entry.identifier.index < world.nextCell ∧
      world.cells entry.identifier = some entry.cell ∧
      loadQWord (published world) entry.cell.address = .ok entry.value := by
  simpa only [List.mem_range] using
    (scan_spec world (List.range world.nextCell) success).1 entry

/-- Every emitted entry names an actual live descriptor and its exact RAM word. -/
theorem enumerate_sound {world : World} {entries : List Entry} {entry : Entry}
    (success : enumerate world = .ok entries) (member : entry ∈ entries) :
    world.cells entry.identifier = some entry.cell ∧
      loadQWord (published world) entry.cell.address = .ok entry.value :=
  ((enumerate_mem_iff success entry).mp member).2

theorem enumerate_id_bound {world : World} {entries : List Entry} {entry : Entry}
    (success : enumerate world = .ok entries) (member : entry ∈ entries) :
    entry.identifier.index < world.nextCell :=
  ((enumerate_mem_iff success entry).mp member).1

/-- No live registered object with its actual readable value is omitted. -/
theorem enumerate_complete {world : World} {entries : List Entry}
    {identifier : Atomics64.CellId64} {cell : Atomics64.Cell} {value : Word}
    (valid : Atomics64.WellFormed world) (success : enumerate world = .ok entries)
    (live : world.cells identifier = some cell)
    (read : loadQWord (published world) cell.address = .ok value) :
    (⟨identifier, cell, value⟩ : Entry) ∈ entries :=
  (enumerate_mem_iff success ⟨identifier, cell, value⟩).mpr
    ⟨(valid.cells identifier cell live).1, live, read⟩

/-- In a well-formed world the finite scan covers every live identifier. -/
theorem enumerate_live_iff {world : World} {entries : List Entry}
    (valid : Atomics64.WellFormed world) (success : enumerate world = .ok entries)
    (entry : Entry) :
    entry ∈ entries ↔ world.cells entry.identifier = some entry.cell ∧
      loadQWord (published world) entry.cell.address = .ok entry.value := by
  constructor
  · exact enumerate_sound success
  · rintro ⟨live, read⟩
    exact enumerate_complete valid success live read

/-- Identifiers are exactly the live part of the complete numeric interval. -/
theorem enumerate_identifiers {world : World} {entries : List Entry}
    (success : enumerate world = .ok entries) :
    entries.map (fun entry => entry.identifier.index) =
      (List.range world.nextCell).filter (fun index => (world.cells ⟨index⟩).isSome) :=
  (scan_spec world (List.range world.nextCell) success).2

/-- Enumeration preserves strictly increasing numeric identifier order. -/
theorem enumerate_ordered {world : World} {entries : List Entry}
    (success : enumerate world = .ok entries) :
    entries.Pairwise (fun first second => first.identifier.index < second.identifier.index) := by
  have ordered : (entries.map (fun entry => entry.identifier.index)).Pairwise (fun a b => a < b) := by
    rw [enumerate_identifiers success]
    exact (List.pairwise_lt_range (n := world.nextCell)).filter
      (fun index => (world.cells ⟨index⟩).isSome)
  exact List.pairwise_map.mp ordered

/-- Each cell identity occurs once, including when distinct cells hold equal words. -/
theorem enumerate_identifiers_nodup {world : World} {entries : List Entry}
    (success : enumerate world = .ok entries) :
    (entries.map Entry.identifier).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.pairwise_map.mpr
  exact (enumerate_ordered success).imp (fun less same => by
    have equal := congrArg Atomics64.CellId64.index same
    rw [equal] at less
    exact Nat.lt_irrefl _ less)

theorem enumerate_nodup {world : World} {entries : List Entry}
    (success : enumerate world = .ok entries) : entries.Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  exact (enumerate_ordered success).imp (fun less same => by
    rw [same] at less
    exact Nat.lt_irrefl _ less)

private theorem scan_success (world : World) (indices : List Nat)
    (readable : ∀ identifier cell, world.cells identifier = some cell →
      ∃ value, loadQWord (published world) cell.address = .ok value) :
    ∃ entries, scan world indices = .ok entries := by
  induction indices with
  | nil => exact ⟨[], rfl⟩
  | cons index rest ih =>
      obtain ⟨tail, tailSuccess⟩ := ih
      cases live : world.cells ⟨index⟩ with
      | none => exact ⟨tail, by simpa only [scan, live] using tailSuccess⟩
      | some cell =>
          obtain ⟨value, read⟩ := readable ⟨index⟩ cell live
          exact ⟨⟨⟨index⟩, cell, value⟩ :: tail,
            by simp [scan, live, read, tailSuccess, Except.mapError]⟩

/-- Current `ValidCell` resources enable all reads, so enumeration succeeds
for every well-formed world without a separate caller-supplied value table. -/
theorem enumerate_success {world : World} (valid : Atomics64.WellFormed world) :
    ∃ entries, enumerate world = .ok entries := by
  exact scan_success world (List.range world.nextCell)
    (fun identifier cell live => (valid.cells identifier cell live).2.1.load_exists)

private theorem scan_error (world : World) (indices : List Nat) :
    ∀ {fault : TSO64.Fault}, scan world indices = .error fault →
      ∃ (identifier : Atomics64.CellId64) (cell : Atomics64.Cell) (error : X86.Error),
        identifier.index ∈ indices ∧ world.cells identifier = some cell ∧
        loadQWord (published world) cell.address = .error error ∧
        fault = TSO64.Fault.machine error := by
  induction indices with
  | nil =>
      intro fault failed
      simp [scan] at failed
  | cons index rest ih =>
      intro fault failed
      cases live : world.cells ⟨index⟩ with
      | none =>
          have tailFailure : scan world rest = .error fault := by
            simpa only [scan, live] using failed
          obtain ⟨identifier, cell, error, inside, descriptor, read, same⟩ := ih tailFailure
          exact ⟨identifier, cell, error, List.mem_cons_of_mem _ inside, descriptor, read, same⟩
      | some cell =>
          cases read : loadQWord (published world) cell.address with
          | error error =>
              have same : TSO64.Fault.machine error = fault := by
                simpa [scan, live, read, Except.mapError] using failed
              exact ⟨⟨index⟩, cell, error, List.mem_cons_self, live, read, same.symm⟩
          | ok value =>
              cases scanned : scan world rest with
              | ok tail => simp [scan, live, read, scanned, Except.mapError] at failed
              | error tailFault =>
                  have sameFault : tailFault = fault := by
                    simpa [scan, live, read, scanned, Except.mapError] using failed
                  subst fault
                  obtain ⟨identifier, descriptor, error, inside, found, loaded, same⟩ := ih scanned
                  exact ⟨identifier, descriptor, error, List.mem_cons_of_mem _ inside,
                    found, loaded, same⟩

/-- Every reported failure is the unchanged machine error of an actual live
cell read in the scanned interval; failed reads are never treated as absence. -/
theorem enumerate_error {world : World} {fault : TSO64.Fault}
    (failed : enumerate world = .error fault) :
    ∃ (identifier : Atomics64.CellId64) (cell : Atomics64.Cell) (error : X86.Error),
      identifier.index < world.nextCell ∧ world.cells identifier = some cell ∧
      loadQWord (published world) cell.address = .error error ∧
      fault = TSO64.Fault.machine error := by
  simpa only [List.mem_range] using scan_error world (List.range world.nextCell) failed

end EDSL.OS.TSO64.C23Projection.AtomicTrace.Initials
