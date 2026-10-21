/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.ReadSource
import EDSL.OS.TSO64.WordProjection.Locations

/-!
Ordering of actual newest-qword selections in the typed oldest-first mixed
FIFO. The production selector remains StoreBuffer.Mixed.newestQWord. Snapshot
indices and persistent managed occurrences remain distinct. Occurrence order
comes from Cursor.Ordered, including gaps consumed by ordinary enqueues.

The structural results select exact-address whole qwords only. They do not
ignore partial overlaps in the byte overlay, authorize a load or publication,
or identify persistent cells from addresses. Resource-derived managed selection
and cell identity require their explicit current-authority/WF premises below.
These results establish no pending-versus-published global rank, release view
transfer, execution-history origin for initial entries, or C23Atomic.Legal.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.Queue.SelectionOrder
open X86 StoreBuffer.Mixed

private theorem payload_at {entries : List Entry} {index : Nat} {entry : Entry}
    (selected : entries[index]? = some entry) :
    (payload entries)[index]? = some entry.store := by
  simp only [payload, List.getElem?_map, selected, Option.map_some]

/-- A missing production selector excludes exact-address qword entries. This
is only a lookup fact; overlapping partial stores require separate resources. -/
private theorem missing_no_qword {buffer : Buffer} {address value : Word} {index : Nat}
    (missing : newestQWord buffer address = none)
    (selected : buffer[index]? = some ⟨address, .qword value⟩) : False := by
  induction buffer generalizing index with
  | nil => simp at selected
  | cons head tail ih =>
    have tailMissing : newestQWord tail address = none := by
      cases found : newestQWord tail address with
      | none => rfl
      | some origin => simp only [newestQWord, found, Option.some_ne_none] at missing
    cases index with
    | zero =>
      have equal : head = ⟨address, .qword value⟩ := Option.some.inj selected
      subst head
      simp [newestQWord, tailMissing] at missing
    | succ index => exact ih tailMissing selected

/-- Strict FIFO index order induces strict persistent occurrence order across
managed entries, even when ordinary entries occur between them. -/
private theorem managed_index_lt {entries : List Entry}
    (ordered : (occurrences entries).Pairwise (fun first second => first < second))
    {first last : Nat} {left right : ManagedRef} {leftValue rightValue : Word}
    {leftOccurrence rightOccurrence : Nat}
    (leftAt : entries[first]? = some (.managed left leftValue leftOccurrence))
    (rightAt : entries[last]? = some (.managed right rightValue rightOccurrence))
    (earlier : first < last) : leftOccurrence < rightOccurrence := by
  induction entries generalizing first last with
  | nil => simp at leftAt
  | cons head tail ih =>
    cases first with
    | zero =>
      have equal : head = .managed left leftValue leftOccurrence := Option.some.inj leftAt
      subst head
      cases last with
      | zero => omega
      | succ last =>
        have member : .managed right rightValue rightOccurrence ∈ tail :=
          List.mem_of_getElem? rightAt
        exact (List.pairwise_cons.mp ordered).1 rightOccurrence
          (managed_mem_occurrences tail right rightValue rightOccurrence member)
    | succ first =>
      cases last with
      | zero => omega
      | succ last =>
        have tailOrdered : (occurrences tail).Pairwise (fun first second => first < second) := by
          cases head with
          | ordinary ticket store => exact ordered
          | managed reference value occurrence => exact (List.pairwise_cons.mp ordered).2
        exact ih tailOrdered leftAt rightAt (by omega)

/-- One worker occurrence identifies the entire managed entry and its exact
snapshot position. Equal payloads or handle aliases do not identify a tag. -/
theorem occurrence_unique {cursor : Cursor} (ordered : cursor.Ordered)
    {first last : Nat} {left right : ManagedRef} {leftValue rightValue : Word}
    {occurrence : Nat}
    (leftAt : cursor.pending[first]? = some (.managed left leftValue occurrence))
    (rightAt : cursor.pending[last]? = some (.managed right rightValue occurrence)) :
    first = last ∧ left = right ∧ leftValue = rightValue := by
  have sameIndex : first = last := by
    by_cases earlier : first < last
    · have impossible := managed_index_lt ordered.1 leftAt rightAt earlier
      exact False.elim (Nat.lt_irrefl _ impossible)
    · by_cases later : last < first
      · have impossible := managed_index_lt ordered.1 rightAt leftAt later
        exact False.elim (Nat.lt_irrefl _ impossible)
      · omega
  subst last
  have equal : Entry.managed left leftValue occurrence = .managed right rightValue occurrence :=
    Option.some.inj (leftAt.symm.trans rightAt)
  cases equal
  exact ⟨rfl, rfl, rfl⟩

/-- A production newest-qword position dominates every managed entry with the
same physical qword start. This is independent of compatibility or authority;
it asserts nothing about partially overlapping stores in the actual overlay. -/
theorem index_maximal {cursor : Cursor} {address : Word} {origin : QWordOrigin}
    (found : newestQWord (payload cursor.pending) address = some origin)
    {index : Nat} {reference : ManagedRef} {value : Word} {occurrence : Nat}
    (selected : cursor.pending[index]? = some (.managed reference value occurrence))
    (sameAddress : reference.cell.address = address) : index ≤ origin.index := by
  by_cases earlier : index ≤ origin.index
  · exact earlier
  · have newer : origin.index + 1 ≤ index := by omega
    have encoded : (payload cursor.pending)[index]? = some ⟨address, .qword value⟩ := by
      simpa only [Entry.store, sameAddress] using payload_at selected
    have shifted : ((payload cursor.pending).drop (origin.index + 1))[index - (origin.index + 1)]? =
        some ⟨address, .qword value⟩ := by
      rw [List.getElem?_drop]
      have aligned : origin.index + 1 + (index - (origin.index + 1)) = index := by omega
      rw [aligned]
      exact encoded
    exact False.elim (missing_no_qword
      (newestQWord_spec (payload cursor.pending) address origin found).2 shifted)

/-- The selected complete descriptor, value, and persistent occurrence come
from the actual queue entry at the production lookup's snapshot index. -/
structure ManagedSelection (cursor : Cursor) (target : Word) (origin : QWordOrigin) where
  reference : ManagedRef
  occurrence : Nat
  selected : cursor.pending[origin.index]? = some (.managed reference origin.value occurrence)
  address : reference.cell.address = target
  newest : newestQWord (payload cursor.pending) target = some origin

/-- Sequence integrity alone leaves the ordinary-authority alternative
explicit. Resource invariants may remove it, but a lookup or tag cannot. -/
theorem selection_cases {cursor : Cursor} (ordered : cursor.Ordered)
    {address : Word} {origin : QWordOrigin}
    (found : newestQWord (payload cursor.pending) address = some origin) :
    (∃ ticket, cursor.pending[origin.index]? =
      some (.ordinary ticket ⟨address, .qword origin.value⟩)) ∨
      Nonempty (ManagedSelection cursor address origin) := by
  rcases cursor.newestQWord_tag ordered address origin found with ordinary | managed
  · exact .inl ordinary
  · obtain ⟨reference, occurrence, selected, sameAddress, _⟩ := managed
    exact .inr ⟨⟨reference, occurrence, selected, sameAddress, found⟩⟩

/-- The selected occurrence dominates every same-address managed occurrence.
A strictly older snapshot index has a strictly smaller occurrence, regardless
of value equality or intervening ordinary entries. -/
theorem ManagedSelection.dominates {cursor : Cursor} {address : Word} {origin : QWordOrigin}
    (selection : ManagedSelection cursor address origin) (ordered : cursor.Ordered)
    {index : Nat} {reference : ManagedRef} {value : Word} {occurrence : Nat}
    (selected : cursor.pending[index]? = some (.managed reference value occurrence))
    (sameAddress : reference.cell.address = address) :
    index ≤ origin.index ∧ occurrence ≤ selection.occurrence ∧
      (index < origin.index → occurrence < selection.occurrence) := by
  have maximal := index_maximal selection.newest selected sameAddress
  have strict : index < origin.index → occurrence < selection.occurrence :=
    managed_index_lt ordered.1 selected selection.selected
  refine ⟨maximal, ?_, strict⟩
  by_cases same : index = origin.index
  · have atOrigin : cursor.pending[origin.index]? = some (.managed reference value occurrence) := by
      simpa only [same] using selected
    have equal : Entry.managed reference value occurrence =
        .managed selection.reference origin.value selection.occurrence := by
      exact Option.some.inj (atOrigin.symm.trans selection.selected)
    cases equal
    exact Nat.le_refl _
  · exact Nat.le_of_lt (strict (by omega))

/-- Reusing the selected occurrence forces both its complete descriptor and
full-width value; neither may be reconstructed from address/value equality. -/
theorem ManagedSelection.same_occurrence {cursor : Cursor} {address : Word} {origin : QWordOrigin}
    (selection : ManagedSelection cursor address origin) (ordered : cursor.Ordered)
    {index : Nat} {reference : ManagedRef} {value : Word}
    (selected : cursor.pending[index]? =
      some (.managed reference value selection.occurrence)) :
    index = origin.index ∧ reference = selection.reference ∧ value = origin.value :=
  occurrence_unique ordered selected selection.selected

private theorem newest_cons_tail {head : Store} {tail : Buffer} {address : Word}
    {origin : QWordOrigin} (found : newestQWord (head :: tail) address = some origin) :
    (origin.index = 0 ∧ newestQWord tail address = none) ∨
      ∃ index, origin.index = index + 1 ∧
        newestQWord tail address = some ⟨index, origin.value⟩ := by
  cases later : newestQWord tail address with
  | some previous =>
    have equal : (⟨previous.index + 1, previous.value⟩ : QWordOrigin) = origin := by
      simpa only [newestQWord, later, Option.some.injEq] using found
    subst origin
    exact .inr ⟨previous.index, rfl, rfl⟩
  | none =>
    cases head with
    | mk headAddress data =>
      cases data with
      | dword value => simp [newestQWord, later] at found
      | qword value =>
        by_cases same : headAddress = address
        · have equal : (⟨0, value⟩ : QWordOrigin) = origin := by
            simpa only [newestQWord, later, same, ↓reduceIte, Option.some.injEq] using found
          subst origin
          exact .inl ⟨rfl, rfl⟩
        · simp [newestQWord, later, same] at found

/-- Removing the FIFO head either removes the selected writer (which was the
head and has no later same-address qword), or preserves the exact descriptor,
value and occurrence with its snapshot index decreased by one. The persistent
counter is unchanged. This bookkeeping theorem does not itself publish bytes. -/
theorem ManagedSelection.dropHead {cursor : Cursor} {address : Word} {origin : QWordOrigin}
    (selection : ManagedSelection cursor address origin) :
    cursor.dropHead.nextStore = cursor.nextStore ∧
      ((origin.index = 0 ∧ newestQWord (payload cursor.dropHead.pending) address = none) ∨
        ∃ index, origin.index = index + 1 ∧
          newestQWord (payload cursor.dropHead.pending) address = some ⟨index, origin.value⟩ ∧
          cursor.dropHead.pending[index]? =
            some (.managed selection.reference origin.value selection.occurrence)) := by
  refine ⟨rfl, ?_⟩
  cases pending : cursor.pending with
  | nil =>
    have selected := selection.selected
    simp [pending] at selected
  | cons head tail =>
    have found : newestQWord (head.store :: payload tail) address = some origin := by
      simpa only [pending, payload_cons] using selection.newest
    rcases newest_cons_tail found with oldest | retained
    · exact .inl ⟨oldest.1, by simpa only [Cursor.dropHead, pending, List.tail_cons] using oldest.2⟩
    · obtain ⟨index, sameIndex, next⟩ := retained
      refine .inr ⟨index, sameIndex, ?_, ?_⟩
      · simpa only [Cursor.dropHead, pending, List.tail_cons] using next
      · simpa only [Cursor.dropHead, pending, List.tail_cons, sameIndex,
          List.getElem?_cons_succ] using selection.selected

private theorem newest_append_qword (buffer : Buffer) (address value : Word) :
    newestQWord (buffer ++ [⟨address, .qword value⟩]) address = some ⟨buffer.length, value⟩ := by
  induction buffer with
  | nil => simp [newestQWord]
  | cons head tail ih =>
    simp only [List.cons_append, newestQWord, ih, List.length_cons]

/-- A freshly appended managed qword becomes the actual production selection
at the old FIFO length, with its occurrence allocated from the old counter.
No earlier entry, even an equal-valued descriptor alias, can replace that tag. -/
def fresh (cursor : Cursor) (reference : ManagedRef) (value : Word) :
    ManagedSelection (cursor.enqueueManaged reference value) reference.cell.address
      ⟨cursor.pending.length, value⟩ where
  reference := reference
  occurrence := cursor.nextStore
  selected := List.getElem?_concat_length
  address := rfl
  newest := by
    change newestQWord (payload (cursor.pending ++ [.managed reference value cursor.nextStore]))
      reference.cell.address = some ⟨cursor.pending.length, value⟩
    rw [payload_enqueue]
    simpa only [Entry.store, payload, List.length_map] using
      newest_append_qword (payload cursor.pending) reference.cell.address value

private theorem newest_append_other (buffer : Buffer) (address other value : Word)
    (different : other ≠ address) :
    newestQWord (buffer ++ [⟨other, .qword value⟩]) address = newestQWord buffer address := by
  induction buffer with
  | nil => simp [newestQWord, different]
  | cons head tail ih =>
    simp only [List.cons_append, newestQWord, ih]

/-- Appending at another physical qword start retains the complete selected
entry, snapshot index, value and persistent occurrence. This only frames the
lookup; it does not assert that two distinct qwords have disjoint bytes. -/
def ManagedSelection.enqueueOther {cursor : Cursor} {address : Word} {origin : QWordOrigin}
    (selection : ManagedSelection cursor address origin) (reference : ManagedRef)
    (value : Word) (different : reference.cell.address ≠ address) :
    ManagedSelection (cursor.enqueueManaged reference value) address origin where
  reference := selection.reference
  occurrence := selection.occurrence
  selected := by
    change (cursor.pending ++ [.managed reference value cursor.nextStore])[origin.index]? = _
    rw [List.getElem?_append_left (List.getElem_of_getElem? selection.selected).1]
    exact selection.selected
  address := selection.address
  newest := by
    simpa only [Cursor.enqueueManaged, payload_enqueue, Entry.store,
      newest_append_other (payload cursor.pending) address reference.cell.address value different]
      using selection.newest

/-- Fresh allocation strictly follows every retained managed occurrence;
ordinary queue entries may account for gaps. The same theorem applies after
any head removal by Cursor.dropHead_ordered, without recycling occurrences. -/
theorem fresh_dominates (cursor : Cursor) (ordered : cursor.Ordered)
    (reference : ManagedRef) (value : Word) {index : Nat} {prior : ManagedRef}
    {priorValue : Word} {occurrence : Nat}
    (selected : cursor.pending[index]? = some (.managed prior priorValue occurrence)) :
    occurrence < (fresh cursor reference value).occurrence ∧
      index < (cursor.pending.length) ∧
      (cursor.enqueueManaged reference value).pending[index]? =
        some (.managed prior priorValue occurrence) := by
  refine ⟨cursor.managed_occurrence_lt ordered prior priorValue occurrence
    (List.mem_of_getElem? selected), (List.getElem_of_getElem? selected).1, ?_⟩
  change (cursor.pending ++ [.managed reference value cursor.nextStore])[index]? = _
  rw [List.getElem?_append_left (List.getElem_of_getElem? selected).1]
  exact selected

/-- Current resources remove the ordinary-selection alternative using the
existing resource theorem. This supplies a real selected descriptor, not a
caller-chosen desired occurrence or an assumed future view. -/
theorem of_current {state : OS.TSO64.State} {worker : Worker} {profile : Profile}
    {resources : Resources} {reference : ManagedRef} {origin : QWordOrigin}
    (valid : WellFormed state profile) (workerValid : WorkerValid state.world worker profile)
    (ordered : worker.storeCursor.Ordered) (current : Current state.world resources reference)
    (found : newestQWord (payload worker.pending) reference.cell.address = some origin) :
    ∃ selection : ManagedSelection worker.storeCursor reference.cell.address origin,
      Current state.world worker.resources selection.reference ∧
      selection.occurrence < worker.nextStore := by
  obtain ⟨writer, occurrence, selected, sameAddress, authority, below⟩ :=
    newest_managed_entry valid workerValid ordered current found
  exact ⟨⟨writer, occurrence, selected, sameAddress, found⟩, authority, below⟩

/-- Persistent cell identity requires both descriptors to be current in the
same well-formed world. Equal physical addresses alone supply no identity. -/
theorem ManagedSelection.cell {cursor : Cursor} {address : Word} {origin : QWordOrigin}
    (selection : ManagedSelection cursor address origin) {world : World}
    {writerResources readerResources : Resources} {reference : ManagedRef}
    (valid : Atomics64.WellFormed world)
    (writerCurrent : Current world writerResources selection.reference)
    (readerCurrent : Current world readerResources reference)
    (sameAddress : reference.cell.address = address) :
    selection.reference.handle.cell = reference.handle.cell :=
  WordProjection.address_injective valid writerCurrent.cell readerCurrent.cell
    (selection.address.trans sameAddress.symm)

end EDSL.OS.TSO64.Queue.SelectionOrder

#audit_edsl
