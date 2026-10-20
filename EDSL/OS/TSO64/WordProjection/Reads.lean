/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.WordProjection.Core

set_option autoImplicit false

namespace EDSL.OS.TSO64.WordProjection
open X86 Concurrency

/-- Current descriptors alias physically exactly when their persistent cell
identities agree. Handles and actors need not agree. -/
private theorem current_address_eq_iff {world : World} {leftResources rightResources : Resources}
    {left right : Queue.ManagedRef} (valid : Atomics64.WellFormed world)
    (leftCurrent : Queue.Current world leftResources left)
    (rightCurrent : Queue.Current world rightResources right) :
    left.cell.address = right.cell.address ↔ left.handle.cell = right.handle.cell := by
  constructor
  · exact address_injective valid leftCurrent.cell rightCurrent.cell
  · intro same
    have linked := leftCurrent.cell
    rw [same] at linked
    have cells : left.cell = right.cell := Option.some.inj (linked.symm.trans rightCurrent.cell)
    exact congrArg Atomics64.Cell.address cells

/-- A physical lookup miss excludes every managed alias in the projected
buffer. Ordinary entries disappear from this symbolic-location statement;
their byte framing is supplied separately by `local_managed_load`. -/
private theorem no_pending_of_absent {world : World} {resources : Resources}
    {profile : Profile} {reference : Queue.ManagedRef}
    (valid : Atomics64.WellFormed world)
    (current : Queue.Current world resources reference) (entries : List Pending)
    (entriesValid : ∀ entry ∈ entries, PendingValid world resources entry profile)
    (absent : StoreBuffer.Mixed.newestQWord (Queue.payload entries)
      reference.cell.address = none) :
    TSOWord.NoPending (managed entries).reverse reference.handle.cell := by
  revert entriesValid absent
  induction entries with
  | nil =>
    intro _ _ pair member
    cases member
  | cons head tail ih =>
    intro entriesValid absent
    have tailValid : ∀ entry ∈ tail, PendingValid world resources entry profile := by
      intro entry member
      exact entriesValid entry (List.mem_cons_of_mem head member)
    have tailAbsent : StoreBuffer.Mixed.newestQWord (Queue.payload tail)
        reference.cell.address = none := by
      cases selected : StoreBuffer.Mixed.newestQWord (Queue.payload tail)
          reference.cell.address with
      | none => rfl
      | some origin =>
        simp [Queue.payload_cons, StoreBuffer.Mixed.newestQWord, selected] at absent
    have tailNoPending := ih tailValid tailAbsent
    cases head with
    | ordinary ticket store => exact tailNoPending
    | managed writer stored occurrence =>
      have writerCurrent : Queue.Current world resources writer :=
        (entriesValid _ List.mem_cons_self).2
      have different : writer.handle.cell ≠ reference.handle.cell := by
        intro same
        have sameAddress := (current_address_eq_iff valid writerCurrent current).mpr same
        simp [Queue.payload_cons, Queue.Entry.store, StoreBuffer.Mixed.newestQWord,
          tailAbsent, sameAddress] at absent
      change TSOWord.NoPending ((writer.handle.cell, stored) :: managed tail).reverse
        reference.handle.cell
      rw [List.reverse_cons]
      intro pair member
      rcases List.mem_append.mp member with newer | oldest
      · exact tailNoPending pair newer
      · have equal := List.mem_singleton.mp oldest
        subst pair
        exact different

/-- Follow the actual newest-qword search through the oldest-first queue.
The selected descriptor determines the symbolic location; equality of stored
values is never used to choose an occurrence. The reversed strict suffix is
the reference rule's prefix with no pending write to that location. -/
private theorem buffer_of_newest {world : World} {resources : Resources}
    {profile : Profile} {reference : Queue.ManagedRef}
    (valid : Atomics64.WellFormed world)
    (current : Queue.Current world resources reference) (entries : List Pending)
    (entriesValid : ∀ entry ∈ entries, PendingValid world resources entry profile)
    {origin : StoreBuffer.Mixed.QWordOrigin}
    (found : StoreBuffer.Mixed.newestQWord (Queue.payload entries)
      reference.cell.address = some origin) :
    ∃ newer older,
      (managed entries).reverse = newer ++ [(reference.handle.cell, origin.value)] ++ older ∧
      TSOWord.NoPending newer reference.handle.cell := by
  revert entriesValid origin
  induction entries with
  | nil =>
    intro _ origin found
    simp [StoreBuffer.Mixed.newestQWord] at found
  | cons head tail ih =>
    intro entriesValid origin found
    have tailValid : ∀ entry ∈ tail, PendingValid world resources entry profile := by
      intro entry member
      exact entriesValid entry (List.mem_cons_of_mem head member)
    cases later : StoreBuffer.Mixed.newestQWord (Queue.payload tail)
        reference.cell.address with
    | some tailOrigin =>
      have equal : (⟨tailOrigin.index + 1, tailOrigin.value⟩ : StoreBuffer.Mixed.QWordOrigin) =
          origin := by
        simpa only [Queue.payload_cons, StoreBuffer.Mixed.newestQWord, later,
          Option.some.injEq] using found
      subst origin
      obtain ⟨newer, older, bufferEq, noNewer⟩ := ih tailValid later
      cases head with
      | ordinary ticket store => exact ⟨newer, older, bufferEq, noNewer⟩
      | managed writer stored occurrence =>
        refine ⟨newer, older ++ [(writer.handle.cell, stored)], ?_, noNewer⟩
        simp only [managed, List.reverse_cons, bufferEq, List.append_assoc]
    | none =>
      cases head with
      | ordinary ticket store =>
        have gate : StoreGate world resources.actor ticket store :=
          (entriesValid _ List.mem_cons_self).2
        have separate := gate.managed_disjoint valid current
        cases store with
        | mk address data =>
          cases data with
          | dword stored =>
            simp [Queue.payload_cons, Queue.Entry.store, StoreBuffer.Mixed.newestQWord,
              later] at found
          | qword stored =>
            by_cases same : address = reference.cell.address
            · subst address
              have impossible := separate 0 (by decide)
              simp [StoreBuffer.Mixed.Store.width] at impossible
            · simp [Queue.payload_cons, Queue.Entry.store, StoreBuffer.Mixed.newestQWord,
                later, same] at found
      | managed writer stored occurrence =>
        have writerCurrent : Queue.Current world resources writer :=
          (entriesValid _ List.mem_cons_self).2
        by_cases sameAddress : writer.cell.address = reference.cell.address
        · have equal : (⟨0, stored⟩ : StoreBuffer.Mixed.QWordOrigin) = origin := by
            simpa only [Queue.payload_cons, Queue.Entry.store, StoreBuffer.Mixed.newestQWord,
              later, sameAddress, ↓reduceIte, Option.some.injEq] using found
          subst origin
          have sameCell := (current_address_eq_iff valid writerCurrent current).mp sameAddress
          refine ⟨(managed tail).reverse, [], ?_,
            no_pending_of_absent valid current tail tailValid later⟩
          simp only [managed, List.reverse_cons, sameCell, List.append_nil]
        · simp [Queue.payload_cons, Queue.Entry.store, StoreBuffer.Mixed.newestQWord,
            later, sameAddress] at found

/-- Every successful current managed load has its real reference read label.
Resource validity supplies whole-qword compatibility for the actual byte load
and excludes ordinary stores at the registered word. Forwarding selects the
actual newest managed descriptor, including equal-value and handle aliases.
No occurrence ordering or prior issue history is required. -/
theorem managed_read {state : State} {worker : Worker} {profile : Profile}
    {tid : Nat} {reference : Queue.ManagedRef} {value : Word}
    (valid : WellFormed state profile) (live : state.workers[tid]? = some worker)
    (current : Queue.Current state.world worker.resources reference)
    (loaded : loadQWord (localCPU state worker).memory reference.cell.address = .ok value) :
    TSOWord.Step (project state) (.read tid reference.handle.cell value) (project state) := by
  have workerValid := valid.2 worker (List.mem_of_getElem? live)
  have source := local_managed_load valid workerValid current
  have notBlocked : TSOWord.NotBlocked (project state) tid := Or.inl rfl
  cases found : StoreBuffer.Mixed.newestQWord (payload worker.pending)
      reference.cell.address with
  | none =>
    rw [found] at source
    have publishedRead : loadQWord (published state.world) reference.cell.address = .ok value :=
      source.symm.trans loaded
    apply TSOWord.Step.readMemory notBlocked
    · exact memory_read current.cell publishedRead
    · change TSOWord.NoPending (buffers state tid) reference.handle.cell
      rw [buffers_live live]
      exact no_pending_of_absent valid.1 current worker.pending workerValid.2 found
  | some origin =>
    rw [found] at source
    have same : origin.value = value := Except.ok.inj (source.symm.trans loaded)
    obtain ⟨newer, older, bufferEq, noNewer⟩ :=
      buffer_of_newest valid.1 current worker.pending workerValid.2 found
    apply TSOWord.Step.readBuffer (newer := newer) (older := older) notBlocked
    · change buffers state tid = newer ++ [(reference.handle.cell, value)] ++ older
      rw [buffers_live live]
      simpa only [same] using bufferEq
    · exact noNewer

end EDSL.OS.TSO64.WordProjection
