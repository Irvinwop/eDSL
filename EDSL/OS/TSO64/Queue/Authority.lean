/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Queue.Model
import EDSL.OS.TSO64.Effects

namespace EDSL.OS.TSO64
open X86

/-- Stability preserves the exact original authorization result, including both
descriptors and current membership in the unchanged worker grant list. -/
theorem Stable.current {before after : World} (frame : Stable before after)
    (resources : Resources) (reference : Queue.ManagedRef) :
    Queue.Current after resources reference ↔ Queue.Current before resources reference := by
  simp only [Queue.Current, frame.authorize]

theorem Stable.queue_valid {before after : World} (frame : Stable before after)
    (resources : Resources) (entry : Queue.Entry) (profile : Queue.Profile) :
    Queue.Valid after resources entry profile ↔ Queue.Valid before resources entry profile := by
  cases entry <;> simp only [Queue.Valid, frame.storeGate, frame.current]

theorem Stable.queueEntry {before after : World} (frame : Stable before after)
    {resources : Resources} {entry : Queue.Entry} {profile : Queue.Profile}
    (valid : Queue.Valid before resources entry profile) :
    Queue.Valid after resources entry profile := (frame.queue_valid _ _ _).mpr valid

namespace Queue

/-- Admission records only current lookup results and the original request.
It does not run a store, test a future state, or assign a publication event. -/
inductive Admission (world : World) (resources : Resources) (store : Store)
    (occurrence : Nat) (profile : Profile) : Entry → Prop where
  | ordinary (ticket : Ownership.Ticket)
      (selected : grantFor world resources store = some ticket) :
      Admission world resources store occurrence profile (.ordinary ticket store)
  | managed (reference : ManagedRef) (value : Word)
      (ordinaryAbsent : grantFor world resources store = none)
      (shared : profile = .sharedCell)
      (qword : store.value = .qword value)
      (selected : atomicFor world resources store.address =
        some (reference.identifier, reference.handle, reference.cell)) :
      Admission world resources store occurrence profile (.managed reference value occurrence)

theorem admit_effect {world : World} {resources : Resources} {store : Store}
    {occurrence : Nat} {profile : Profile} {entry : Entry}
    (success : admit world resources store occurrence profile = .ok entry) :
    Admission world resources store occurrence profile entry := by
  cases grant : grantFor world resources store with
  | some ticket =>
      simp only [admit, grant, Except.ok.injEq] at success
      subst entry
      exact .ordinary ticket grant
  | none =>
      cases profile with
      | ownedOnly => simp [admit, grant] at success
      | sharedCell =>
          cases store with
          | mk address value =>
              cases value with
              | dword value => simp [admit, grant] at success
              | qword value =>
                  cases selected : atomicFor world resources address with
                  | none => simp [admit, grant, selected] at success
                  | some descriptor =>
                      rcases descriptor with ⟨identifier, handle, cell⟩
                      simp only [admit, grant, selected, Except.ok.injEq] at success
                      subst entry
                      exact .managed ⟨identifier, handle, cell⟩ value grant rfl rfl selected

theorem Admission.valid {world : World} {resources : Resources} {store : Store}
    {occurrence : Nat} {profile : Profile} {entry : Entry}
    (effect : Admission world resources store occurrence profile entry) :
    Valid world resources entry profile := by
  cases effect with
  | ordinary ticket selected => exact grantFor_sound selected
  | managed reference value ordinaryAbsent shared qword selected =>
      have authoritative := atomicFor_sound selected
      exact ⟨shared, authoritative.1, authoritative.2.1⟩

/-- The payload is the exact originally requested store, including its width.
The managed descriptor's address comes from atomicFor's checked equality. -/
theorem Admission.store {world : World} {resources : Resources} {store : Store}
    {occurrence : Nat} {profile : Profile} {entry : Entry}
    (effect : Admission world resources store occurrence profile entry) : entry.store = store := by
  cases effect with
  | ordinary ticket selected => rfl
  | managed reference value ordinaryAbsent shared qword selected =>
      have addressEq := (atomicFor_sound selected).2.2
      cases store with
      | mk address originalValue =>
          simp only at qword addressEq
          simp only [Entry.store, addressEq, qword]

theorem Admission.managed_occurrence {world : World} {resources : Resources} {store : Store}
    {occurrence : Nat} {profile : Profile} {entry : Entry}
    (effect : Admission world resources store occurrence profile entry)
    {reference : ManagedRef} {value : Word} {sequence : Nat}
    (managed : entry = .managed reference value sequence) : sequence = occurrence := by
  cases effect <;> cases managed <;> rfl

/-- A successful default admission is ordinary even for an arbitrary initial
world. No invariant is needed to exclude managed entries from this API. -/
theorem Admission.ownedOnly {world : World} {resources : Resources} {store : Store}
    {occurrence : Nat} {entry : Entry}
    (effect : Admission world resources store occurrence .ownedOnly entry) :
    ∃ ticket, entry = .ordinary ticket store ∧ grantFor world resources store = some ticket := by
  cases effect with
  | ordinary ticket selected => exact ⟨ticket, rfl, selected⟩
  | managed reference value ordinaryAbsent shared qword selected => cases shared

theorem admit_valid {world : World} {resources : Resources} {store : Store}
    {occurrence : Nat} {profile : Profile} {entry : Entry}
    (success : admit world resources store occurrence profile = .ok entry) :
    Valid world resources entry profile := (admit_effect success).valid

theorem admit_store {world : World} {resources : Resources} {store : Store}
    {occurrence : Nat} {profile : Profile} {entry : Entry}
    (success : admit world resources store occurrence profile = .ok entry) :
    entry.store = store := (admit_effect success).store

theorem admit_managed_occurrence {world : World} {resources : Resources} {store : Store}
    {occurrence : Nat} {profile : Profile} {entry : Entry}
    (success : admit world resources store occurrence profile = .ok entry)
    {reference : ManagedRef} {value : Word} {sequence : Nat}
    (managed : entry = .managed reference value sequence) : sequence = occurrence :=
  (admit_effect success).managed_occurrence managed

theorem admit_ownedOnly_ordinary {world : World} {resources : Resources} {store : Store}
    {occurrence : Nat} {entry : Entry}
    (success : admit world resources store occurrence = .ok entry) :
    ∃ ticket, entry = .ordinary ticket store ∧ grantFor world resources store = some ticket :=
  (admit_effect success).ownedOnly

theorem admit_ordinary {world : World} {resources : Resources} {store : Store}
    (occurrence : Nat) (profile : Profile) {ticket : Ownership.Ticket}
    (selected : grantFor world resources store = some ticket) :
    admit world resources store occurrence profile = .ok (.ordinary ticket store) := by
  simp only [admit, selected]

theorem admit_managed {world : World} {resources : Resources} {store : Store}
    (occurrence : Nat) {reference : ManagedRef} {value : Word}
    (ordinaryAbsent : grantFor world resources store = none)
    (qword : store.value = .qword value)
    (selected : atomicFor world resources store.address =
      some (reference.identifier, reference.handle, reference.cell)) :
    admit world resources store occurrence .sharedCell =
      .ok (.managed reference value occurrence) := by
  simp only [admit, ordinaryAbsent, qword, selected]

theorem admit_ownedOnly_no_grant {world : World} {resources : Resources} {store : Store}
    (occurrence : Nat) (absent : grantFor world resources store = none) :
    admit world resources store occurrence = .error .noGrant := by
  simp only [admit, absent]

theorem admit_shared_dword_no_grant {world : World} {resources : Resources}
    (address : Word) (value : BitVec 32) (occurrence : Nat)
    (absent : grantFor world resources ⟨address, .dword value⟩ = none) :
    admit world resources ⟨address, .dword value⟩ occurrence .sharedCell = .error .noGrant := by
  simp only [admit, absent]

theorem admit_shared_no_atomic_grant {world : World} {resources : Resources}
    (address value : Word) (occurrence : Nat)
    (ordinaryAbsent : grantFor world resources ⟨address, .qword value⟩ = none)
    (managedAbsent : atomicFor world resources address = none) :
    admit world resources ⟨address, .qword value⟩ occurrence .sharedCell =
      .error .noAtomicGrant := by
  simp only [admit, ordinaryAbsent, managedAbsent]

end Queue
end EDSL.OS.TSO64
