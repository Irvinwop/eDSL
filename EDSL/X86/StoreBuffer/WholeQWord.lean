/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.StoreBuffer.Mixed

set_option autoImplicit false

/-!
Whole-qword provenance over the production mixed-width byte overlay.

Compatibility is a theorem premise to be derived from a resource invariant by
clients; it grants no authority. These results establish no OS authorization,
physical atomicity, or source acquire/release semantics, and change no scheduler.
An origin index is only a position in the supplied oldest-first buffer snapshot.
It is not a persistent occurrence identifier, source reads-from identifier, or
global linearization identifier.
-/

namespace EDSL.X86.StoreBuffer.Mixed

/-- A local buffer position and the complete 64-bit payload stored there. -/
structure QWordOrigin where
  index : Nat
  value : Word
  deriving DecidableEq, Repr

/-- Search newest first for an exact-address qword, returning its oldest-first
position. DWORDs and nonmatching addresses are ignored only by this lookup;
they still participate in the production `view` and count toward positions. -/
def newestQWord : Buffer → Word → Option QWordOrigin
  | [], _ => none
  | head :: tail, address =>
      match newestQWord tail address with
      | some origin => some ⟨origin.index + 1, origin.value⟩
      | none =>
          match head.value with
          | .dword _ => none
          | .qword value =>
              if head.address = address then some ⟨0, value⟩ else none

/-- A qword may replace the whole operand or miss it entirely. A DWORD must
miss it entirely. Disjointness is the production modular byte-footprint relation. -/
def QWordCompatible (address : Word) (store : Store) : Prop :=
  match store.value with
  | .qword _ => store.address = address ∨ store.Disjoint address 8
  | .dword _ => store.Disjoint address 8

/-- A prestate premise, never an authorization mechanism. -/
def WholeQWordCompatible (buffer : Buffer) (address : Word) : Prop :=
  ∀ store ∈ buffer, QWordCompatible address store

/-- Lookup provenance is structural and needs no compatibility assumption:
the exact entry exists, and its strict suffix has no matching qword. -/
theorem newestQWord_spec (buffer : Buffer) (address : Word) (origin : QWordOrigin)
    (found : newestQWord buffer address = some origin) :
    buffer[origin.index]? = some ⟨address, .qword origin.value⟩ ∧
      newestQWord (buffer.drop (origin.index + 1)) address = none := by
  induction buffer generalizing origin with
  | nil => simp [newestQWord] at found
  | cons head tail ih =>
    cases later : newestQWord tail address with
    | some tailOrigin =>
      have equal : (⟨tailOrigin.index + 1, tailOrigin.value⟩ : QWordOrigin) = origin := by
        simpa only [newestQWord, later, Option.some.injEq] using found
      subst origin
      obtain ⟨entry, absent⟩ := ih tailOrigin later
      constructor
      · simpa only [List.getElem?_cons_succ] using entry
      · simpa only [List.drop_succ_cons] using absent
    | none =>
      cases head with
      | mk headAddress headValue =>
        cases headValue with
        | dword value => simp [newestQWord, later] at found
        | qword value =>
          by_cases same : headAddress = address
          · subst headAddress
            have equal : (⟨0, value⟩ : QWordOrigin) = origin := by
              simpa [newestQWord, later] using found
            subst origin
            exact ⟨rfl, later⟩
          · simp [newestQWord, later, same] at found

/-- The returned value and address belong to this exact entry, without a profile. -/
theorem newestQWord_getElem? (buffer : Buffer) (address : Word) (origin : QWordOrigin)
    (found : newestQWord buffer address = some origin) :
    buffer[origin.index]? = some ⟨address, .qword origin.value⟩ :=
  (newestQWord_spec buffer address origin found).1

theorem newestQWord_index_lt (buffer : Buffer) (address : Word) (origin : QWordOrigin)
    (found : newestQWord buffer address = some origin) :
    origin.index < buffer.length :=
  (List.getElem_of_getElem? (newestQWord_getElem? buffer address origin found)).1

/-- Every matching qword in this buffer is at or before the returned position. -/
theorem newestQWord_drop_eq_none (buffer : Buffer) (address : Word) (origin : QWordOrigin)
    (found : newestQWord buffer address = some origin) :
    newestQWord (buffer.drop (origin.index + 1)) address = none :=
  (newestQWord_spec buffer address origin found).2

/-- A miss frames every store only when the compatibility premise is supplied. -/
theorem newestQWord_none_disjoint (buffer : Buffer) (address : Word)
    (compatible : WholeQWordCompatible buffer address)
    (missing : newestQWord buffer address = none) :
    ∀ store ∈ buffer, store.Disjoint address 8 := by
  revert compatible missing
  induction buffer with
  | nil =>
    intro _ _ store member
    cases member
  | cons head tail ih =>
    intro compatible missing
    have tailCompatible : WholeQWordCompatible tail address := by
      intro store member
      exact compatible store (List.mem_cons_of_mem head member)
    have tailMissing : newestQWord tail address = none := by
      cases selected : newestQWord tail address with
      | none => rfl
      | some origin => simp [newestQWord, selected] at missing
    have headCompatible := compatible head List.mem_cons_self
    have headDisjoint : head.Disjoint address 8 := by
      cases head with
      | mk headAddress headValue =>
        cases headValue with
        | dword value => exact headCompatible
        | qword value =>
          rcases headCompatible with same | outside
          · change headAddress = address at same
            subst headAddress
            simp [newestQWord, tailMissing] at missing
          · exact outside
    intro store member
    rcases List.mem_cons.mp member with rfl | member
    · exact headDisjoint
    · exact ih tailCompatible tailMissing store member

/-- Under the prestate profile, every store newer than the origin misses all
eight operand bytes, including newer DWORDs and nonmatching qwords. -/
theorem newestQWord_some_disjoint (buffer : Buffer) (address : Word) (origin : QWordOrigin)
    (compatible : WholeQWordCompatible buffer address)
    (found : newestQWord buffer address = some origin) :
    ∀ store ∈ buffer.drop (origin.index + 1), store.Disjoint address 8 := by
  exact newestQWord_none_disjoint (buffer.drop (origin.index + 1)) address
    (fun store member => compatible store (List.mem_of_mem_drop member))
    (newestQWord_drop_eq_none buffer address origin found)

/-- An exact qword entry followed by disjoint stores supplies the actual DATA
load through `view`. Earlier stores need no compatibility assumption. -/
theorem view_loadQWord_of_getElem? (memory : Memory) (buffer : Buffer)
    (address value : Word) (index : Nat)
    (valid : qwordAddressable address = true)
    (entry : buffer[index]? = some ⟨address, .qword value⟩)
    (later : ∀ store ∈ buffer.drop (index + 1), store.Disjoint address 8) :
    loadQWord (view memory buffer) address = .ok value := by
  induction buffer generalizing memory index with
  | nil => simp at entry
  | cons head tail ih =>
    cases index with
    | zero =>
      have equal : head = ⟨address, .qword value⟩ := by
        simpa only [List.getElem?_cons_zero, Option.some.injEq] using entry
      subst head
      have tailDisjoint : ∀ store ∈ tail, store.Disjoint address 8 := by
        simpa only [List.drop_succ_cons, List.drop_zero] using later
      rw [view_cons, view_loadQWord_frame _ _ _ tailDisjoint]
      exact qword_load_after_write memory address value valid
    | succ index =>
      have tailEntry : tail[index]? = some ⟨address, .qword value⟩ := by
        simpa only [List.getElem?_cons_succ] using entry
      have tailDisjoint : ∀ store ∈ tail.drop (index + 1), store.Disjoint address 8 := by
        simpa only [List.drop_succ_cons] using later
      rw [view_cons]
      exact ih (head.publish memory) index tailEntry tailDisjoint

/-- Whole-qword provenance for the existing byte overlay, conditional on the
addressability and compatible prestate premises. A lookup miss preserves the
complete global-memory load result, including faults. No write admission is inferred. -/
theorem view_loadQWord_newestQWord (memory : Memory) (buffer : Buffer) (address : Word)
    (valid : qwordAddressable address = true)
    (compatible : WholeQWordCompatible buffer address) :
    loadQWord (view memory buffer) address =
      match newestQWord buffer address with
      | some origin => .ok origin.value
      | none => loadQWord memory address := by
  cases found : newestQWord buffer address with
  | none =>
    exact view_loadQWord_frame memory buffer address
      (newestQWord_none_disjoint buffer address compatible found)
  | some origin =>
    exact view_loadQWord_of_getElem? memory buffer address origin.value origin.index valid
      (newestQWord_getElem? buffer address origin found)
      (newestQWord_some_disjoint buffer address origin compatible found)

end EDSL.X86.StoreBuffer.Mixed
