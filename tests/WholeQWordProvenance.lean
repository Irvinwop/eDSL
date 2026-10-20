/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.StoreBuffer.WholeQWord
import EDSL.Audit

namespace EDSL.Tests.WholeQWordProvenance
open X86
open X86.StoreBuffer.Mixed

-- These are functional buffer observations at canonical, nonwrapping addresses;
-- they make no scheduler, OS admission or hardware atomicity claim.
def ram : Memory where
  read address := if address = 0x3006 ∨ address = 0x3015 then none else some 0x5a
  executable _ := false
  writable _ := true

def older : Store := ⟨0x1000, .qword 0x1122334455667788⟩
def newer : Store := ⟨0x1000, .qword 0xfedcba9876543210⟩
def own : Buffer := [older, newer]

-- Full-width loads and independent little-endian bytes catch truncated values,
-- reversed queue order and reuse of an older store's high half.
theorem newest_full_qword :
    (newestQWord own 0x1000,
      loadQWord (view ram own) 0x1000,
      ([0x1000, 0x1003, 0x1004, 0x1007] : List Word).map (view ram own).read) =
    (some ⟨1, 0xfedcba9876543210⟩, .ok 0xfedcba9876543210,
      [some 0x10, some 0x76, some 0x98, some 0xfe]) := by rfl

-- Equal payloads do not identify an occurrence: enqueue selects a new position
-- even though the concrete load's value stays the same.
theorem repeated_equal_values_keep_positions :
    (newestQWord own 0x1000,
      newestQWord (enqueue own newer) 0x1000,
      loadQWord (view ram (enqueue own newer)) 0x1000,
      (view ram (enqueue own newer)).read 0x1006) =
    (some ⟨1, 0xfedcba9876543210⟩, some ⟨2, 0xfedcba9876543210⟩,
      .ok 0xfedcba9876543210, some 0xdc) := by rfl

-- Both neighbors abut the target without overlapping it. The earlier DWORD
-- counts toward the origin index; the later QWORD must not replace that origin.
def separated : Buffer :=
  [⟨0x0ffc, .dword 0x89abcdef⟩, older, newer,
    ⟨0x1008, .qword 0x0123456789abcdef⟩]

theorem disjoint_entries_do_not_retarget :
    WholeQWordCompatible separated 0x1000 ∧
    (newestQWord separated 0x1000,
      loadQWord (view ram separated) 0x1000,
      ([0x0fff, 0x1008, 0x100f] : List Word).map (view ram separated).read) =
    (some ⟨2, 0xfedcba9876543210⟩, .ok 0xfedcba9876543210,
      [some 0x89, some 0xef, some 0x01]) := by
  constructor
  · have before : (⟨0x0ffc, .dword 0x89abcdef⟩ : Store).Disjoint 0x1000 8 := by
      intro offset bound
      exact (show ∀ i : Fin 8,
        4 ≤ (((0x1000 : Word) + BitVec.ofNat 64 i.val) - 0x0ffc).toNat
        from by decide) ⟨offset, bound⟩
    have after : (⟨0x1008, .qword 0x0123456789abcdef⟩ : Store).Disjoint 0x1000 8 := by
      intro offset bound
      exact (show ∀ i : Fin 8,
        8 ≤ (((0x1000 : Word) + BitVec.ofNat 64 i.val) - 0x1008).toNat
        from by decide) ⟨offset, bound⟩
    intro store member
    have choices : store = ⟨0x0ffc, .dword 0x89abcdef⟩ ∨ store = older ∨
        store = newer ∨ store = ⟨0x1008, .qword 0x0123456789abcdef⟩ := by
      simpa [separated] using member
    rcases choices with rfl | rfl | rfl | rfl
    · exact before
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr after
  · rfl

def fifoObservation := do
  let after ← publishOldest ram own
  return (loadQWord after.1 0x1000,
    loadQWord (view after.1 after.2) 0x1000,
    newestQWord after.2 0x1000,
    after.1.read 0x1004, (view after.1 after.2).read 0x1004)

-- Actual FIFO publication exposes the older payload globally. The issuing
-- worker still sees the newer payload, whose remaining-buffer index is now 0.
theorem fifo_publication_preserves_own_newest : fifoObservation =
    some (.ok 0x1122334455667788, .ok 0xfedcba9876543210,
      some ⟨0, 0xfedcba9876543210⟩, some 0x44, some 0x98) := by rfl

def elsewhere : Buffer :=
  [⟨0x4000, .dword 0x89abcdef⟩, ⟨0x4010, .qword 0x0123456789abcdef⟩]

def currentMemoryObservation := do
  let after ← publishOldest ram [⟨0x3000, .qword 0x8071625344352617⟩]
  return (newestQWord elsewhere 0x3000, newestQWord elsewhere 0x3010,
    loadQWord (view ram elsewhere) 0x3000,
    loadQWord (view after.1 elsewhere) 0x3000,
    loadQWord (view after.1 elsewhere) 0x3010,
    ([0x3000, 0x3006, 0x3007] : List Word).map (view after.1 elsewhere).read)

-- A peer publication repairs the first real upper-byte fault. A separate
-- missing byte must still fault through the same nonempty, disjoint own buffer.
-- A cached initial memory or a fabricated success on a lookup miss fails here.
theorem no_origin_uses_current_published_memory : currentMemoryObservation =
    some (none, none, .error (.inaccessibleData 0x3006),
      .ok 0x8071625344352617, .error (.inaccessibleData 0x3015),
      [some 0x17, some 0x71, some 0x80]) := by rfl

def overlappingDWord : Store := ⟨0x1002, .dword 0xaabbccdd⟩

-- The lookup alone still finds the old QWORD. Its value is not the actual
-- mixed-width load: four middle bytes now come from the partial DWORD.
theorem partial_overlap_changes_the_real_view :
    ¬ QWordCompatible 0x1000 overlappingDWord ∧
    ¬ WholeQWordCompatible [older, overlappingDWord] 0x1000 ∧
    (newestQWord [older, overlappingDWord] 0x1000,
      loadQWord (view ram [older, overlappingDWord]) 0x1000,
      ([0x1001, 0x1002, 0x1005, 0x1006] : List Word).map
        (view ram [older, overlappingDWord]).read) =
    (some ⟨0, 0x1122334455667788⟩, .ok 0x1122aabbccdd7788,
      [some 0x77, some 0xdd, some 0xaa, some 0x22]) := by
  have excluded : ¬ QWordCompatible 0x1000 overlappingDWord := by
    intro compatible
    have disjoint : overlappingDWord.Disjoint 0x1000 8 := compatible
    have impossible := disjoint 2 (by decide)
    change 4 ≤ 0 at impossible
    exact (by decide : ¬ (4 ≤ 0)) impossible
  refine ⟨excluded, ?_, ?_⟩
  · intro compatible
    exact excluded (compatible overlappingDWord (by simp))
  · rfl

end EDSL.Tests.WholeQWordProvenance

#audit_edsl
