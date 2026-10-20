/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.StoreBuffer.Mixed
import EDSL.Audit

namespace EDSL.Tests.MixedStoreBuffer
open X86
open X86.StoreBuffer.Mixed

/-- The missing upper operand byte and denied upper write byte are intentional. -/
def ram : Memory where
  read address := if address = 0x3006 then none else some 0x5a
  executable address := decide (address.toNat < 0x100)
  writable address := address != 0x2007

def wide : Store := ⟨0x1000, .qword 0x1122334455667788⟩
def narrow : Store := ⟨0x1002, .dword 0xaabbccdd⟩
def pending : Buffer := [wide, narrow]

-- Literal little-endian observations distinguish partial-byte forwarding from
-- whole-store matching, truncation, reversed queue order and reversed endianness.
-- Kernel reduction checks these independent constants through the real APIs.
theorem mixed_overlap : loadQWord (view ram pending) 0x1000 =
    .ok 0x1122aabbccdd7788 := by rfl

theorem overlap_dword : loadDWord (view ram pending) 0x1004 = .ok 0x1122aabb := by rfl

theorem overlap_stack_read : readWord (view ram pending) 0x1000 =
    .ok 0x1122aabbccdd7788 := by rfl

theorem forwarded_bytes : ([0x0fff, 0x1000, 0x1001, 0x1002, 0x1003,
    0x1004, 0x1005, 0x1006, 0x1007, 0x1008] : List Word).map (forward pending) =
    [none, some 0x88, some 0x77, some 0xdd, some 0xcc, some 0xbb,
      some 0xaa, some 0x22, some 0x11, none] := by rfl

theorem overlap_order : loadQWord (view ram [narrow, wide]) 0x1000 =
    .ok 0x1122334455667788 := by rfl

-- A newer qword supplies its upper four bytes too. The older dword's bytes
-- beyond that qword must survive: a whole-entry deletion would lose them.
theorem newer_qword : loadQWord (view ram
    [⟨0x1006, .dword 0xaabbccdd⟩, ⟨0x1000, .qword 0xfedcba9876543210⟩]) 0x1000 =
    .ok 0xfedcba9876543210 := by rfl

theorem older_tail_survives : loadDWord (view ram
    [⟨0x1006, .dword 0xaabbccdd⟩, ⟨0x1000, .qword 0xfedcba9876543210⟩]) 0x1006 =
    .ok 0xaabbfedc := by rfl

-- The qword starts inside an earlier dword, crossing both the earlier end and
-- its own upper-byte boundary. Ordinary functional addressability allows this.
theorem shifted_qword : loadQWord (view ram
    [⟨0x1000, .dword 0xaabbccdd⟩, ⟨0x1002, .qword 0x1122334455667788⟩]) 0x1000 =
    .ok 0x334455667788ccdd := by rfl

/-- Observe a peer's global load and the issuing worker's own load at each drain. -/
def fifoObservations : Option (List (Except Error Word × Except Error Word) × Bool) := do
  let first ← publishOldest ram pending
  let second ← publishOldest first.1 first.2
  return ([(loadQWord ram 0x1000, loadQWord (view ram pending) 0x1000),
    (loadQWord first.1 0x1000, loadQWord (view first.1 first.2) 0x1000),
    (loadQWord second.1 0x1000, loadQWord (view second.1 second.2) 0x1000)],
    second.2.isEmpty && (publishOldest second.1 second.2).isNone)

theorem fifo_stages : fifoObservations = some
    ([(.ok 0x5a5a5a5a5a5a5a5a, .ok 0x1122aabbccdd7788),
      (.ok 0x1122334455667788, .ok 0x1122aabbccdd7788),
      (.ok 0x1122aabbccdd7788, .ok 0x1122aabbccdd7788)], true) := by rfl

-- Disjoint mixed writes retain both observations in either order.
theorem disjoint_observations :
    ([([wide, ⟨0x1010, .dword 0x89abcdef⟩] : Buffer),
      [⟨0x1010, .dword 0x89abcdef⟩, wide]] : List Buffer).map (fun buffer =>
        (loadQWord (view ram buffer) 0x1000, loadDWord (view ram buffer) 0x1010,
          loadDWord (view ram buffer) 0x1008)) =
    [(.ok 0x1122334455667788, .ok 0x89abcdef, .ok 0x5a5a5a5a),
      (.ok 0x1122334455667788, .ok 0x89abcdef, .ok 0x5a5a5a5a)] := by rfl

theorem outside_bytes : ([0x0fff, 0x1008, 0x3006] : List Word).map
    (view ram pending).read = [some 0x5a, some 0x5a, none] := by rfl

theorem outside_data_fault : loadQWord (view ram pending) 0x3000 =
    .error (.inaccessibleData 0x3006) := by rfl

theorem outside_stack_fault : readWord (view ram pending) 0x3000 =
    .error (.inaccessibleStack 0x3006) := by rfl

theorem upper_permission_checked :
    (canStoreDWord (view ram pending) 0x2000, canStoreQWord (view ram pending) 0x2000,
      (storeQWord (view ram pending) 0x2000 7).map (fun _ => true)) =
    (true, false, .error (.writeDenied 0x2000)) := by rfl

/-- Permissions deliberately differ within a pending qword's own footprint. -/
def protectedRam : Memory :=
  { ram with
    executable := fun address => address == 0x1006
    writable := fun address => address != 0x1007 }

theorem buffered_permissions :
    ((view protectedRam pending).executable 0x1006,
      (view protectedRam pending).executable 0x1007,
      (view protectedRam pending).writable 0x1006,
      (view protectedRam pending).writable 0x1007,
      (storeQWord (view protectedRam pending) 0x1000 7).map (fun _ => true)) =
    (true, false, true, false, .error (.writeDenied 0x1000)) := by rfl

theorem fetch_outside : fetchByte (view ram pending) 0x40 = .ok 0x5a := by rfl

-- The frame theorem transports arbitrary code evidence, using only the
-- independent concrete separation of this buffer and a two-byte code region.
theorem transport_code (memory : Memory) (code : CodeAt memory 0x40 [0x90, 0xc3]) :
    CodeAt (view memory pending) 0x40 [0x90, 0xc3] := by
  apply view_code memory pending 0x40 [0x90, 0xc3] code
  intro store member
  have choices : store = wide ∨ store = narrow := by
    simpa [pending] using member
  rcases choices with rfl | rfl <;>
    intro offset bound <;>
    rcases (show offset = 0 ∨ offset = 1 by change offset < 2 at bound; omega) with
      rfl | rfl <;> decide

-- This is a functional overlay, including at modular addresses. The production
-- checked loads still reject wrapped and noncanonical operands.
theorem unchecked_wrap_bytes : ([0xffffffffffffffff, 0, 6, 7] : List Word).map
    (view ram [⟨0xffffffffffffffff, .qword 0x1122334455667788⟩]).read =
    [some 0x88, some 0x77, some 0x11, some 0x5a] := by rfl

theorem wrapped_load_rejected : loadQWord
    (view ram [⟨0xffffffffffffffff, .qword 0x1122334455667788⟩]) 0xffffffffffffffff =
    .error (.inaccessibleData 0xffffffffffffffff) := by rfl

theorem noncanonical_load_rejected : loadQWord
    (view ram [⟨0x800000000000, .qword 0x1122334455667788⟩]) 0x800000000000 =
    .error (.inaccessibleData 0x800000000000) := by rfl

end EDSL.Tests.MixedStoreBuffer

#audit_edsl
