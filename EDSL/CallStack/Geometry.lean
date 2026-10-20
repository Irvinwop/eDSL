/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Resources

set_option warningAsError true

namespace EDSL.CallStack
open X86 OS

/-- A whole qword at a natural depth below the original caller slot. Depth is
bounded by the current allocation, so subtraction cannot wrap. -/
theorem private_slot_at_depth {frame : StackFrame.Descriptor} {shared : Borrowing.State}
    (contract : StackFrame.Contract frame shared) {depth : Nat}
    (minimum : 8 ≤ depth) (maximum : depth ≤ frame.capacity) :
    StackFrame.Slot frame (frame.top - BitVec.ofNat 64 depth) := by
  have below : depth ≤ frame.top.toNat := Nat.le_trans maximum contract.topBound
  have small : depth < 2^64 := Nat.lt_of_le_of_lt below frame.top.isLt
  have depthNat : (BitVec.ofNat 64 depth).toNat = depth := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  have natural : (frame.top - BitVec.ofNat 64 depth).toNat = frame.top.toNat - depth := by
    rw [BitVec.toNat_sub_of_le (by change (BitVec.ofNat 64 depth).toNat ≤ frame.top.toNat; rw [depthNat]; exact below), depthNat]
  have bounds := contract.region_bounds
  change frame.region.base.toNat ≤ (frame.top - BitVec.ofNat 64 depth).toNat ∧
    (frame.top - BitVec.ofNat 64 depth).toNat + 8 ≤ frame.region.base.toNat + frame.region.length
  rw [natural, bounds.2, bounds.1]
  omega

theorem private_depth_ne_top {frame : StackFrame.Descriptor} {shared : Borrowing.State}
    (contract : StackFrame.Contract frame shared) {depth : Nat}
    (positive : 0 < depth) (maximum : depth ≤ frame.capacity) :
    frame.top - BitVec.ofNat 64 depth ≠ frame.top := by
  have below : depth ≤ frame.top.toNat := Nat.le_trans maximum contract.topBound
  have small : depth < 2^64 := Nat.lt_of_le_of_lt below frame.top.isLt
  intro equal
  have same := congrArg BitVec.toNat equal
  have le : BitVec.ofNat 64 depth ≤ frame.top := by
    change (BitVec.ofNat 64 depth).toNat ≤ frame.top.toNat
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using below
  rw [BitVec.toNat_sub_of_le le] at same
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at same
  omega

end EDSL.CallStack
