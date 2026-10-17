/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.GCC.Facts

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.GCC
open X86 OS

theorem accumulator_step (value : Word) (remaining : Nat) :
    (value + 1) + BitVec.ofNat 64 remaining = value + BitVec.ofNat 64 (remaining + 1) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  congr 1
  exact BitVec.add_comm _ _

/-- One complete iteration consists of ten actual covered instructions. CALL
writes S-32, the helper stores and reloads current DATA, and its RET reads the
actual S-32 word. Only the final original-slot RET is a terminal observation. -/
theorem body {resource : Resources} {initial state : State} {shared : Shared} {remaining : Nat}
    (same : resource.descriptor.frame.call.bytes = text)
    (capacity : 32 ≤ resource.descriptor.frame.capacity)
    (current : Current resource.descriptor shared state)
    (inv : Invariant resource initial state (remaining + 1)) (choices : CallReturn.Choices) :
    ∃ evolved middle reads, CoveredHistory resource.descriptor choices shared state evolved middle 10 reads ∧
      Current resource.descriptor evolved middle ∧ Invariant resource initial middle remaining := by
  have nonzero : state.registers .rbx ≠ 0 := by
    intro zero
    have count := inv.counter
    rw [zero] at count
    simp at count
  let s1 := tested state (choices 0)
  have step0 := test_next current same inv.pc (choices 0)
  have c1 : Current resource.descriptor shared s1 := step0.current current
  have pc1 : s1.rip = resource.descriptor.frame.call.code + 12 := by
    simp [s1, tested, inv.pc, BitVec.add_assoc]
  have flag : s1.flags.getLsbD 6 = false := by
    change (Sequential.logicalFlags64 state.flags (state.registers .rbx) (choices 0)).getLsbD 6 = false
    rw [Sequential.logicalFlags64_zero]
    exact beq_eq_false_iff_ne.mpr nonzero
  let s2 := atPC s1 (resource.descriptor.frame.call.code + 14)
  have step1 : Next resource.descriptor shared shared s1 s2 ((choices.drop 1) 0) :=
    guard_next c1 same pc1 flag ((choices.drop 1) 0)
  have c2 := step1.current c1
  let s3 := moved s2 .rdi .rbp
  have step2 := move_next c2 same
    (by decide : (14, .sequential (.movReg64 .rdi .rbp)) ∈ Compiler.sites .gccSeparate) rfl
    (((choices.drop 1).drop 1) 0)
  have c3 : Current resource.descriptor shared s3 := step2.current c2
  have pc3 : s3.rip = resource.descriptor.frame.call.code + 17 := by
    simp [s3, moved, s2, atPC, BitVec.add_assoc]
  let s4 := decremented s3
  have step3 := decrement_next c3 same pc3 ((((choices.drop 1).drop 1).drop 1) 0)
  have c4 : Current resource.descriptor shared s4 := step3.current c3
  have pc4 : s4.rip = resource.descriptor.frame.call.code + 20 := by
    simp [s4, decremented, pc3, BitVec.add_assoc]
  have slotEq : CallReturn.stackDestination s4 = resource.descriptor.frame.top - 32 := by
    change state.registers .rsp - 8 = _
    rw [inv.stack, BitVec.sub_sub]
    rfl
  have callSlot : StackFrame.Slot resource.descriptor.frame (CallReturn.stackDestination s4) := by
    rw [slotEq]
    exact depth_slot c4 capacity (by decide : 8 ≤ 32) (by decide)
  let s5 := called s4
  obtain ⟨w5, step4, _, effect4, read4⟩ := call_next c4 same pc4 callSlot
    (((((choices.drop 1).drop 1).drop 1).drop 1) 0)
  have c5 : Current resource.descriptor w5 s5 := step4.current c4
  have pc5 : s5.rip = resource.descriptor.frame.call.code + 38 := by
    simp [s5, called, CallReturn.callState, CallReturn.callTarget, CallReturn.returnAddress, pc4, BitVec.add_assoc]
  have pointer5 : s5.registers .rdi = resource.descriptor.target := inv.pointer
  let s6world : Shared → State := stored s5
  obtain ⟨w6, step5, effect5, owned5⟩ := store_next c5 same pc5 pointer5
    ((((((choices.drop 1).drop 1).drop 1).drop 1).drop 1) 0)
  let s6 := s6world w6
  have c6 : Current resource.descriptor w6 s6 := step5.current c5
  have pc6 : s6.rip = resource.descriptor.frame.call.code + 41 := by
    simp [s6, s6world, stored, WordResources64.storeAfterLength, pc5, BitVec.add_assoc]
  have pointer6 : s6.registers .rdi = resource.descriptor.target := pointer5
  have owned6 : Borrowing.loadOwnedWord64 w6 resource.descriptor.owner resource.descriptor.ticket
      resource.descriptor.target = .ok (state.registers .rsi) := owned5
  let s7 := loaded s6 (state.registers .rsi)
  have step6 := load_next c6 same pc6 pointer6 owned6
    (((((((choices.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1) 0)
  have c7 : Current resource.descriptor w6 s7 := step6.current c6
  have pc7 : s7.rip = resource.descriptor.frame.call.code + 44 := by
    simp [s7, loaded, pc6, BitVec.add_assoc]
  have sp7 : s7.registers .rsp = CallReturn.stackDestination s4 := rfl
  have innerSlot : StackFrame.Slot resource.descriptor.frame (s7.registers .rsp) := by
    rw [sp7]
    exact callSlot
  have continuation : CallReturn.returnAddress s4 = resource.descriptor.frame.call.code + 25 := by
    simp [CallReturn.returnAddress, pc4, BitVec.add_assoc]
  have read7 : readWord s7.memory (s7.registers .rsp) = .ok (resource.descriptor.frame.call.code + 25) := by
    rw [sp7]
    exact ((OS.CallMemory64.data_preserves_private c5 c6 effect5 callSlot).trans read4).trans
      (congrArg Except.ok continuation)
  have canon : canonical (resource.descriptor.frame.call.code + 25) = true :=
    Sequential.code_canonical_offset (current_code c7 same) 25 (by decide)
  let s8 := finished s7 (resource.descriptor.frame.call.code + 25)
  have step7 := inner_ret_next c7 same pc7 innerSlot read7 canon
    ((((((((choices.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1) 0)
  have c8 : Current resource.descriptor w6 s8 := step7.current c7
  let s9 := advanced s8
  have step8 := advance_next c8 same rfl
    (((((((((choices.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1) 0)
  have c9 : Current resource.descriptor w6 s9 := step8.current c8
  have pc9 : s9.rip = resource.descriptor.frame.call.code + 29 := by
    simp [s9, advanced, CallReturn.leaState, CallReturn.Instruction.length, s8, finished, BitVec.add_assoc]
  let s10 := atPC s9 (resource.descriptor.frame.call.code + 9)
  have step9 := back_next c9 same pc9
    ((((((((((choices.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1).drop 1) 0)
  have c10 : Current resource.descriptor w6 s10 := step9.current c9
  have history : CoveredHistory resource.descriptor choices shared state w6 s10 10
      [⟨.data, resource.descriptor.target, 8⟩, ⟨.stack, s7.registers .rsp, 8⟩] :=
    .next step0.step step0.fetch (.next step1.step step1.fetch (.next step2.step step2.fetch
      (.next step3.step step3.fetch (.next step4.step step4.fetch (.next step5.step step5.fetch
        (.next step6.step step6.fetch (.next step7.step step7.fetch (.next step8.step step8.fetch
          (.next step9.step step9.fetch .nil)))))))))
  have saved4 : Saved resource.descriptor initial s4 := inv.saved.sameMemory rfl
  have saved5 : Saved resource.descriptor initial s5 :=
    saved4.private_store c4 c5 capacity effect4 slotEq
  have saved6 : Saved resource.descriptor initial s6 := saved5.data_store c5 c6 capacity effect5
  have saved10 : Saved resource.descriptor initial s10 := saved6.sameMemory rfl
  have target : readWord s6.memory resource.descriptor.target = .ok (state.registers .rsi) := by
    rw [c6.coupled]
    exact Borrowing.loadOwnedWord64_readWord _ _ _ _ _ owned6
  have frame : Frame initial s10 := inv.frame.trans ((frame_test state (choices 0)).trans
    ((frame_pc s1 _).trans ((frame_move s2 .rdi .rbp (by decide)).trans
      ((frame_decrement s3).trans ((frame_call s4).trans ((frame_store s5 w6).trans
        ((frame_load s6 _).trans ((frame_finish s7 _).trans ((frame_advance s8).trans (frame_pc s9 _))))))))))
  refine ⟨w6, s10, _, history, c10, ?_⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, saved10, frame⟩
  · change (state.registers .rsp - 8) + 8 = resource.descriptor.frame.top - 24
    simpa only [BitVec.sub_add_cancel] using inv.stack
  · exact inv.pointer
  · change (state.registers .rbx - 1).toNat = remaining
    have enough : (1 : Word) ≤ state.registers .rbx := by
      change 1 ≤ (state.registers .rbx).toNat
      rw [inv.counter]
      omega
    rw [BitVec.toNat_sub_of_le enough, inv.counter]
    simp
  · change (state.registers .rsi + 1) + BitVec.ofNat 64 remaining = resource.value + resource.count
    rw [accumulator_step]
    exact inv.total
  · have bound := inv.remaining_le
    omega
  · change readWord s6.memory resource.descriptor.target =
      if remaining = resource.count.toNat then readWord initial.memory resource.descriptor.target
      else .ok (state.registers .rsi + 1 - 1)
    have different : remaining ≠ resource.count.toNat := by have bound := inv.remaining_le; omega
    simpa only [ite_eq_right different, BitVec.add_sub_cancel] using target

end EDSL.CallMemoryLoop64.GCC
