/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.Clang.Local

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.Clang
open X86 OS

/-- The exit cutpoint is selected exactly when the natural remaining count is
zero. The original descriptor and saved RAM words are retained at both points. -/
structure Loop (d : OS.CallMemory64.Descriptor) (saved14 savedBX value : Word)
    (remaining : Nat) (s : State) : Prop where
  pc : s.rip = d.frame.call.code + if remaining = 0 then 37 else 18
  stack : s.registers .rsp = d.frame.top - 24
  pointer : s.registers .r14 = d.target
  accumulator : s.registers .rax = value
  counter : s.registers .rbx = BitVec.ofNat 64 remaining
  saved : Saved d saved14 savedBX s

/-- One actual nine-instruction iteration, including checked CALL, DATA
store/reload, RAM-derived private RET, and the ZF-dependent backedge. -/
theorem iteration {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    {a b value : Word} {n : Nat} (current : OS.CallMemory64.Current d w s)
    (same : d.frame.call.bytes = text) (capacity : 32 ≤ d.frame.capacity)
    (bound : n + 1 < 2^64) (inv : Loop d a b value (n + 1) s) (choices : CallReturn.Choices) :
    ∃ evolved after, Block d choices w s evolved after 9 ∧
      Loop d a b (value + 1) n after ∧ Frame s after ∧
      readWord after.memory d.target = .ok value := by
  have pc0 : s.rip = d.frame.call.code + 18 := by simpa using inv.pc
  let s1 := mov s .rdi .r14
  have one1 : One d (choices 0) w w s s1 := mov_one current same
    (by decide : (18, .sequential (.movReg64 .rdi .r14)) ∈ Compiler.sites .clangSeparate) pc0 (choices 0)
  have c1 : OS.CallMemory64.Current d w s1 := one1.current current
  have pc1 : s1.rip = d.frame.call.code + 21 := by simp [s1, mov, pc0, BitVec.add_assoc]
  let s2 := mov s1 .rsi .rax
  have one2 : One d (choices 1) w w s1 s2 := mov_one c1 same
    (by decide : (21, .sequential (.movReg64 .rsi .rax)) ∈ Compiler.sites .clangSeparate) pc1 (choices 1)
  have c2 : OS.CallMemory64.Current d w s2 := one2.current c1
  have pc2 : s2.rip = d.frame.call.code + 24 := by simp [s2, mov, pc1, BitVec.add_assoc]
  have dest : CallReturn.stackDestination s2 = d.frame.top - 32 := by
    simp [CallReturn.stackDestination, s2, s1, mov, State.writeRegister, inv.stack, BitVec.sub_sub]
  have slotCall : StackFrame.Slot d.frame (CallReturn.stackDestination s2) := by
    rw [dest]
    exact slot c2 capacity (by decide : 8 ≤ 32) (by decide)
  obtain ⟨w3, step3, effect3, read3⟩ := call_step c2 same pc2 slotCall (choices 2)
  let s3 := call s2
  have c3 : OS.CallMemory64.Current d w3 s3 := step3.current c2
  have one3 : One d (choices 2) w w3 s2 s3 :=
    ⟨[], step3, fetch c2 same
      (by decide : (24, .callRelative32 16) ∈ Compiler.sites .clangSeparate) pc2⟩
  have pc3 : s3.rip = d.frame.call.code + 45 := by
    simp [s3, call, CallReturn.callState, CallReturn.callTarget, CallReturn.returnAddress,
      pc2, BitVec.add_assoc]
  have continuation : CallReturn.returnAddress s2 = d.frame.call.code + 29 := by
    simp [CallReturn.returnAddress, pc2, BitVec.add_assoc]
  have stack3 : s3.registers .rsp = d.frame.top - 32 := by
    simp [s3, call, CallReturn.callState, State.writeRegister, dest]
  have ptr3 : s3.registers .rdi = d.target := by
    simp [s3, call, CallReturn.callState, s2, s1, mov, State.writeRegister, inv.pointer]
  have arg3 : s3.registers .rsi = value := by
    simp [s3, call, CallReturn.callState, s2, s1, mov, State.writeRegister, inv.accumulator]
  obtain ⟨w4, step4, effect4, owned4⟩ := store_step c3 same pc3 ptr3 arg3 (choices 3)
  let s4 := store s3 w4
  have c4 : OS.CallMemory64.Current d w4 s4 := step4.current c3
  have one4 : One d (choices 3) w3 w4 s3 s4 :=
    ⟨[], step4, fetch c3 same
      (by decide : (45, .sequential (.storeMem64 (.base .rdi) .rsi)) ∈ Compiler.sites .clangSeparate) pc3⟩
  have pc4 : s4.rip = d.frame.call.code + 48 := by
    simp [s4, store, WordResources64.storeAfterLength, pc3, BitVec.add_assoc]
  have ptr4 : s4.registers .rdi = d.target := ptr3
  have step5 := load_step c4 same pc4 ptr4 owned4 (choices 4)
  let s5 := load s4 value
  have c5 : OS.CallMemory64.Current d w4 s5 := step5.current c4
  have one5 : One d (choices 4) w4 w4 s4 s5 :=
    ⟨_, step5, fetch c4 same
      (by decide : (48, .sequential (.loadMem64 .rax (.base .rdi))) ∈ Compiler.sites .clangSeparate) pc4⟩
  have pc5 : s5.rip = d.frame.call.code + 51 := by simp [s5, load, pc4, BitVec.add_assoc]
  have stack5 : s5.registers .rsp = d.frame.top - 32 := by
    simp [s5, load, State.writeRegister, s4, store, WordResources64.storeAfterLength, stack3]
  have callRead : readWord s3.memory (d.frame.top - 32) = .ok (d.frame.call.code + 29) := by
    change readWord s3.memory (CallReturn.stackDestination s2) =
      .ok (CallReturn.returnAddress s2) at read3
    rwa [dest, continuation] at read3
  have keptCall : readWord s4.memory (d.frame.top - 32) = readWord s3.memory (d.frame.top - 32) :=
    OS.CallMemory64.data_preserves_private c3 c4 effect4
      (slot c3 capacity (by decide : 8 ≤ 32) (by decide))
  have retRead : readWord s5.memory (s5.registers .rsp) = .ok (d.frame.call.code + 29) := by
    rw [stack5]
    exact keptCall.trans callRead
  have slotRet : StackFrame.Slot d.frame (s5.registers .rsp) := by
    rw [stack5]
    exact slot c5 capacity (by decide : 8 ≤ 32) (by decide)
  have step6 := inner_ret_step c5 same pc5 slotRet retRead (choices 5)
  let s6 := ret s5 (d.frame.call.code + 29)
  have c6 : OS.CallMemory64.Current d w4 s6 := step6.current c5
  have one6 : One d (choices 5) w4 w4 s5 s6 :=
    ⟨_, step6, fetch c5 same
      (by decide : (51, .sequential (.legacy .ret)) ∈ Compiler.sites .clangSeparate) pc5⟩
  have pc6 : s6.rip = d.frame.call.code + 29 := rfl
  let s7 := inc s6
  have one7 : One d (choices 6) w4 w4 s6 s7 := plain_one c6 same
    (by decide : (29, .sequential (.inc64 .rax)) ∈ Compiler.sites .clangSeparate) pc6 rfl rfl rfl
  have c7 : OS.CallMemory64.Current d w4 s7 := one7.current c6
  have pc7 : s7.rip = d.frame.call.code + 32 := by simp [s7, inc, pc6, BitVec.add_assoc]
  let s8 := dec s7
  have one8 : One d (choices 7) w4 w4 s7 s8 := plain_one c7 same
    (by decide : (32, .sequential (.dec64 .rbx)) ∈ Compiler.sites .clangSeparate) pc7 rfl rfl rfl
  have c8 : OS.CallMemory64.Current d w4 s8 := one8.current c7
  have pc8 : s8.rip = d.frame.call.code + 35 := by simp [s8, dec, pc7, BitVec.add_assoc]
  have count7 : s7.registers .rbx = BitVec.ofNat 64 (n + 1) := by
    simp [s7, inc, s6, ret, s5, load, s4, store, WordResources64.storeAfterLength,
      s3, call, CallReturn.callState, s2, s1, mov, State.writeRegister, inv.counter]
  have zero8 : s8.flags.getLsbD 6 = (BitVec.ofNat 64 n == (0 : Word)) := by
    change (Sequential.decFlags64 s7.flags (s7.registers .rbx)).getLsbD 6 = _
    rw [(Sequential.decFlags64_bits ..).2.2.2.1, count7, ofNat_succ, BitVec.add_sub_cancel]
  let s9 := jump s8 (d.frame.call.code + if n = 0 then 37 else 18)
  have one9 := jnz_one c8 same pc8 (by omega : n < 2^64) zero8 (choices 8)
  have saved2 : Saved d a b s2 := inv.saved.sameMemory rfl
  have callEffect : Borrowing.StoreEffect64 w w3 (d.frame.top - 32) (CallReturn.returnAddress s2) := by
    change Borrowing.StoreEffect64 w w3 (CallReturn.stackDestination s2)
      (CallReturn.returnAddress s2) at effect3
    rwa [dest] at effect3
  have saved3 : Saved d a b s3 := saved2.private c2 c3 capacity (by decide : 24 ≤ 32)
    (by decide) callEffect
  have saved4 : Saved d a b s4 := saved3.data c3 c4 capacity effect4
  have data4 : readWord s4.memory d.target = .ok value := by
    rw [c4.coupled]
    exact readWord_of_loadQWord _ _ _ effect4.readback
  refine ⟨w4, s9, ?_, ?_, ?_, ?_⟩
  · apply Block.cons one1
    apply Block.cons one2
    apply Block.cons one3
    apply Block.cons one4
    apply Block.cons one5
    apply Block.cons one6
    apply Block.cons one7
    apply Block.cons one8
    exact one9.block
  · refine ⟨rfl, ?_, ?_, ?_, ?_, saved4.sameMemory rfl⟩
    · simp [s9, jump, s8, dec, s7, inc, s6, ret, State.writeRegister, stack5,
        BitVec.sub_eq_add_neg, BitVec.add_assoc]
    · simp [s9, jump, s8, dec, s7, inc, s6, ret, s5, load, s4, store,
        WordResources64.storeAfterLength, s3, call, CallReturn.callState, s2, s1, mov,
        State.writeRegister, inv.pointer]
    · simp [s9, jump, s8, dec, s7, inc, s6, ret, s5, load, State.writeRegister]
    · change s7.registers .rbx - 1 = BitVec.ofNat 64 n
      rw [count7, ofNat_succ, BitVec.add_sub_cancel]
  · exact (frame_mov s .rdi .r14 (by decide)).trans
      ((frame_mov s1 .rsi .rax (by decide)).trans ((frame_call s2).trans
        ((frame_store s3 w4).trans ((frame_load s4 value).trans
          ((frame_ret s5 _).trans ((frame_inc s6).trans
            ((frame_dec s7).trans (frame_jump s8 _))))))))
  · exact data4

end EDSL.CallMemoryLoop64.Clang
