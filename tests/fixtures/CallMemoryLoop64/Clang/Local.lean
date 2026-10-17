/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.Clang.Steps
import EDSL.X86.Sequential.ShortBranch

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.Clang
open X86 OS

/-- A real mixed instruction together with its complete fetch extent. -/
inductive One (d : OS.CallMemory64.Descriptor) (af : Bool) (w v : Borrowing.State)
    (s t : State) : Prop where
  | intro (reads : List CallReturn.Read)
      (step : OS.CallMemory64.CPU.Step d w v s t af ⟨.next t, reads⟩)
      (fetch : CallStack.FetchWithin d.frame s)

theorem One.current {d af w v s t} (one : One d af w v s t)
    (current : OS.CallMemory64.Current d w s) : OS.CallMemory64.Current d v t := by
  obtain ⟨_, step, _⟩ := one
  exact step.current current

inductive Block (d : OS.CallMemory64.Descriptor) (choices : CallReturn.Choices)
    (w : Borrowing.State) (s : State) (v : Borrowing.State) (t : State) (count : Nat) : Prop where
  | intro (reads : List CallReturn.Read)
      (history : OS.CallMemory64.CoveredHistory d choices w s v t count reads)

theorem Block.nil {d choices w s} : Block d choices w s w s 0 := ⟨[], .nil⟩

theorem One.block {d choices w v s t} (one : One d (choices 0) w v s t) :
    Block d choices w s v t 1 := by
  obtain ⟨reads, step, fetch⟩ := one
  exact ⟨reads, by simpa using OS.CallMemory64.CoveredHistory.next step fetch .nil⟩

theorem Block.cons {d choices w v z s t u count}
    (one : One d (choices 0) w v s t) (tail : Block d (choices.drop 1) v t z u count) :
    Block d choices w s z u (count + 1) := by
  obtain ⟨reads, step, fetch⟩ := one
  obtain ⟨rest, history⟩ := tail
  exact ⟨reads ++ rest, .next step fetch history⟩

theorem Block.current {d choices w v s t count} (block : Block d choices w s v t count)
    (current : OS.CallMemory64.Current d w s) : OS.CallMemory64.Current d v t := by
  obtain ⟨_, history⟩ := block
  exact history.current current

theorem Block.trans {d choices w v z s t u count more}
    (first : Block d choices w s v t count)
    (last : Block d (choices.drop count) v t z u more) :
    Block d choices w s z u (count + more) := by
  obtain ⟨reads, firstHistory⟩ := first
  obtain ⟨rest, suffix⟩ := last
  exact ⟨reads ++ rest, firstHistory.trans suffix⟩

theorem Block.finish {d choices w v z s t result count}
    (first : Block d choices w s v t count)
    (last : OS.CallMemory64.CoveredExecution d (choices.drop count) v t z result) :
    ∃ combined, OS.CallMemory64.CoveredExecution d choices w s z combined ∧
      combined.state = result.state ∧ combined.instructions = count + result.instructions := by
  obtain ⟨reads, firstHistory⟩ := first
  exact ⟨result.prepend count reads, firstHistory.then_execution last, rfl, rfl⟩

theorem plain_one {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s t : State}
    {off : Nat} {op : CallReturn.Instruction} {af : Bool}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (member : (off, op) ∈ Compiler.sites .clangSeparate)
    (pc : s.rip = d.frame.call.code + BitVec.ofNat 64 off)
    (actual : CallReturn.execute s op af = .ok ⟨.next t, []⟩)
    (noWrite : op.writeEffect s = none) (memory : t.memory = s.memory) : One d af w w s t :=
  ⟨[], plain_step current same member pc actual noWrite memory, fetch current same member pc⟩

theorem mov_one {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    {off : Nat} {dst src : Register} (current : OS.CallMemory64.Current d w s)
    (same : d.frame.call.bytes = text)
    (member : (off, .sequential (.movReg64 dst src)) ∈ Compiler.sites .clangSeparate)
    (pc : s.rip = d.frame.call.code + BitVec.ofNat 64 off) (af : Bool) :
    One d af w w s (mov s dst src) := plain_one current same member pc rfl rfl rfl

theorem depth_nat {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    (current : OS.CallMemory64.Current d w s) (capacity : 32 ≤ d.frame.capacity)
    {depth : Nat} (bound : depth ≤ 32) :
    (d.frame.top - BitVec.ofNat 64 depth).toNat = d.frame.top.toNat - depth := by
  have below : depth ≤ d.frame.top.toNat :=
    Nat.le_trans bound (Nat.le_trans capacity current.contract.stack.topBound)
  have small : depth < 2^64 := Nat.lt_of_le_of_lt below d.frame.top.isLt
  have wordNat : (BitVec.ofNat 64 depth).toNat = depth := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  have le : BitVec.ofNat 64 depth ≤ d.frame.top := by
    change (BitVec.ofNat 64 depth).toNat ≤ d.frame.top.toNat
    rw [wordNat]
    exact below
  rw [BitVec.toNat_sub_of_le le, wordNat]

private theorem sub_slot_gap {top a b : Nat} (below : b ≤ top) (gap : a + 8 ≤ b) :
    top - b + 8 ≤ top - a :=
  Nat.le_sub_of_add_le (calc
    top - b + 8 + a = top - b + (a + 8) := by
      rw [Nat.add_assoc, Nat.add_comm 8 a]
    _ ≤ top - b + b := Nat.add_le_add_left gap _
    _ = top := Nat.sub_add_cancel below)

theorem slots_disjoint {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    (current : OS.CallMemory64.Current d w s) (capacity : 32 ≤ d.frame.capacity)
    {a b : Nat} (aBound : a ≤ 32) (bBound : b ≤ 32)
    (gap : a + 8 ≤ b ∨ b + 8 ≤ a) :
    Ownership.Disjoint (AddressSpace.qwordRegion (d.frame.top - BitVec.ofNat 64 a))
      (AddressSpace.qwordRegion (d.frame.top - BitVec.ofNat 64 b)) := by
  have first := depth_nat current capacity aBound
  have last := depth_nat current capacity bBound
  change (d.frame.top - BitVec.ofNat 64 a).toNat + 8 ≤
      (d.frame.top - BitVec.ofNat 64 b).toNat ∨
    (d.frame.top - BitVec.ofNat 64 b).toNat + 8 ≤
      (d.frame.top - BitVec.ofNat 64 a).toNat
  rw [first, last]
  cases gap with
  | inl gap => exact Or.inr (sub_slot_gap
      (Nat.le_trans bBound (Nat.le_trans capacity current.contract.stack.topBound)) gap)
  | inr gap => exact Or.inl (sub_slot_gap
      (Nat.le_trans aBound (Nat.le_trans capacity current.contract.stack.topBound)) gap)

theorem slot {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    (current : OS.CallMemory64.Current d w s) (capacity : 32 ≤ d.frame.capacity)
    {depth : Nat} (minimum : 8 ≤ depth) (maximum : depth ≤ 32) :
    StackFrame.Slot d.frame (d.frame.top - BitVec.ofNat 64 depth) :=
  CallStack.private_slot_at_depth current.contract.stack minimum (Nat.le_trans maximum capacity)

/-- Actual current saved register contents, with no immutable-stack premise. -/
structure Saved (d : OS.CallMemory64.Descriptor) (r14 rbx : Word) (s : State) : Prop where
  high : readWord s.memory (d.frame.top - 8) = .ok r14
  low : readWord s.memory (d.frame.top - 16) = .ok rbx

theorem Saved.sameMemory {d a b s t} (saved : Saved d a b s) (same : t.memory = s.memory) :
    Saved d a b t := ⟨same ▸ saved.high, same ▸ saved.low⟩

theorem Saved.private {d : OS.CallMemory64.Descriptor} {w v : Borrowing.State}
    {s t : State} {a b value : Word} {depth : Nat}
    (saved : Saved d a b s) (first : OS.CallMemory64.Current d w s)
    (last : OS.CallMemory64.Current d v t) (capacity : 32 ≤ d.frame.capacity)
    (lower : 24 ≤ depth) (upper : depth ≤ 32)
    (effect : Borrowing.StoreEffect64 w v (d.frame.top - BitVec.ofNat 64 depth) value) :
    Saved d a b t := by
  refine ⟨?_, ?_⟩
  · exact (OS.CallMemory64.store64_preserves_private first last effect
      (slot first capacity (by decide : 8 ≤ 8) (by decide))
      (slots_disjoint first capacity upper (by decide : 8 ≤ 32)
        (Or.inr (Nat.le_trans (by decide : 16 ≤ 24) lower)))).trans saved.high
  · exact (OS.CallMemory64.store64_preserves_private first last effect
      (slot first capacity (by decide : 8 ≤ 16) (by decide))
      (slots_disjoint first capacity upper (by decide : 16 ≤ 32) (Or.inr lower))).trans saved.low

theorem Saved.data {d : OS.CallMemory64.Descriptor} {w v : Borrowing.State}
    {s t : State} {a b value : Word} (saved : Saved d a b s)
    (first : OS.CallMemory64.Current d w s) (last : OS.CallMemory64.Current d v t)
    (capacity : 32 ≤ d.frame.capacity) (effect : Borrowing.StoreEffect64 w v d.target value) :
    Saved d a b t :=
  ⟨(OS.CallMemory64.data_preserves_private first last effect
      (slot first capacity (by decide : 8 ≤ 8) (by decide))).trans saved.high,
    (OS.CallMemory64.data_preserves_private first last effect
      (slot first capacity (by decide : 8 ≤ 16) (by decide))).trans saved.low⟩

theorem ofNat_zero_iff {n : Nat} (bound : n < 2^64) : (BitVec.ofNat 64 n : Word) = 0 ↔ n = 0 := by
  constructor
  · intro zero
    have same := congrArg BitVec.toNat zero
    have natural : (BitVec.ofNat 64 n).toNat = n := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    rw [natural] at same
    exact same
  · rintro rfl
    rfl

theorem ofNat_succ (n : Nat) : (BitVec.ofNat 64 (n + 1) : Word) = BitVec.ofNat 64 n + 1 := by
  rw [BitVec.ofNat_add]
  rfl

theorem je_one {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (pc : s.rip = d.frame.call.code + 6) (zero : s.flags.getLsbD 6 = true) (af : Bool) :
    One d af w w s (jump s (d.frame.call.code + 44)) := by
  have target : s.rip + 2 + (0x24 : Byte).signExtend 64 = d.frame.call.code + 44 := by
    simp only [pc, BitVec.add_assoc]
    congr 1
  have canon : canonical (d.frame.call.code + 44) = true :=
    Sequential.code_canonical_offset (current_code current same) 44 (by decide)
  apply plain_one current same
    (by decide : (6, .sequential (.je 0x24)) ∈ Compiler.sites .clangSeparate) pc
  · simp only [CallReturn.execute_sequential, Sequential.execute_je, zero, executeShortBranch,
      ↓reduceIte, target, canon, ok_bind, pure_ok]
    rfl
  · rfl
  · rfl

theorem jne_fallthrough {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (pc : s.rip = d.frame.call.code + 6) (zero : s.flags.getLsbD 6 = false) (af : Bool) :
    One d af w w s (jump s (d.frame.call.code + 8)) := by
  apply plain_one current same
    (by decide : (6, .sequential (.je 0x24)) ∈ Compiler.sites .clangSeparate) pc
  · simp only [CallReturn.execute_sequential, Sequential.execute_je, zero, executeShortBranch,
      Bool.false_eq_true, ↓reduceIte, ok_bind, pure_ok]
    simp [jump, pc, BitVec.add_assoc]
  · rfl
  · rfl

theorem jnz_one {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State} {n : Nat}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (pc : s.rip = d.frame.call.code + 35) (bound : n < 2^64)
    (zero : s.flags.getLsbD 6 = (BitVec.ofNat 64 n == (0 : Word))) (af : Bool) :
    One d af w w s (jump s (d.frame.call.code + if n = 0 then 37 else 18)) := by
  have target : s.rip + 2 + (0xed : Byte).signExtend 64 = d.frame.call.code + 18 := by
    simp only [pc, BitVec.add_assoc]
    congr 1
  have fallthrough : s.rip + 2 = d.frame.call.code + 37 := by
    rw [pc, BitVec.add_assoc]
    rfl
  have canon : canonical (d.frame.call.code + 18) = true :=
    Sequential.code_canonical_offset (current_code current same) 18 (by decide)
  apply plain_one current same
    (by decide : (35, .sequential (.legacy (.jnz 0xed))) ∈ Compiler.sites .clangSeparate) pc
  · rw [CallReturn.execute_sequential,
      Sequential.execute_shortBranch_context s (.notEqual 0xed)
        (fun _ => (congrArg canonical target).trans canon) af]
    by_cases empty : n = 0
    · have condition : Sequential.Condition.notEqual.holds s.flags = false := by
        change (!s.flags.getLsbD 6) = false
        rw [zero, (ofNat_zero_iff bound).mpr empty]
        rfl
      simp only [Sequential.shortBranchTarget, condition, Bool.false_eq_true, ↓reduceIte,
        jump, ite_eq_left empty, fallthrough]
    · have nonzero : (BitVec.ofNat 64 n : Word) ≠ 0 := fun h => empty ((ofNat_zero_iff bound).mp h)
      have condition : Sequential.Condition.notEqual.holds s.flags = true := by
        change (!s.flags.getLsbD 6) = true
        rw [zero, beq_eq_false_iff_ne.mpr nonzero]
        rfl
      simp only [Sequential.shortBranchTarget, condition, ↓reduceIte,
        target, jump, ite_eq_right empty]
  · rfl
  · rfl

end EDSL.CallMemoryLoop64.Clang
