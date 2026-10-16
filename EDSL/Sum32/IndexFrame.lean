/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.LoopContract

namespace EDSL.Sum32
open X86

namespace IndexProof

/-- The body writes only RAX and RCX. This frame includes the complete
memory and every flag bit outside the arithmetic status mask. -/
structure Frame (initial final : State) : Prop where
  memory : final.memory = initial.memory
  registers : ∀ register, register ≠ .rax → register ≠ .rcx →
    final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem finish_after {initial middle final : State} {accumulator value : BitVec 32}
    {remaining : List (BitVec 32)} {target : Word} (frame : Frame initial middle)
    (post : LoopPost middle (accumulator + value) remaining target final) :
    LoopPost initial accumulator (value :: remaining) target final := by
  refine ⟨?_, post.memory.trans frame.memory, post.returnAddress, ?_, ?_,
    post.flags.trans frame.flags⟩
  · simpa only [sum32_cons, BitVec.add_assoc] using post.value
  · rw [post.stackPointer, frame.registers .rsp (by decide) (by decide)]
  · intro register outside
    have distinct : register ≠ .rax ∧ register ≠ .rcx := by
      simp only [clobbers, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
      exact ⟨outside.1, outside.2.1⟩
    exact (post.preserved register outside).trans
      (frame.registers register distinct.1 distinct.2)

/-- Bounds make equality of the full machine counters faithful to Nat
equality; a counter alias modulo 2^64 cannot terminate this loop early. -/
theorem counter_eq {consumed total : Nat} (ordered : consumed ≤ total)
    (bound : total < 2^64) :
    (BitVec.ofNat 64 total = BitVec.ofNat 64 consumed) ↔ consumed = total := by
  constructor
  · intro same
    have natural := congrArg BitVec.toNat same
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt ordered bound)] using natural.symm
  · intro same
    rw [same]

theorem cmp_zero {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {values : List (BitVec 32)} {accumulator : BitVec 32} {target : Word}
    {consumed total : Nat}
    (header : IndexHeader bytes plan base state values accumulator target consumed total) :
    (Sequential.cmpFlags64 state.flags (state.registers .rsi)
      (state.registers .rcx)).getLsbD 6 = true ↔ consumed = total := by
  rw [Sequential.cmpFlags64_zero, header.count, header.index]
  simp only [beq_iff_eq]
  exact counter_eq (by have := header.remaining; omega) header.countBound

/-- The selected SIB scale multiplies the entire 64-bit index by four.
This equality is modular at the machine width and never truncates to ECX. -/
theorem indexed_address {state : State} {consumed : Nat}
    (index : state.registers .rcx = BitVec.ofNat 64 consumed) :
    (Sequential.Address.indexed .rdi .rcx 2).eval state =
      state.registers .rdi + BitVec.ofNat 64 (4 * consumed) := by
  simp only [Sequential.Address.eval, index]
  congr 1
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 consumed * BitVec.ofNat 64 4 = BitVec.ofNat 64 (4 * consumed)
  rw [Nat.mul_comm 4 consumed, BitVec.ofNat_mul]

theorem next_address (base : Word) (consumed : Nat) :
    base + BitVec.ofNat 64 (4 * (consumed + 1)) =
      (base + BitVec.ofNat 64 (4 * consumed)) + 4 := by
  simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

/-- The generic checked index shape has exactly one full-width INC, at the
contiguous address supplied by the checker rather than a compiler offset. -/
theorem update_layout {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan)
    (mode : plan.mode = .index) :
    plan.updates = [⟨plan.load + 3, .inc64 .rcx⟩] ∧
      plan.back.offset = plan.load + 6 := by
  have updatesValid := (Bool.and_eq_true_iff.mp valid.shape).2
  have mapped : plan.updates.map Node.instruction = [.inc64 .rcx] :=
    of_decide_eq_true (by simpa only [Plan.updatesValid, mode] using updatesValid)
  have length : plan.updates.length = 1 := by
    simpa only [List.length_map, List.length_cons, List.length_nil] using
      congrArg List.length mapped
  obtain ⟨node, nodes⟩ := List.length_eq_one_iff.mp length
  have instruction : node.instruction = .inc64 .rcx := by
    simpa only [nodes, List.map_cons, List.map_nil, List.cons.injEq, and_true] using mapped
  have linear := valid.updates
  rw [nodes] at linear
  have start := linearFrom_cons linear
  have offset : node.offset = plan.load + 3 := by
    simpa only [mode, Mode.load, Sequential.Instruction.length] using start.1
  have finish : plan.back.offset = plan.load + 6 := by
    simpa only [linearFrom, mode, Mode.load, instruction, Sequential.Instruction.length,
      decide_eq_true_eq, Nat.add_assoc] using (of_decide_eq_true
        (show decide (plan.load + plan.mode.load.length + node.instruction.length =
          plan.back.offset) = true from start.2)).symm
  refine ⟨?_, finish⟩
  rw [nodes]
  congr 1
  cases node with
  | mk off ins =>
    simp only at offset instruction
    subst off
    subst ins
    rfl

end IndexProof
end EDSL.Sum32
