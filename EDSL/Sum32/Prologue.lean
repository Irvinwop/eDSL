/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.LoopContract

namespace EDSL.Sum32
open X86

structure ClearEffect (initial final : State) (instruction : SeqInstruction) (destination : Register) : Prop where
  memory : final.memory = initial.memory
  pc : final.rip = initial.rip + BitVec.ofNat 64 instruction.length
  registers : ∀ register, final.registers register = if register = destination then 0 else initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem clear_step {initial : State} {instruction : SeqInstruction} {destination : Register}
    (cleared : clearTarget instruction = some destination) (af : Bool)
    (decoded : Sequential.decodeAt initial = .ok instruction) :
    ∃ final, Sequential.step af initial = .ok ⟨.next final, []⟩ ∧
      ClearEffect initial final instruction destination := by
  rcases clearTarget_some cleared with kind | kind
  · subst instruction
    let final : State := { initial.writeRegister destination 0 with
      rip := initial.rip + 2, flags := Sequential.logicalFlags32 initial.flags 0 af }
    refine ⟨final, ?_, ⟨rfl, rfl, ?_, Sequential.logicalFlags32_preserves ..⟩⟩
    · rw [Sequential.step_eq_execute af decoded, Sequential.execute_xorSelf32]
    · intro register
      rfl
  · subst instruction
    let final := executeMov32 initial destination 0
    refine ⟨final, ?_, ⟨rfl, rfl, ?_, rfl⟩⟩
    · rw [Sequential.step_eq_execute af decoded, Sequential.execute_legacy]
      rfl
    · intro register
      simp [final, executeMov32, State.writeRegister]

structure PrologueEffect (nodes : List Node) (initial final : State) : Prop where
  memory : final.memory = initial.memory
  registers : ∀ register,
    final.registers register = if clears nodes register then 0 else initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

/-- Every admitted initialization block is executable under every AF stream.
The statement describes its semantic effect, independent of byte encodings. -/
theorem prologue_block {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan)
    {base : Word} (nodes : List Node)
    (members : ∀ node ∈ nodes, node ∈ plan.nodes)
    (allowed : nodes.all (fun node => allowedClear node.instruction) = true)
    (start finish : Nat) (linear : linearFrom start nodes finish = true)
    (initial : State) (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 start) (choices : Sequential.Choices) :
    ∃ final, Sequential.Block choices initial final nodes.length [] ∧
      final.rip = base + BitVec.ofNat 64 finish ∧ PrologueEffect nodes initial final := by
  induction nodes generalizing start initial choices with
  | nil =>
    have endpoint : start = finish := of_decide_eq_true linear
    refine ⟨initial, .nil, ?_, ⟨rfl, ?_, rfl⟩⟩
    · simpa only [endpoint] using pc
    · intro register
      rfl
  | cons node rest induction =>
    obtain ⟨atNode, restLinear⟩ := linearFrom_cons linear
    have permitted := (List.all_eq_true.mp allowed) node (by simp)
    obtain ⟨destination, cleared⟩ : ∃ destination, clearTarget node.instruction = some destination := by
      cases selected : clearTarget node.instruction with
      | none => simp [allowedClear, selected] at permitted
      | some destination => exact ⟨destination, rfl⟩
    have decoded := valid.decoded code node (members node (by simp)) initial rfl
      (by simpa only [atNode] using pc)
    obtain ⟨middle, issued, first⟩ := clear_step cleared (choices 0) decoded
    have restMembers : ∀ next ∈ rest, next ∈ plan.nodes :=
      fun next member => members next (List.mem_cons_of_mem node member)
    have restAllowed : rest.all (fun next => allowedClear next.instruction) = true :=
      (Bool.and_eq_true_iff.mp allowed).2
    have nextCode : CodeAt middle.memory base bytes := first.memory ▸ code
    have nextPC : middle.rip = base + BitVec.ofNat 64 (start + node.instruction.length) := by
      rw [first.pc, pc, BitVec.ofNat_add, BitVec.add_assoc]
    obtain ⟨final, block, finalPC, tail⟩ := induction restMembers restAllowed
      (start + node.instruction.length) restLinear middle nextCode nextPC (choices.drop 1)
    refine ⟨final, ?_, finalPC, ⟨tail.memory.trans first.memory, ?_, tail.flags.trans first.flags⟩⟩
    · simpa only [List.length_cons, List.nil_append, Nat.add_comm] using
        (Sequential.Engine.Block.next issued block)
    · intro register
      rw [tail.registers, first.registers]
      by_cases own : register = destination
      · subst register
        simp [clears, cleared]
      · have other : destination ≠ register := Ne.symm own
        simp [clears, cleared, own, other]

theorem allowedClear_target {instruction : SeqInstruction} {register : Register}
    (allowed : allowedClear instruction = true) (cleared : clearTarget instruction = some register) :
    register = .rax ∨ register = .rcx := by
  cases register <;> simp_all [allowedClear]

theorem Plan.prologue_not_clears {plan : Plan} (valid : plan.prologueValid = true)
    (register : Register) (notRax : register ≠ .rax) (notRcx : register ≠ .rcx) :
    clears plan.prologue register = false := by
  have allowed := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).1
  cases present : clears plan.prologue register with
  | false => rfl
  | true =>
    obtain ⟨node, member, cleared⟩ := List.any_eq_true.mp present
    have target := allowedClear_target (List.all_eq_true.mp allowed node member) (of_decide_eq_true cleared)
    exact False.elim (target.elim notRax notRcx)

end EDSL.Sum32
