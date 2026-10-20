/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.ArraySum64.Clang.Steps

set_option warningAsError true

namespace EDSL.ArraySum64.Clang
open X86 X86.Sequential

theorem inputReads_cons (base value : Word) (rest : List Word) :
    inputReads base (value :: rest) = ⟨.data,base,8⟩ :: inputReads (base + 8) rest := by
  simp only [inputReads,List.length_cons,List.range_succ_eq_map,List.map_cons,
    Nat.mul_zero,List.map_map]
  congr 1
  · congr 1
    exact BitVec.add_zero base
  · apply List.map_congr_left
    intro index member
    simp only [Function.comp_apply,Nat.mul_succ,BitVec.ofNat_add]
    congr 1
    change base + (BitVec.ofNat 64 (8 * index) + 8) = (base + 8) + BitVec.ofNat 64 (8 * index)
    rw [BitVec.add_assoc,BitVec.add_comm (BitVec.ofNat 64 (8 * index)) 8]

theorem next_address (base : Word) (consumed : Nat) :
    base + BitVec.ofNat 64 (8 * (consumed + 1)) =
      (base + BitVec.ofNat 64 (8 * consumed)) + 8 := by
  simp [Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

/-- A complete iteration retires the fused ADD, INC, CMP and JNE, reading the original indexed DATA8 once. -/
theorem body_block {initial state : State} {values rest : List Word} {consumed : Nat}
    {value target : Word} (pre : Pre bytes initial values target)
    (header : Header initial values (value :: rest) consumed state) (choices : Choices) :
    Sequential.Block choices state (cycleState initial.rip state value rest) 4
      [⟨.data,initial.registers .rdi + BitVec.ofNat 64 (8 * consumed),8⟩] := by
  have block := Sequential.Block.next (step_add pre header (choices 0))
    (Sequential.Block.next (step_increment pre header ((choices.drop 1) 0))
      (Sequential.Block.next (step_compareIndex pre header (((choices.drop 1).drop 1) 0))
        (Sequential.Block.next (step_cycle pre header ((((choices.drop 1).drop 1).drop 1) 0))
          Sequential.Block.nil)))
  simpa only [List.nil_append,List.append_nil] using block

/-- Induction on the mathematical suffix proves all-choice termination. Its
empty case executes RET itself; there is no assumed future execution in Header. -/
theorem loop_execution {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (remaining : List Word) (consumed : Nat)
    (state : State) (header : Header initial values remaining consumed state) (choices : Choices) :
    ∃ result, Sequential.Executes choices state result ∧ Post initial values target result.state ∧
      result.instructions = 4 * remaining.length + 1 ∧
      result.reads = inputReads (initial.registers .rdi + BitVec.ofNat 64 (8 * consumed)) remaining ++
        [⟨.stack,initial.registers .rsp,8⟩] := by
  induction remaining generalizing consumed state choices with
  | nil =>
    exact ⟨_,Sequential.Executes.ret (step_return pre header (choices 0)),return_post header,rfl,rfl⟩
  | cons value rest induction =>
    obtain ⟨result,execution,post,cost,reads⟩ :=
      induction (consumed + 1) (cycleState initial.rip state value rest) (nextHeader header) (choices.drop 4)
    have block := body_block pre header choices
    refine ⟨result.prepend 4 [⟨.data,initial.registers .rdi + BitVec.ofNat 64 (8 * consumed),8⟩],
      block.then_executes execution,post,?_,?_⟩
    · change 4 + result.instructions = 4 * (rest.length + 1) + 1
      omega
    · change [⟨.data,initial.registers .rdi + BitVec.ofNat 64 (8 * consumed),8⟩] ++ result.reads = _
      rw [reads,inputReads_cons,next_address]
      rfl

/-- Nonempty entry initialization consists of TEST, untaken JE and both XORs.
The AF stream is advanced once for each actual retired instruction. -/
theorem initialization_block {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (nonempty : values ≠ []) (choices : Choices) :
    Sequential.Block choices initial
      (initializedState initial (choices 0) (((choices.drop 1).drop 1) 0)
        ((((choices.drop 1).drop 1).drop 1) 0)) 4 [] := by
  have block := Sequential.Block.next (step_test pre (choices 0))
    (Sequential.Block.next (step_positive pre nonempty (choices 0) ((choices.drop 1) 0))
      (Sequential.Block.next (step_clearIndex pre (choices 0) (((choices.drop 1).drop 1) 0))
        (Sequential.Block.next
          (step_clearResult pre (choices 0) (((choices.drop 1).drop 1) 0)
            ((((choices.drop 1).drop 1).drop 1) 0)) Sequential.Block.nil)))
  simpa only [List.nil_append] using block

def instructionCount (values : List Word) : Nat := if values.isEmpty then 4 else 4 * values.length + 5

/-- Exact accounting is a client theorem, separate from the independent
sum postcondition used by the independent mathematical task. -/
theorem raw_exact {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) :
    AllExecutions initial (fun result => Post initial values target result.state ∧
      result.instructions = instructionCount values ∧ result.reads = operandReads initial values) := by
  intro choices
  by_cases empty : values = []
  · have execution := Sequential.Executes.next (step_test pre (choices 0))
      (Sequential.Executes.next (step_empty pre empty (choices 0) ((choices.drop 1) 0))
        (Sequential.Executes.next (step_clearEmpty pre (choices 0) (((choices.drop 1).drop 1) 0))
          (Sequential.Executes.ret
            (step_returnEmpty pre (choices 0) (((choices.drop 1).drop 1) 0)
              ((((choices.drop 1).drop 1).drop 1) 0)))))
    refine ⟨_,execution,empty_post empty _ _,?_,?_⟩
    · simp only [Result.prepend,instructionCount,empty,List.isEmpty_nil,ite_true]
    · simp [Result.prepend,operandReads,inputReads,empty]
  · have header := initialized pre empty (choices 0) (((choices.drop 1).drop 1) 0)
      ((((choices.drop 1).drop 1).drop 1) 0)
    obtain ⟨result,execution,post,cost,reads⟩ := loop_execution pre values 0 _ header (choices.drop 4)
    have block := initialization_block pre empty choices
    refine ⟨result.prepend 4 [],block.then_executes execution,post,?_,?_⟩
    · change 4 + result.instructions = instructionCount values
      have nonempty : values.isEmpty = false := by cases values <;> simp_all
      simp only [instructionCount,nonempty,Bool.false_eq_true,ite_false]
      omega
    · simpa [Result.prepend,operandReads] using reads

/-- The independent full64 modular sum, actual return, complete RAM/permission
frame, ABI register frame and nonarithmetic flags hold for every AF stream. -/
theorem raw_semantics {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) :
    AllExecutions initial (fun result => Post initial values target result.state) := by
  intro choices
  obtain ⟨result,execution,post,_,_⟩ := raw_exact pre choices
  exact ⟨result,execution,post⟩

/-- Any actual execution has the exact retired-instruction count and original
index-ordered DATA8 reads followed by the original caller's STACK8 read. -/
theorem execution_accounting {initial : State} {values : List Word} {target : Word}
    {choices : Choices} {result : Sequential.Result} (pre : Pre bytes initial values target)
    (execution : Sequential.Executes choices initial result) :
    result.instructions = instructionCount values ∧ result.reads = operandReads initial values := by
  obtain ⟨expected,chosen,_,cost,reads⟩ := raw_exact pre choices
  have same := execution.fixed_choices_unique chosen
  cases same
  exact ⟨cost,reads⟩

/-- All AF streams terminate with the separately specified exact instruction
count and ordered original DATA8 reads followed by the caller STACK8 read. -/
theorem raw_accounting {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) :
    AllExecutions initial (fun result => result.instructions = instructionCount values ∧
      result.reads = operandReads initial values) := by
  intro choices
  obtain ⟨result,execution,_,cost,reads⟩ := raw_exact pre choices
  exact ⟨result,execution,cost,reads⟩

end EDSL.ArraySum64.Clang
