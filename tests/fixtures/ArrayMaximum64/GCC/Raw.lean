/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.ArrayMaximum64.GCC.Steps

set_option warningAsError true

namespace EDSL.ArrayMaximum64.GCC
open X86 X86.Sequential

def cost (values : List Word) : Nat := 7 * values.length + 5

theorem inputReads_cons (base value : Word) (rest : List Word) :
    inputReads base (value :: rest) = ⟨.data,base,8⟩ :: inputReads (base + 8) rest := by
  simp only [inputReads,List.length_cons,List.range_succ_eq_map,List.map_cons,Nat.mul_zero,List.map_map]
  congr 1
  · congr 1
    exact BitVec.add_zero base
  · apply List.map_congr_left
    intro index _
    simp only [Function.comp_apply,Nat.mul_succ,BitVec.ofNat_add]
    congr 1
    change base + (BitVec.ofNat 64 (8 * index) + 8) = (base + 8) + BitVec.ofNat 64 (8 * index)
    rw [BitVec.add_assoc,BitVec.add_comm (BitVec.ofNat 64 (8 * index)) 8]

def suffixReads (initial : State) (consumed : Nat) (remaining : List Word) : List Read :=
  inputReads (initial.registers .rdi + BitVec.ofNat 64 (8 * consumed)) remaining ++
    [⟨.stack,initial.registers .rsp,8⟩]

theorem suffixReads_cons (initial : State) (consumed : Nat) (value : Word) (rest : List Word) :
    suffixReads initial consumed (value :: rest) =
      [⟨.data,initial.registers .rdi + BitVec.ofNat 64 (8 * consumed),8⟩] ++
        suffixReads initial (consumed + 1) rest := by
  simp only [suffixReads,inputReads_cons,List.cons_append,List.nil_append,Nat.mul_succ,
    BitVec.ofNat_add,BitVec.add_assoc]
  rfl

/-- Induction over the actual remaining elements composes the real seven-step
cycle. Every retired instruction consumes its own AF stream position. -/
theorem suffix_execution {initial values target} (pre : Pre bytes initial values target)
    (remaining : List Word) {consumed state} (header : Header initial values remaining consumed state)
    (choices : Choices) : ∃ result, Sequential.Executes choices state result ∧
      Post initial values target result.state ∧ result.instructions = 7 * remaining.length + 3 ∧
        result.reads = suffixReads initial consumed remaining := by
  induction remaining generalizing consumed state choices with
  | nil =>
    have actual := Sequential.Executes.next (test_step header pre (choices 0))
      (Sequential.Executes.next (exit_step header pre ((choices.drop 1) 0))
        (Sequential.Executes.ret (ret_step header pre (((choices.drop 1).drop 1) 0))))
    refine ⟨_,actual,empty_post header,?_,?_⟩
    · rfl
    · rfl
  | cons value rest induction =>
    obtain ⟨result,actual,post,count,reads⟩ :=
      induction (next_header header) (choices.drop 7)
    have block := iteration_block header pre choices
    refine ⟨result.prepend 7 [⟨.data,initial.registers .rdi + BitVec.ofNat 64 (8 * consumed),8⟩],
      block.then_executes actual,post,?_,?_⟩
    · simp only [Result.prepend,count,List.length_cons]
      omega
    · simp only [Result.prepend,reads,suffixReads_cons]

/-- All complete actual executions exist for every AF stream and satisfy the
independent contract. The exact accounting below is separate proof evidence. -/
theorem executions {initial values target} (pre : Pre bytes initial values target) (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧ Post initial values target result.state ∧
      result.instructions = cost values ∧ result.reads = operandReads initial values := by
  have header := initialized_header pre (choices 0) ((choices.drop 1) 0)
  obtain ⟨result,actual,post,count,reads⟩ := suffix_execution pre values header (choices.drop 2)
  refine ⟨result.prepend 2 [],(prefix_block pre choices).then_executes actual,post,?_,?_⟩
  · simp only [Result.prepend,count,cost]
    omega
  · simpa only [Result.prepend,List.nil_append,suffixReads,Nat.mul_zero,
      BitVec.add_zero,operandReads] using reads

/-- The registered mathematical contract carries no cost or trace-order gate. -/
theorem raw_semantics {initial values target} (pre : Pre bytes initial values target) :
    AllExecutions initial (fun result => Post initial values target result.state) := by
  intro choices
  obtain ⟨result,actual,post,_,_⟩ := executions pre choices
  exact ⟨result,actual,post⟩

/-- Exact independent accounting for any actual returning execution. Reads are
original DATA8 elements in index order followed by the original STACK8 slot. -/
theorem execution_exact {initial values target choices result}
    (pre : Pre bytes initial values target) (actual : Sequential.Executes choices initial result) :
    result.instructions = 7 * values.length + 5 ∧ result.reads = operandReads initial values := by
  obtain ⟨expected,execution,_,count,reads⟩ := executions pre choices
  have same := Sequential.Executes.fixed_choices_unique execution actual
  cases same
  exact ⟨count,reads⟩

theorem raw_accounting {initial values target} (pre : Pre bytes initial values target) :
    AllExecutions initial (fun result => result.instructions = 7 * values.length + 5 ∧
      result.reads = operandReads initial values) := by
  intro choices
  obtain ⟨result,actual,_,count,reads⟩ := executions pre choices
  exact ⟨result,actual,count,reads⟩

end EDSL.ArrayMaximum64.GCC
