/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Stride32.Accounting
import EDSL.Stride32.Resources

namespace EDSL.Stride32
open X86

/-- Constructive total correctness of the exact GCC stride-two bytes. The
result is an independent even-index modular sum, with full memory/ABI framing.
The conservative bound comes from the reusable cutpoint theorem. -/
theorem executes {initial : State} {values : List (BitVec 32)} {count : Nat} {target : Word}
    (pre : Pre bytes initial values count target) (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices initial result ∧ Post initial values count target result.state ∧
      result.instructions ≤ 9 * (count + 2) := by
  let proof := annotations pre (fun _ => True) (by intros; trivial)
  exact proof.execution valid (.entry pre) choices

theorem all_executions {initial : State} {values : List (BitVec 32)} {count : Nat} {target : Word}
    (pre : Pre bytes initial values count target) :
    Sequential.AllExecutions initial (fun result => Post initial values count target result.state ∧
      result.instructions ≤ 9 * (count + 2)) := executes pre

theorem safe {initial : State} {values : List (BitVec 32)} {count : Nat} {target : Word}
    (pre : Pre bytes initial values count target) : Sequential.Safe initial :=
  (all_executions pre).safe

theorem no_divergence {initial : State} {values : List (BitVec 32)} {count : Nat} {target : Word}
    (pre : Pre bytes initial values count target) : ¬ Sequential.Diverges initial :=
  (all_executions pre).no_divergence

theorem sound {initial : State} {values : List (BitVec 32)} {count : Nat} {target : Word}
    (pre : Pre bytes initial values count target) (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices (9 * (count + 2)) initial = .ok result ∧
      Post initial values count target result.state ∧ result.instructions ≤ 9 * (count + 2) := by
  obtain ⟨result, execution, post, bound⟩ := executes pre choices
  exact ⟨result, Sequential.run_complete execution bound, post, bound⟩

/-- Optional local accounting strengthens total correctness to the exact
instruction count and the independent ordered even-index read footprint. -/
theorem exact_sound {initial : State} {values : List (BitVec 32)} {count : Nat} {target : Word}
    (pre : Pre bytes initial values count target) (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices (6 * count + 4) initial = .ok result ∧
      Post initial values count target result.state ∧ result.instructions = 6 * count + 4 ∧
      result.reads = operandReads initial count := by
  let account := accounting pre (fun _ => True) (by intros; trivial)
  have cost : account.cost ⟨0, by decide⟩ initial = 6 * count + 4 := rfl
  have reads : account.reads ⟨0, by decide⟩ initial = operandReads initial count :=
    accounting_initial_reads pre _ _
  have result := account.sound (entry := ⟨0, by decide⟩) (by decide) (.entry pre) choices
  simpa only [cost, reads] using result

theorem exact_executes {initial : State} {values : List (BitVec 32)} {count : Nat} {target : Word}
    (pre : Pre bytes initial values count target) (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      Post initial values count target result.state ∧ result.instructions = 6 * count + 4 ∧
      result.reads = operandReads initial count := by
  obtain ⟨result, success, post, cost, reads⟩ := exact_sound pre choices
  exact ⟨result, Sequential.run_sound success, post, cost, reads⟩

/-- Current OS admission supplies all initial RAM/resource premises. Every
actual operand read retains current loan authority; input count remains
symbolic, with no input-loan requirement in the empty case. -/
theorem resource_sound {shared : OS.Borrowing.State} {call : OS.ArrayResources.Call}
    {initial : State} {count : Nat} (code : call.bytes = bytes)
    (admitted : OS.ArrayResources.Admission shared call initial)
    (entry : initial.rip = call.code) (stack : initial.registers .rsp = call.stack)
    (base : initial.registers .rdi = call.base) (length : call.values.length = 2 * count)
    (counter : initial.registers .rsi = BitVec.ofNat 64 count)
    (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices (6 * count + 4) initial = .ok result ∧
      Post initial call.values count call.target result.state ∧
      result.instructions = 6 * count + 4 ∧ result.reads = operandReads initial count ∧
      OS.ArrayResources.Admission shared call result.state ∧
      ∀ read ∈ result.reads, OS.ArrayResources.ReadPermission shared call.worker read := by
  have pre := pre_of_admission admitted entry stack base length counter
  rw [code] at pre
  obtain ⟨result, success, post, cost, reads⟩ := exact_sound pre choices
  refine ⟨result, success, post, cost, reads, admitted.unchangedMemory post.memory, ?_⟩
  intro read member
  exact operandReads_permission admitted length base stack (reads ▸ member)

/-- Every actual operand read has a successful current-RAM origin and a current
OS loan permission. The current admission also retains executable code, array
contents, return slot and full RAM coupling, not just a saved read snapshot. -/
theorem resource_read_origin {shared : OS.Borrowing.State} {call : OS.ArrayResources.Call}
    {initial : State} {count : Nat} (code : call.bytes = bytes)
    (admitted : OS.ArrayResources.Admission shared call initial)
    (entry : initial.rip = call.code) (stack : initial.registers .rsp = call.stack)
    (base : initial.registers .rdi = call.base) (length : call.values.length = 2 * count)
    (counter : initial.registers .rsi = BitVec.ofNat 64 count)
    {choices : Sequential.Choices} {result : Sequential.Result}
    (execution : Sequential.Executes choices initial result)
    {read : Sequential.Read} (member : read ∈ result.reads) :
    ∃ index before priorReads observation node, index < result.instructions ∧
      Sequential.Block choices initial before index priorReads ∧
      Sequential.step (choices index) before = .ok observation ∧ read ∈ observation.reads ∧
      Sequential.CFG.At bytes graph initial.rip node before ∧
      OS.ArrayResources.Admission shared call before ∧
      OS.ArrayResources.ReadPermission shared call.worker read ∧
      Sequential.OperandReadSucceeds before read := by
  have pre := pre_of_admission admitted entry stack base length counter
  rw [code] at pre
  let proof := annotations pre (OS.ArrayResources.ReadPermission shared call.worker)
    (fun read member => operandReads_permission admitted length base stack member)
  obtain ⟨index, before, priorReads, observation, node, bound, block, actual, present,
    binding, allowed, succeeded⟩ := proof.read_origin valid (.entry pre) execution member
  exact ⟨index, before, priorReads, observation, node, bound, block, actual, present,
    binding, admitted.unchangedMemory allowed.2, allowed.1, succeeded⟩

end EDSL.Stride32
