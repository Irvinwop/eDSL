/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Pair32.Accounting

namespace EDSL.Pair32
open X86

/-- The generic cutpoint theorem constructs actual execution through both
loops for every flag-choice stream and every admitted pair of input lists. -/
theorem executes {initial : State} {valuesA valuesB : List (BitVec 32)} {target : Word}
    (pre : Pre bytes initial valuesA valuesB target) (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      Post initial valuesA valuesB target result.state ∧
      result.instructions ≤ 15 * (valuesA.length + valuesB.length + 3) := by
  let proof := annotations pre (fun _ => True) (by intros; trivial)
  exact proof.execution valid (.entry pre) choices

theorem all_executions {initial : State} {valuesA valuesB : List (BitVec 32)} {target : Word}
    (pre : Pre bytes initial valuesA valuesB target) :
    Sequential.AllExecutions initial (fun result => Post initial valuesA valuesB target result.state ∧
      result.instructions ≤ 15 * (valuesA.length + valuesB.length + 3)) := executes pre

theorem safe {initial : State} {valuesA valuesB : List (BitVec 32)} {target : Word}
    (pre : Pre bytes initial valuesA valuesB target) : Sequential.Safe initial :=
  (all_executions pre).safe

theorem no_divergence {initial : State} {valuesA valuesB : List (BitVec 32)} {target : Word}
    (pre : Pre bytes initial valuesA valuesB target) : ¬ Sequential.Diverges initial :=
  (all_executions pre).no_divergence

theorem sound {initial : State} {valuesA valuesB : List (BitVec 32)} {target : Word}
    (pre : Pre bytes initial valuesA valuesB target) (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices (15 * (valuesA.length + valuesB.length + 3)) initial = .ok result ∧
      Post initial valuesA valuesB target result.state ∧
      result.instructions ≤ 15 * (valuesA.length + valuesB.length + 3) := by
  obtain ⟨result, execution, post, bound⟩ := executes pre choices
  exact ⟨result, Sequential.run_complete execution bound, post, bound⟩

/-- Exact local accounting composes with the separately constructed totality
proof. The operand list includes repeated reads when immutable inputs alias. -/
theorem exact_sound {initial : State} {valuesA valuesB : List (BitVec 32)} {target : Word}
    (pre : Pre bytes initial valuesA valuesB target) (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices (6 * (valuesA.length + valuesB.length) + 6) initial = .ok result ∧
      Post initial valuesA valuesB target result.state ∧
      result.instructions = 6 * (valuesA.length + valuesB.length) + 6 ∧
      result.reads = operandReads initial valuesA valuesB := by
  let account := accounting pre (fun _ => True) (by intros; trivial)
  have cost : account.cost ⟨0, by decide⟩ initial = 6 * (valuesA.length + valuesB.length) + 6 := rfl
  have reads : account.reads ⟨0, by decide⟩ initial = operandReads initial valuesA valuesB :=
    accounting_initial_reads pre _ _
  have result := account.sound (entry := ⟨0, by decide⟩) (by decide) (.entry pre) choices
  simpa only [cost, reads] using result

theorem exact_executes {initial : State} {valuesA valuesB : List (BitVec 32)} {target : Word}
    (pre : Pre bytes initial valuesA valuesB target) (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices initial result ∧ Post initial valuesA valuesB target result.state ∧
      result.instructions = 6 * (valuesA.length + valuesB.length) + 6 ∧
      result.reads = operandReads initial valuesA valuesB := by
  obtain ⟨result, success, post, cost, reads⟩ := exact_sound pre choices
  exact ⟨result, Sequential.run_sound success, post, cost, reads⟩

/-- Both current resource admissions supply the initial contract and remain
valid at return. Each actual data/stack operand has current loan permission. -/
theorem resource_sound {shared : OS.Borrowing.State} {callA callB : OS.ArrayResources.Call}
    {initial : State} (code : callA.bytes = bytes) (admitted : PairAdmission shared callA callB initial)
    (entry : initial.rip = callA.code) (stack : initial.registers .rsp = callA.stack)
    (baseA : initial.registers .rdi = callA.base)
    (counterA : initial.registers .rsi = BitVec.ofNat 64 callA.values.length)
    (baseB : initial.registers .rdx = callB.base)
    (counterB : initial.registers .rcx = BitVec.ofNat 64 callB.values.length)
    (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices (6 * (callA.values.length + callB.values.length) + 6) initial = .ok result ∧
      Post initial callA.values callB.values callA.target result.state ∧
      result.instructions = 6 * (callA.values.length + callB.values.length) + 6 ∧
      result.reads = operandReads initial callA.values callB.values ∧
      PairAdmission shared callA callB result.state ∧
      ∀ read ∈ result.reads, OS.ArrayResources.ReadPermission shared callA.worker read := by
  have pre := pre_of_admission admitted entry stack baseA counterA baseB counterB
  rw [code] at pre
  obtain ⟨result, success, post, cost, reads⟩ := exact_sound pre choices
  refine ⟨result, success, post, cost, reads, admitted.unchangedMemory post.memory, ?_⟩
  intro read member
  exact operandReads_permission admitted baseA baseB stack (reads ▸ member)

/-- Every actual operand read retains both current admissions and is authorized
for the common worker in its real pre-instruction state. Compatible readonly
aliases require no disjointness between the two input resources. -/
theorem resource_read_origin {shared : OS.Borrowing.State}
    {callA callB : OS.ArrayResources.Call} {initial : State}
    (code : callA.bytes = bytes) (admitted : PairAdmission shared callA callB initial)
    (entry : initial.rip = callA.code) (stack : initial.registers .rsp = callA.stack)
    (baseA : initial.registers .rdi = callA.base)
    (counterA : initial.registers .rsi = BitVec.ofNat 64 callA.values.length)
    (baseB : initial.registers .rdx = callB.base)
    (counterB : initial.registers .rcx = BitVec.ofNat 64 callB.values.length)
    {choices : Sequential.Choices} {result : Sequential.Result}
    (execution : Sequential.Executes choices initial result)
    {read : Sequential.Read} (member : read ∈ result.reads) :
    ∃ index before priorReads observation node, index < result.instructions ∧
      Sequential.Block choices initial before index priorReads ∧
      Sequential.step (choices index) before = .ok observation ∧ read ∈ observation.reads ∧
      Sequential.CFG.At bytes graph initial.rip node before ∧
      PairAdmission shared callA callB before ∧
      OS.ArrayResources.ReadPermission shared callA.worker read ∧
      Sequential.OperandReadSucceeds before read := by
  have pre := pre_of_admission admitted entry stack baseA counterA baseB counterB
  rw [code] at pre
  let proof := annotations pre (OS.ArrayResources.ReadPermission shared callA.worker)
    (fun read member => operandReads_permission admitted baseA baseB stack member)
  obtain ⟨index, before, priorReads, observation, node, bound, block, actual, present,
    binding, allowed, succeeded⟩ := proof.read_origin valid (.entry pre) execution member
  exact ⟨index, before, priorReads, observation, node, bound, block, actual, present,
    binding, admitted.unchangedMemory allowed.2, allowed.1, succeeded⟩

end EDSL.Pair32
