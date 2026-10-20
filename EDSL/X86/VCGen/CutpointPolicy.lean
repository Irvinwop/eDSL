/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Cutpoints
import EDSL.Grading.Policy

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen.Cutpoints
open Sequential

variable {profile : CFG.Profile}

variable {bytes : List Byte} {graph : CFG.Graph} {base : Word}
  {Post : State → Prop} {AllowedRead : State → Read → Prop}

/-- Every actual continuing prefix preserves complete RAM, including access,
execute and write permissions. The proof uses the checked read-only CFG and
retained cutpoint ghost, not a memory assertion supplied at every instruction. -/
theorem Annotations.block_memory
    (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : CFG.Valid bytes graph profile) {entry : graph.Index} {initial before : State}
    (isCut : graph.cutpoint entry = true) (binding : CFG.At bytes graph base entry initial)
    (admitted : annotations.Inv entry initial) {choices : Choices} {count : Nat}
    {reads : List Read} (block : Sequential.Block choices initial before count reads) :
    before.memory = initial.memory := by
  let certificate := annotations.certificate valid
  have start := certificate.ghost_start isCut ⟨binding, admitted⟩
  have frame : ∀ {choices : Choices} {first last : State} {count : Nat} {reads : List Read},
      Sequential.Cutpoints.Ghost certificate first →
      Sequential.Block choices first last count reads → last.memory = first.memory := by
    intro choices first last count reads ghost trace
    induction trace with
    | nil => rfl
    | next actual tail induction =>
      obtain ⟨source, budget, node, inside⟩ := ghost
      obtain ⟨code, pc⟩ := (annotations.machineAnnotations valid).binding source budget node _ inside
      obtain ⟨_, _, _, memory, _⟩ := valid.next code node pc actual rfl
      exact (induction (certificate.continues_ghost
        ⟨source, budget, node, inside⟩ actual rfl)).trans memory
    | atomic actual tail induction =>
      obtain ⟨source, budget, node, inside⟩ := ghost
      obtain ⟨code, pc⟩ := (annotations.machineAnnotations valid).binding source budget node _ inside
      exact False.elim (valid.no_atomic code node pc actual _ _ rfl)
  exact frame start block

/-- Generated sparse block VCs establish the fixed every-prefix read-only
policy. Both AF choices execute in current code; every reported operand read is
permitted and succeeds in current RAM. Interior assertions are generated once
by the production cutpoint adapter. -/
theorem Annotations.readOnly_policy_memory
    (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : CFG.Valid bytes graph profile) {entry : graph.Index} {initial : State}
    (isCut : graph.cutpoint entry = true) (binding : CFG.At bytes graph base entry initial)
    (admitted : annotations.Inv entry initial) :
    Grading.ReadOnlyPolicy initial (fun before => before.memory = initial.memory) AllowedRead := by
  intro before reachable
  let certificate := annotations.certificate valid
  have start := certificate.ghost_start isCut ⟨binding, admitted⟩
  obtain ⟨source, budget, node, inside⟩ := certificate.reachable_ghost start reachable
  obtain ⟨code, pc⟩ := (annotations.machineAnnotations valid).binding source budget node _ inside
  have decoded := valid.decoded code node before rfl pc
  have readOnly := (valid.nodes node).2.2.1
  obtain ⟨choices, count, reads, block⟩ := reachable
  refine ⟨annotations.block_memory valid isCut binding admitted block,
    ⟨(graph.node node).instruction, decoded, readOnly⟩, ?_⟩
  intro af
  obtain ⟨observation, actual, allowed, _⟩ := certificate.localVC source budget node before inside af
  have effect : execute before (graph.node node).instruction af = .ok observation := by
    rw [← Sequential.step_eq_execute af decoded]
    exact actual
  refine ⟨observation, actual, ?_, ?_⟩
  · intro read member
    exact ⟨allowed read member, observed_reads_succeed actual read member⟩
  · obtain ⟨after, next | ⟨returned, _⟩⟩ := CFG.execute_result readOnly effect
    · rw [next]
      exact CFG.execute_next_memory readOnly effect next
    · rw [returned]
      exact CFG.execute_returned_memory readOnly effect returned

/-- The production totality and prefix-policy evidence share the same checked
CFG, sparse invariants and input-dependent rank. The static block depth never
bounds the mathematical input size. -/
theorem Annotations.total_policy
    (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : CFG.Valid bytes graph profile) {entry : graph.Index} {initial : State}
    (isCut : graph.cutpoint entry = true) (binding : CFG.At bytes graph base entry initial)
    (admitted : annotations.Inv entry initial) :
    Sequential.AllExecutions initial (fun result => Post result.state ∧
      result.instructions ≤ (graph.maxDepth + 1) * (annotations.rank entry initial + 1)) ∧
    Grading.ReadOnlyPolicy initial (fun before => before.memory = initial.memory) AllowedRead :=
  ⟨annotations.all_executions valid isCut binding admitted,
    annotations.readOnly_policy_memory valid isCut binding admitted⟩

end EDSL.X86.VCGen.Cutpoints

