/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.IndexSteps

namespace EDSL.Sum32
open X86

/-- Every structurally checked indexed loop returns for every full choice
stream, from its current header and current readable suffix. The contract
contains no assumed future execution or successful fuel bound. -/
theorem index_loop {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {remaining : List (BitVec 32)} {accumulator : BitVec 32} {target : Word}
    {consumed total : Nat} (valid : Valid bytes plan) (mode : plan.mode = .index)
    (header : IndexHeader bytes plan base state remaining accumulator target consumed total)
    (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices state result ∧
      LoopPost state accumulator remaining target result.state ∧
      result.instructions = 5 * remaining.length + 3 ∧
      result.reads = indexReads state consumed remaining := by
  induction remaining generalizing state accumulator consumed choices with
  | nil =>
    exact ⟨⟨IndexProof.returned plan base state target, 3,
      [⟨.stack, state.registers .rsp, 8⟩]⟩,
      IndexProof.exit_execution valid mode header choices,
      IndexProof.exit_post header, rfl, rfl⟩
  | cons value remaining induction =>
    obtain ⟨result, execution, post, cost, reads⟩ :=
      induction (IndexProof.resumed_header header) (choices.drop 5)
    let accesses : List Sequential.Read :=
      [⟨.data, state.registers .rdi + BitVec.ofNat 64 (4 * consumed), 4⟩]
    refine ⟨result.prepend 5 accesses,
      (IndexProof.body_block valid mode header choices).then_executes execution,
      IndexProof.finish_after (IndexProof.resumed_frame plan base state value) post, ?_, ?_⟩
    · change 5 + result.instructions = 5 * (value :: remaining).length + 3
      rw [cost, List.length_cons]
      omega
    · change accesses ++ result.reads = indexReads state consumed (value :: remaining)
      rw [reads]
      exact (IndexProof.reads_cons plan base state value remaining consumed).symm

/-- This universal execution contract exposes the generic nondeterministic
projection, fault exclusion and divergence exclusion theorems. Its proof
constructs a terminating actual execution separately for every choice stream. -/
theorem index_all_executions {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {remaining : List (BitVec 32)} {accumulator : BitVec 32} {target : Word}
    {consumed total : Nat} (valid : Valid bytes plan) (mode : plan.mode = .index)
    (header : IndexHeader bytes plan base state remaining accumulator target consumed total) :
    Sequential.AllExecutions state (fun result =>
      LoopPost state accumulator remaining target result.state ∧
      result.instructions = 5 * remaining.length + 3 ∧
      result.reads = indexReads state consumed remaining) :=
  index_loop valid mode header

/-- Exact sufficient fuel is a consequence of the relational loop proof. -/
theorem index_run {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {remaining : List (BitVec 32)} {accumulator : BitVec 32} {target : Word}
    {consumed total : Nat} (valid : Valid bytes plan) (mode : plan.mode = .index)
    (header : IndexHeader bytes plan base state remaining accumulator target consumed total)
    (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices (5 * remaining.length + 3) state = .ok result ∧
      LoopPost state accumulator remaining target result.state ∧
      result.instructions = 5 * remaining.length + 3 ∧
      result.reads = indexReads state consumed remaining :=
  (index_all_executions valid mode header).run (fun _ contract => contract.2.1) choices

end EDSL.Sum32
