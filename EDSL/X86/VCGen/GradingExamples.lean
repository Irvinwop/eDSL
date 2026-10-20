/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Policy
import EDSL.X86.VCGen.Examples
import EDSL.Comparison64.Domain
import EDSL.Grading.Task

set_option warningAsError true

namespace EDSL.X86.VCGen.GradingExamples
open Sequential

/- One shared adapter for the two supported Clang comparison functions. The
independent Comparison64 contract fixes full64 mathematical order, the caller
return, SysV registers, flags and complete RAM. Costs remain in Examples.

These are raw-byte registered claims under the sequential callable profile:
stable ordinary RAM, live code/caller mappings and loans, no asynchronous
interference, the modeled ABI and ordinary RET without CET. They do not by
themselves bind a frozen ELF's symbol/window, establish native loading or CPU
refinement, or change any end-to-end corpus certification count. -/

def routine (minimum : Bool) : Examples.Routine :=
  if minimum then .minClang else .maxClang

def operation (minimum : Bool) : Comparison64.Operation :=
  if minimum then .unsignedMinimum else .unsignedMaximum

def taskID (minimum : Bool) : Grading.TaskID :=
  if minimum then .minimum64 else .maximum64

/-- Forget only the example's extra cost/trace assertions. The retained
mathematical, ABI, flag, return and memory fields are exactly the independently
registered contract; its input bindings come from Comparison64.Pre. -/
theorem post_contract (minimum : Bool) {input : Comparison64.Input} {initial : State}
    (pre : Comparison64.Pre (Examples.bytes (routine minimum)) input initial)
    {result : Result}
    (post : Examples.Post (routine minimum) initial input.returnAddress 0 result) :
    Comparison64.Post (operation minimum) input initial result.state := by
  refine ⟨?_, post.2.1, post.2.2.1, post.2.2.2.1,
    post.2.2.2.2.1, post.2.2.2.2.2.1⟩
  cases minimum <;>
    simpa only [routine, operation, Bool.false_eq_true, ↓reduceIte,
      Examples.Value, Comparison64.MathematicalResult, pre.left, pre.right] using post.1

/-- Universal raw semantics and every-prefix policy, obtained from the shared
generated WP and production execution theorem. No per-instruction proof or
program-specific resource invariant is supplied. Other registers and flags,
both full64 operands, all admitted memories and every AF stream are arbitrary. -/
theorem raw_semantics (minimum : Bool) (input : Comparison64.Input) (initial : State)
    (pre : Comparison64.Pre (Examples.bytes (routine minimum)) input initial) :
    AllExecutions initial (fun result =>
      Comparison64.Post (operation minimum) input initial result.state) ∧
      Comparison64.RawPolicy initial := by
  have ready : Examples.ReturnReady initial input.returnAddress :=
    ⟨pre.stack, pre.returnCanonical, pre.stackBound, pre.postStackCanonical⟩
  have data : Examples.DataReady (routine minimum) initial 0 := by
    cases minimum <;> simp [routine, Examples.DataReady]
  have order : Examples.OrderReady (routine minimum) initial := by
    cases minimum <;> simp [routine, Examples.OrderReady]
  have pc : initial.rip = initial.rip +
      BitVec.ofNat 64 ((Examples.graph (routine minimum)).node
        (Examples.entry (routine minimum))).offset := by simp
  constructor
  · intro choices
    obtain ⟨result, actual, post, _⟩ := Examples.verifies (routine minimum) initial
      input.returnAddress 0 pre.code ready data order choices
    exact ⟨result, Sequential.run_sound actual, post_contract minimum pre post⟩
  · have policy := readOnly_policy_memory (Examples.valid (routine minimum)) pre.code pc
      (Examples.generated_vc (routine minimum) initial input.returnAddress 0 ready data order)
    refine policy.mono (fun _ memory => memory) ?_
    intro before read allowed
    rcases allowed.2 with stack | ⟨load, _⟩
    · rw [stack]
      exact ⟨rfl, rfl, rfl⟩
    · cases minimum <;> simp [routine] at load

/-- The existing resource adapter retains the original complete OS world and
code/caller loans before every actual step and after return. -/
theorem readOnly_semantics (minimum : Bool) :
    Grading.ReadOnlySemanticClaim (Comparison64.readOnlyTask (operation minimum))
      (Examples.bytes (routine minimum)) :=
  Comparison64.readOnly_semantics_of_raw (raw_semantics minimum)

/-- Existing registered min/max claims, with useful unequal raw/current
witnesses constructed independently of code decoding by Comparison64.Domain.
No task, admission predicate, grader or instruction budget is added here. -/
theorem claim (minimum : Bool) :
    Grading.Claim (taskID minimum) (Examples.bytes (routine minimum)) := by
  have witnesses := Comparison64.Domain.nonvacuous (operation minimum)
    (Examples.bytes (routine minimum)) (by cases minimum <;> decide)
    (by cases minimum <;> decide)
  have registered := (Grading.old_claim_iff _ _).mpr
    ⟨readOnly_semantics minimum, witnesses⟩
  cases minimum <;> exact registered

theorem minimum_claim : Grading.Claim .minimum64 (Examples.bytes .minClang) := claim true

theorem maximum_claim : Grading.Claim .maximum64 (Examples.bytes .maxClang) := claim false

end EDSL.X86.VCGen.GradingExamples
