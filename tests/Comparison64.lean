/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.Comparison64
import EDSL.Comparison64.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.Comparison64
open EDSL X86 X86.Sequential Comparison64 Comparison64.Client

private def observe (variant : Variant) (operation : Operation) (left right : Word)
    (fuel : Nat) (af : Bool) : Except Error (Nat × Word × Word × Word × Word × List Read) := do
  let result ← Sequential.run (fun _ => af) fuel
    (Domain.initial (bytes variant operation) left right)
  return (result.instructions,result.state.registers .rax,result.state.rip,
    result.state.registers .rsp,result.state.flags &&& ~~~arithmeticFlagMask,result.reads)

private def allCases : List (Variant × Operation) :=
  [(.gcc,.unsignedMaximum),(.gcc,.unsignedMinimum),(.gcc,.signedMaximum),
    (.clang,.unsignedMaximum),(.clang,.unsignedMinimum),(.clang,.signedMaximum)]

/-- Literal full64 order vectors distinguish signed from unsigned selection
and exercise subtraction overflow. RET and its exact footprint are observed
through the real evaluator, not reconstructed from the expected theorem. -/
theorem signed_unsigned_boundary (af : Bool) :
    allCases.map (fun (variant,operation) => observe variant operation 0x8000000000000000 1 4 af) =
    [.ok (4,0x8000000000000000,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,1,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,1,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,0x8000000000000000,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,1,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,1,8192,65552,0x602,[⟨.stack,65544,8⟩])] := by
  cases af <;> rfl

/-- A nonzero high half must participate in ordering; narrowing either the
comparison or selected value changes these independently requested results. -/
theorem high_half_order (af : Bool) :
    allCases.map (fun (variant,operation) => observe variant operation 0x100000001 0xffffffff 4 af) =
    [.ok (4,0x100000001,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,0xffffffff,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,0x100000001,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,0x100000001,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,0xffffffff,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,0x100000001,8192,65552,0x602,[⟨.stack,65544,8⟩])] := by
  cases af <;> rfl

theorem maximum_and_negative_one (af : Bool) :
    allCases.map (fun (variant,operation) => observe variant operation 0x7fffffffffffffff 0xffffffffffffffff 4 af) =
    [.ok (4,0xffffffffffffffff,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,0x7fffffffffffffff,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,0x7fffffffffffffff,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,0xffffffffffffffff,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,0x7fffffffffffffff,8192,65552,0x602,[⟨.stack,65544,8⟩]),
      .ok (4,0x7fffffffffffffff,8192,65552,0x602,[⟨.stack,65544,8⟩])] := by
  cases af <;> rfl

theorem equal_operands (af : Bool) :
    allCases.map (fun (variant,operation) =>
      observe variant operation 0xdeadbeef12345678 0xdeadbeef12345678 4 af) =
    List.replicate 6 (.ok (4,0xdeadbeef12345678,8192,65552,0x602,[⟨.stack,65544,8⟩])) := by
  cases af <;> rfl

/-- Computing a selected value without executing RET is insufficient. -/
theorem fuel_short (af : Bool) :
    allCases.map (fun (variant,operation) => observe variant operation 0 1 3 af) =
      List.replicate 6 (.error .exhaustedFuel) := by
  cases af <;> rfl

/-- The universal client claim returns the same present world with reusable
original code/slot loans. The admission fixes neither flags nor scratch GPRs. -/
theorem returned_resources {variant operation resource initial}
    (pre : ResourcePre (bytes variant operation) resource initial) (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      Post operation (resourceInput resource) initial result.state ∧
      OS.CallResources.Current resource.call resource.shared result.state ∧
      OS.Threads.HasLoan resource.shared resource.call.worker resource.call.codeLoan
        ⟨resource.call.code,resource.call.bytes.length⟩ ∧
      OS.Threads.HasLoan resource.shared resource.call.worker resource.call.stackLoan
        ⟨resource.call.stack,8⟩ ∧
      OS.CallResources.ReadAllowed resource.call resource.shared ⟨.stack,resource.call.stack,8⟩ := by
  have claim := semantic_claim variant operation
  rw [registered_task] at claim
  have checked := (Grading.old_semanticClaim_iff _ _).mp claim
  have semantics := checked.resource resource initial pre
  obtain ⟨result,actual,post,current⟩ := semantics.1 choices
  exact ⟨result,actual,post,current,current.contract.codeLoan,current.contract.stackLoan,
    OS.CallResources.stackRead_permission current.contract⟩

/-- A supported, terminating minimum implementation cannot satisfy maximum.
The counterexample uses its actual all-input execution and an independent
mathematical maximum contract; unsupported code and proof failure play no role. -/
theorem minimum_not_maximum (variant : Variant) :
    ¬Grading.Claim .maximum64 (bytes variant .unsignedMinimum) := by
  intro claimed
  let resource := Domain.resource (bytes variant .unsignedMinimum) 0 1
  let initial := Domain.initial (bytes variant .unsignedMinimum) 0 1
  have pre : ResourcePre (bytes variant .unsignedMinimum) resource initial :=
    Domain.resource_pre _ (by cases variant <;> decide) (by cases variant <;> decide) 0 1
  obtain ⟨result,actual,post⟩ := (claimed.1.machine (resourceInput resource) initial pre.machine).1
    (fun _ => false)
  have exactResult := execution_exact pre.machine actual
  cases exactResult
  have impossible : ¬MathematicalResult .unsignedMaximum 0 1
      ((finalState variant .unsignedMinimum initial 8192).registers .rax) := by
    cases variant <;> unfold MathematicalResult <;> decide
  exact impossible post.result

/-- Signed and unsigned maxima disagree at INT64_MIN versus one, even though
both complete normally and preserve the identical OS resource frame. -/
theorem unsigned_not_signed (variant : Variant) :
    ¬Grading.Claim .signedMaximum64 (bytes variant .unsignedMaximum) := by
  intro claimed
  let resource := Domain.resource (bytes variant .unsignedMaximum) 0x8000000000000000 1
  let initial := Domain.initial (bytes variant .unsignedMaximum) 0x8000000000000000 1
  have pre : ResourcePre (bytes variant .unsignedMaximum) resource initial :=
    Domain.resource_pre _ (by cases variant <;> decide) (by cases variant <;> decide)
      0x8000000000000000 1
  obtain ⟨result,actual,post⟩ := (claimed.1.machine (resourceInput resource) initial pre.machine).1
    (fun _ => false)
  have exactResult := execution_exact pre.machine actual
  cases exactResult
  have impossible : ¬MathematicalResult .signedMaximum 0x8000000000000000 1
      ((finalState variant .unsignedMaximum initial 8192).registers .rax) := by
    cases variant <;> unfold MathematicalResult <;> decide
  exact impossible post.result

end EDSL.Tests.Comparison64

#audit_edsl
