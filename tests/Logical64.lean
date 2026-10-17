/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.Logical64
import EDSL.Logical64.Accounting
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.Logical64
open X86 X86.Sequential
open EDSL.Logical64 EDSL.Logical64.Client


private def observe (operation : Operation) (left right : Word) (fuel : Nat) (af : Bool) :
    Except Error (Word × Nat × Word × Word × Word × Bool × List Read) := do
  let result ← Sequential.run (fun _ => af) fuel
    (EDSL.Logical64.Domain.initial (bytes operation) left right)
  return (result.state.registers .rax,result.instructions,result.state.rip,
    result.state.registers .rsp,result.state.flags &&& ~~~arithmeticFlagMask,
    result.state.flags.getLsbD 4,result.reads)

/-- Independently calculated literal vectors distinguish all three operations
and catch 32-bit narrowing, wrong operands, missed RET, or incorrect AF.
The evaluator executes admitted literal code in real modeled RAM. -/
theorem high_bits (af : Bool) :
    [observe .intersection 0x8000000100000001 0x8000000200000003 3 af,
      observe .union 0x8000000100000001 0x8000000200000003 3 af,
      observe .symmetricDifference 0x8000000100000001 0x8000000200000003 3 af] =
    [.ok (0x8000000000000001,3,8192,65552,0x602,af,[⟨.stack,65544,8⟩]),
      .ok (0x8000000300000003,3,8192,65552,0x602,af,[⟨.stack,65544,8⟩]),
      .ok (0x300000002,3,8192,65552,0x602,af,[⟨.stack,65544,8⟩])] := by
  cases af <;> rfl

/-- A computed RAX without the actual caller return is insufficient. -/
theorem two_retirements_are_short (af : Bool) :
    [observe .intersection 0 1 2 af,observe .union 0 1 2 af,
      observe .symmetricDifference 0 1 2 af] =
    [.error .exhaustedFuel,.error .exhaustedFuel,.error .exhaustedFuel] := by
  cases af <;> rfl

/-- A fully terminating, resource-preserving XOR cannot satisfy union. The
equal-operand high-bit witness is admitted independently of future behavior;
the contradiction uses its actual execution and the independent contract. -/
theorem xor_is_not_union :
    ¬Grading.ReadOnlySemanticClaim (readOnlyTask .union) (bytes .symmetricDifference) := by
  intro claimed
  let resource := EDSL.Logical64.Domain.resource (bytes .symmetricDifference)
    0x8000000000000000 0x8000000000000000
  let initial := EDSL.Logical64.Domain.initial (bytes .symmetricDifference)
    0x8000000000000000 0x8000000000000000
  have pre : ResourcePre (bytes .symmetricDifference) resource initial :=
    EDSL.Logical64.Domain.resource_pre _ (by decide) (by decide)
      0x8000000000000000 0x8000000000000000
  obtain ⟨result,actual,post,_⟩ := (claimed.resource resource initial pre).1 (fun _ => false)
  have same := execution_exact pre.machine actual
  cases same
  have impossible : ¬MathematicalResult .union 0x8000000000000000 0x8000000000000000
      ((finalState .symmetricDifference initial 8192 false).registers .rax) := by
    intro correct
    have bit := (correct ⟨63,by decide⟩).2 (Or.inl (by unfold HasBit; decide))
    exact (by unfold HasBit; decide : ¬HasBit
      ((finalState .symmetricDifference initial 8192 false).registers .rax) ⟨63,by decide⟩) bit
  exact impossible post.result

end EDSL.Tests.Logical64

#print axioms EDSL.Logical64.Client.claim
#print axioms EDSL.Logical64.Client.returned_resources
#print axioms EDSL.Logical64.minimum_modeled_instructions
#print axioms EDSL.Logical64.claim_minimum
#print axioms EDSL.X86.Sequential.step_returned_register
#print axioms EDSL.X86.Sequential.Executes.changed_register_needs_two
#print axioms EDSL.Tests.Logical64.xor_is_not_union
#audit_edsl
