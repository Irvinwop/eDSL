/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.SignumBodies
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.SignumBodies
open X86 X86.Sequential Corpus.V1

/-- Owned synthetic ordinary RAM supplies only exact selected code and a
literal little-endian original caller return word. No helper evaluator or
mocked decoder participates in the checks below. -/
private def initial (bytes : List Byte) (argument : Word) : State where
  registers register := if register = .rsp then 32768
    else if register = .rdi then argument else 0xfedcba9876543210
  rip := 0
  flags := 0xed7
  memory := {
    read address := if 32768 ≤ address.toNat ∧ address.toNat < 32776 then
      ([0,0x30,0,0,0,0,0,0] : List Byte)[address.toNat - 32768]?
      else bytes[address.toNat]?
    executable address := decide (address.toNat < bytes.length)
    writable _ := false }

private def selected (af of : Bool) : FlagChoices :=
  ⟨true,true,af,true,true,of⟩

/-- Only the independent integer-order result contract is graded. Failure to
return, unsupported bytes or a wrong result each fail this predicate. -/
private def satisfies (choices : FlagChoices) (bytes : List Byte) (argument : Word) : Bool :=
  match runWith (fun _ => choices) 7 (initial bytes argument) with
  | .ok result =>
    letI : Decidable (WordMath.Signum (argument.setWidth 32).toInt
        ((result.state.registers .rax).setWidth 32).toInt) := by
      unfold WordMath.Signum
      infer_instance
    decide (WordMath.Signum (argument.setWidth 32).toInt
      ((result.state.registers .rax).setWidth 32).toInt)
  | .error _ => false

/-- Includes signed minimum/maximum, -1, zero and one with unrelated incoming
high32 bits. All off-diagonal AF/OF patterns satisfy the same order contract. -/
theorem original_corners :
    ([.defaultGCC,.defaultClang] : List SignumCode.Compiler).all
      (fun compiler =>
        ([selected false false,selected false true,selected true false,selected true true] :
          List FlagChoices).all (fun choices =>
          ([0x1234567880000000,0x76543210ffffffff,0xabcdef0100000000,
            0xfedcba9800000001,0x13579bdf7fffffff] : List Word).all
            (satisfies choices (SignumCode.bytes compiler)))) = true := by
  decide +kernel

/-- GCC's count31→30 mutation returns -2 on INT32_MIN. SAR in place of SHR
instead reverses the negative result. Neither satisfies the independent spec. -/
theorem gcc_wrong_shift :
    satisfies (selected false true) ((SignumCode.bytes .defaultGCC).set 13 30)
      0x1234567880000000 = false ∧
    satisfies (selected true false) ((SignumCode.bytes .defaultGCC).set 12 0xff)
      0x76543210ffffffff = false := by
  decide +kernel

/-- Clang OR→XOR fails on -1; SETNE→SETE fails at zero. These are semantic
counterexamples on owned mutations, not merely changes to artifact identity. -/
theorem clang_wrong_boolean :
    satisfies (selected false true) ((SignumCode.bytes .defaultClang).set 12 0x31)
      0x76543210ffffffff = false ∧
    satisfies (selected true false) ((SignumCode.bytes .defaultClang).set 10 0x94)
      0xabcdef0100000000 = false := by
  decide +kernel

/-- The original proposed graphs cannot authenticate changed operations or
final RET bytes, even when an individual mutation preserves this result. -/
theorem changed_graphs_reject :
    CFG.check ((SignumCode.bytes .defaultGCC).set 13 30) SignumBodies.gccGraph = false ∧
    CFG.check ((SignumCode.bytes .defaultClang).set 4 30) SignumBodies.clangGraph = false ∧
    CFG.check ((SignumCode.bytes .defaultClang).set 14 0x90) SignumBodies.clangGraph = false := by
  decide +kernel

end EDSL.Tests.SignumBodies
#audit_edsl
