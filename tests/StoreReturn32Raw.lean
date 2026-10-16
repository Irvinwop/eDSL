/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.StoreReturn32.RawProof
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.StoreReturn32Raw
open EDSL X86 X86.Sequential StoreReturn32

/-- A successful theorem for any actual return carries the stronger pointer
contract and exact accounting; it is not limited to a chosen evaluation fuel. -/
theorem actual_return_contract {shape : Shape} {input initial choices result}
    (pre : Grading.Write32.Pre shape.bytes input initial)
    (execution : Sequential.Executes choices initial result) :
    result.state.registers .rax = input.address ∧
      loadDWord result.state.memory input.address = .ok (input.argument.setWidth 32) ∧
      result.instructions = 3 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] := by
  have contract := Sequential.AllExecutions.project (raw_semantics pre).1 ⟨choices, execution⟩
  exact ⟨contract.1.pointer, contract.1.value, contract.2⟩

/-- A truncated returned pointer cannot meet the independent postcondition
at any address above4GiB, even if the low32 store and ABI otherwise succeed. -/
theorem rejects_truncated_pointer {input : Grading.Write32.Input} {initial final : State}
    (large : 2^32 ≤ input.address.toNat)
    (truncated : final.registers .rax = (input.address.setWidth 32).setWidth 64) :
    ¬StoreReturn32.Post input initial final := by
  intro post
  have equal := congrArg BitVec.toNat (truncated.symm.trans post.pointer)
  simp only [BitVec.toNat_setWidth] at equal
  have small : input.address.toNat % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
  have widened : input.address.toNat % 2^32 < 2^64 := by omega
  rw [Nat.mod_eq_of_lt widened] at equal
  omega

/-- Omitting REX.W, reversing the pointer copy, changing store source/width,
or appending bytes cannot acquire the exact production artifact theorem. -/
theorem rejects_semantic_mutants :
    ([[0x89,0xf8,0x89,0x37,0xc3],
      [0x48,0x89,0xc7,0x89,0x37,0xc3],
      [0x48,0x89,0xf8,0x89,0x3f,0xc3],
      [0x48,0x89,0xf8,0x48,0x89,0x37,0xc3],
      [0x48,0x89,0xf8,0x89,0x37,0xc3,0x90]] : List (List Byte)).map check =
      [none, none, none, none, none] := by decide

end EDSL.Tests.StoreReturn32Raw

#print axioms EDSL.StoreReturn32.raw_semantics
#print axioms EDSL.StoreReturn32.modeled_accounting
#print axioms EDSL.Tests.StoreReturn32Raw.actual_return_contract
#print axioms EDSL.Tests.StoreReturn32Raw.rejects_truncated_pointer
#audit_edsl
