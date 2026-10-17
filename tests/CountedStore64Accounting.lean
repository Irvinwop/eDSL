/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Artifact
import EDSL.CountedStore64.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CountedStore64Accounting
open EDSL X86 X86.Sequential CountedStore64

/-- An empty loop still retires MOV, TEST, JE and the actual caller RET. -/
theorem zero_cost (choices : Choices) :
    ∃ result, Sequential.run choices 4 (Domain.initial GCC.bytes 0xfeedface89abcdef 0) = .ok result ∧
      result.instructions = 4 ∧ result.reads = [⟨.stack, 65544, 8⟩] ∧
      result.state.registers .rax = 0xfeedface89abcdef ∧
      loadQWord result.state.memory 262144 = .ok 0 ∧
      ResourceReturn (Domain.resource GCC.bytes 0xfeedface89abcdef 0)
        (Domain.initial GCC.bytes 0xfeedface89abcdef 0) result := by
  have pre := Domain.resource_pre GCC.bytes (by decide) (by decide) 0xfeedface89abcdef 0
  obtain ⟨result, run, post, returned, cost, reads⟩ :=
    Artifact.resource_exact_run (by decide) pre choices
  exact ⟨result, run, cost, reads, post.result, post.value, returned⟩

/-- The complete high-half count contributes to the natural instruction cost.
No native four-billion-iteration workload is needed for this symbolic result. -/
theorem high_count_cost (choices : Choices) :
    ∃ result, Sequential.Executes choices (Domain.initial GCC.bytes 0 0x100000000) result ∧
      result.instructions = 25769803780 ∧ result.state.registers .rax = 0x100000000 ∧
      ResourceReturn (Domain.resource GCC.bytes 0 0x100000000)
        (Domain.initial GCC.bytes 0 0x100000000) result := by
  have pre := Domain.resource_pre GCC.bytes (by decide) (by decide) 0 0x100000000
  obtain ⟨result, actual, post, returned, _⟩ := (GCC.resource_semantics pre).1 choices
  have cost := (GCC.execution_exact pre.machine actual).1
  exact ⟨result, actual, cost, post.result, returned⟩

/-- The cost is a natural number, so it cannot wrap at the machine-word width. -/
theorem maximum_count_cost (choices : Choices) :
    ∃ result, Sequential.Executes choices (Domain.initial GCC.bytes 1 0xffffffffffffffff) result ∧
      result.instructions = 110680464442257309694 ∧ result.state.registers .rax = 0 ∧
      ResourceReturn (Domain.resource GCC.bytes 1 0xffffffffffffffff)
        (Domain.initial GCC.bytes 1 0xffffffffffffffff) result := by
  have pre := Domain.resource_pre GCC.bytes (by decide) (by decide) 1 0xffffffffffffffff
  obtain ⟨result, actual, post, returned, _⟩ := (GCC.resource_semantics pre).1 choices
  have cost := (GCC.execution_exact pre.machine actual).1
  exact ⟨result, actual, cost, post.result, returned⟩

/-- A genuinely admitted single-iteration call needs ten instructions. Nine
fuel units cannot omit the final RET from the retirement accounting. -/
theorem one_fuel_short :
    ResourcePre GCC.bytes (Domain.resource GCC.bytes 0 1) (Domain.initial GCC.bytes 0 1) ∧
      Sequential.run (fun _ => false) 9 (Domain.initial GCC.bytes 0 1) = .error .exhaustedFuel :=
  ⟨Domain.resource_pre GCC.bytes (by decide) (by decide) 0 1, by rfl⟩

end EDSL.Tests.CountedStore64Accounting

#print axioms EDSL.CountedStore64.GCC.execution_exact
#print axioms EDSL.Tests.CountedStore64Accounting.maximum_count_cost
#audit_edsl
