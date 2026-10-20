/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicLogical64.Contract
import EDSL.X86.LockedLogical64.Accounting

namespace EDSL.Grading.AtomicLogical64
open X86

/-- A useful requested bit must change in actual RAM. Therefore the certified
return cannot have an empty real event trace. This is separate from admission
and applies equally to implementations with repeated/no-change RMW events. -/
theorem Returned.event_required {candidate input shared initial choices evolved result}
    (returned : Returned (frame candidate input shared initial) shared initial choices evolved result)
    (useful : Useful initial) : result.events ≠ [] := by
  intro empty
  obtain ⟨old, readOld, index, absent, requested⟩ := useful
  obtain ⟨entry, word, entryRead, finalRead, union⟩ := returned.post.value
  change loadQWord initial.memory (initial.registers .rdi) = .ok entry at entryRead
  have sameEntry : entry = old := Except.ok.inj (entryRead.symm.trans readOld)
  subst entry
  have memory := returned.covered.machine.memory_of_no_events empty
  rw [memory] at finalRead
  change loadQWord initial.memory (initial.registers .rdi) = .ok word at finalRead
  have sameWord : word = old := Except.ok.inj (finalRead.symm.trans readOld)
  subst word
  exact absent ((union index).mpr (Or.inr requested))

/-- At least one actual RMW plus RET is necessary on every useful admitted
input. Counts are retired instructions in the strict OR/RET model only; this
is not a global x86 instruction, micro-op, latency or source-level optimum. -/
theorem Returned.useful_lower_bound {candidate input shared initial choices evolved result}
    (returned : Returned (frame candidate input shared initial) shared initial choices evolved result)
    (useful : Useful initial) : 2 ≤ result.instructions := by
  have positive := List.length_pos_iff.mpr (returned.event_required useful)
  have count := returned.covered.machine.event_count
  omega

/-- Every successful actual run is subject to the same independent lower
bound, with arbitrary supplied fuel and arbitrary AF choices. -/
theorem Claim.actual_lower_bound {candidate input shared initial choices fuel result}
    (claim : Claim candidate) (pre : EDSL.AtomicLogical64.Pre candidate input shared initial)
    (useful : Useful initial)
    (actual : LockedLogical64.run choices fuel initial = .ok result) :
    2 ≤ result.instructions := by
  obtain ⟨_, returned⟩ := claim.actual pre actual
  exact returned.useful_lower_bound useful

end EDSL.Grading.AtomicLogical64
