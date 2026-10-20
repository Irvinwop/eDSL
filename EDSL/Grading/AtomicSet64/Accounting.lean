/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicSet64.Contract
import EDSL.X86.LockedSet64.Accounting

namespace EDSL.Grading.AtomicSet64
open X86

/-- Independent useful membership must change actual RAM. Every actual RMW
remains observable, including repeated or cancelling updates. -/
theorem Returned.event_required {desired candidate input shared initial choices evolved result}
    (returned : Returned desired (frame candidate input shared initial) shared initial choices evolved result)
    (useful : Useful desired initial) : result.events ≠ [] := by
  intro empty
  obtain ⟨old, oldRead, bits⟩ := useful
  obtain ⟨entry, word, entryRead, finalRead, mathematical⟩ := returned.post.value
  change loadQWord initial.memory (initial.registers .rdi) = .ok entry at entryRead
  have sameEntry : entry = old := Except.ok.inj (entryRead.symm.trans oldRead)
  subst entry
  rw [returned.covered.machine.memory_of_no_events empty] at finalRead
  change loadQWord initial.memory (initial.registers .rdi) = .ok word at finalRead
  have sameWord : word = old := Except.ok.inj (finalRead.symm.trans oldRead)
  exact bits.changes mathematical sameWord

/-- Useful inputs require an actual RMW plus RET in the strict logical/RET
profile. This is a retired-instruction bound, not a global x86 or timing optimum. -/
theorem Returned.useful_lower_bound {desired candidate input shared initial choices evolved result}
    (returned : Returned desired (frame candidate input shared initial) shared initial choices evolved result)
    (useful : Useful desired initial) : 2 ≤ result.instructions := by
  have positive := List.length_pos_iff.mpr (returned.event_required useful)
  have count := returned.covered.machine.event_count
  omega

theorem Claim.actual_lower_bound {desired candidate input shared initial choices fuel result}
    (claim : Claim desired candidate) (pre : EDSL.AtomicSet64.Pre candidate input shared initial)
    (useful : Useful desired initial)
    (actual : LockedSet64.run choices fuel initial = .ok result) :
    2 ≤ result.instructions := by
  obtain ⟨_, returned⟩ := claim.actual pre actual
  exact returned.useful_lower_bound useful

end EDSL.Grading.AtomicSet64
