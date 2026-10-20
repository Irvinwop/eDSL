/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.AtomicSet64.Contract
import EDSL.Grading.AtomicLogical64.Domain

namespace EDSL.AtomicSet64.Domain
open X86

/-- The existing domain is a byte-span/resource constructor, not an OR
decoder. Reuse its checked fresh installation, ownership, initialization,
persistent cell, actor handle and code/caller loans for arbitrary input bytes. -/
abbrev World := Grading.AtomicLogical64.Domain.shared
abbrev cpu := Grading.AtomicLogical64.Domain.initial
abbrev input := Grading.AtomicLogical64.Domain.input

theorem admitted_bytes (candidate : List Byte) (positive : 0 < candidate.length)
    (bound : candidate.length ≤ 4096) (old mask : Word) :
    Pre candidate input (World candidate old) (cpu candidate old mask) :=
  Grading.AtomicLogical64.Domain.resource_pre candidate positive bound old mask

/-- Every old word and mask has a real current-resource invocation for each
selected operation. The universal callable theorem therefore has an inhabited
domain, including useful changed results and unchanged/zero inputs. -/
theorem admitted (operation : Logical64.Operation) (old mask : Word) :
    Pre (bytes operation) input (World (bytes operation) old) (cpu (bytes operation) old mask) :=
  admitted_bytes _ (by cases operation <;> decide) (by cases operation <;> decide) old mask

theorem realized (operation : Logical64.Operation) (old mask : Word) :
    loadQWord (cpu (bytes operation) old mask).memory
      ((cpu (bytes operation) old mask).registers .rdi) = .ok old ∧
    (cpu (bytes operation) old mask).registers .rsi = mask ∧
    LockedSet64.AllExecutions (cpu (bytes operation) old mask)
      (ResultContract operation input (World (bytes operation) old) (cpu (bytes operation) old mask)) := by
  exact ⟨Grading.AtomicLogical64.Domain.old_read _ (by cases operation <;> decide) old mask,
    rfl, semantics operation (admitted operation old mask)⟩

end EDSL.AtomicSet64.Domain
