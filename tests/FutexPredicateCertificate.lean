/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.FutexPredicateCertificate
import EDSL.Examples.FutexPredicate

set_option warningAsError true

namespace EDSL.Tests.FutexPredicateCertificate
open X86 OS OS.Futex OS.Futex.Predicate
open Examples.FutexPredicate

/-- Independent mnemonic-assembled contract: successful loads bypass WAIT;
every completion takes the forced backedge before the next predicate test. -/
def candidate : List Byte :=
  [0x8b, 0x07, 0x83, 0xf8, 0, 0x75, 0x16,
   0xb8, 202, 0, 0, 0, 0xbe, 128, 0, 0, 0,
   0x0f, 0x05, 0xb8, 1, 0, 0, 0, 0x83, 0xf8, 0, 0x75, 0xe3, 0xc3]

/-- The artifact is connected to genuine initial code/resource admission,
rather than to an assumed successful future execution. -/
theorem initial_certificate :
    EDSL.FutexPredicateCertificate.Specification candidate cohort initial 0 waiter := by
  apply EDSL.FutexPredicateCertificate.sound candidate (by decide) initial_admitted rfl
  exact (initial_protection 0 (.waitLoop waiter) rfl).2.2.1

/-- A physical LOAD learns zero before notification. The certificate must lift
the actual instruction and preserve the resulting artifact binding without a
managed-success premise. -/
theorem load_lifts :
    ∃ after, Physical.issue cohort.profile initial 0 =
        .ok (after, .machine (.retired 0 none)) ∧
      after.suspended.machine.workers[0]?.map (fun actual => actual.context.registers .rax) = some 0 ∧
      EDSL.FutexPredicateCertificate.Specification candidate cohort after 0 waiter := by
  have issued : Suspend.issue initial.suspended 0 =
      .ok (Predicate.retire initial.suspended 0 (waiter.entry.loaded 0), .machine (.retired 0 none)) := by
    rfl
  obtain ⟨after, lifted, same, certificate⟩ := initial_certificate.issue issued
  exact ⟨after, lifted, by rw [same]; rfl, certificate⟩

-- Missing the recheck jumps directly to RET after a WAIT result. The same
-- length mutant must not receive this loop's predicate-checked certificate.
example : EDSL.FutexPredicateCertificate.accepts (candidate.set 28 0) = false := by decide
-- Skipping the initial read or losing protected RET is also outside the profile.
example : EDSL.FutexPredicateCertificate.accepts (candidate.set 0 0x90) = false := by decide
example : EDSL.FutexPredicateCertificate.accepts (candidate.take 29) = false := by decide
example : EDSL.FutexPredicateCertificate.accepts (candidate ++ [0x90]) = false := by decide

/-- Handwritten ELF64LE ET_EXEC/EM_X86_64 selects offset128 as entry. An RX
segment contains the complete loop; no symbol table or objcopy output is used. -/
def elfHeader : List Byte :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   2, 0, 62, 0, 1, 0, 0, 0, 0x80, 0, 0x40, 0, 0, 0, 0, 0,
   0x40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 64, 0, 56, 0, 1, 0, 0, 0, 0, 0, 0, 0,
   1, 0, 0, 0, 5, 0, 0, 0, 0x80, 0, 0, 0, 0, 0, 0, 0,
   0x80, 0, 0x40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   30, 0, 0, 0, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0,
   0, 0x10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def elf : List Byte := elfHeader ++ candidate

def image : ELF.Image := ⟨0x400080, [⟨128, 0x400080, 30, 31, 5, 4096⟩]⟩

theorem elf_parsed : ELF.parse elf = .ok image :=
  ELF.checkParsed_sound elf image (by decide +kernel)

theorem elf_selected : EDSL.FutexPredicateCertificate.acceptsELF elf = true := by decide +kernel

/-- Full-file loading produces the entry's exact executable code for any prior
caller space. This evidence does not create the separate OS-resource setup. -/
theorem elf_current_code (prior : AddressSpace.Space) :
    CodeAt (AddressSpace.toMemory (ELF.install elf image prior)) 0x400080 candidate :=
  ELF.checked_entry_code elf image candidate prior (by decide +kernel)

-- Same loop remains elsewhere in the file, but the selected entry is shifted.
example : EDSL.FutexPredicateCertificate.acceptsELF (elf.set 24 0x81) = false := by decide +kernel
-- The final RET cannot be borrowed from RX BSS instead of the artifact file.
example : EDSL.FutexPredicateCertificate.acceptsELF (elf.set 96 29) = false := by decide +kernel
-- Header truncation, nonexecutable selection, and an in-place lost recheck fail.
example : EDSL.FutexPredicateCertificate.acceptsELF (elf.take 110) = false := by decide +kernel
example : EDSL.FutexPredicateCertificate.acceptsELF (elf.set 68 4) = false := by decide +kernel
example : EDSL.FutexPredicateCertificate.acceptsELF (elf.set 156 0) = false := by decide +kernel

end EDSL.Tests.FutexPredicateCertificate

#audit_edsl
