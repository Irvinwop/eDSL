/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.Loader
import EDSL.Examples.Compiler.Exit

namespace EDSL.Process
open X86 OS.AddressSpace

abbrev exitBytes := Examples.Compiler.Exit42.bytes

def checkExit42 (file : List Byte) (image : ELF.Image) : Bool :=
  ELF.checkParsed file image && ELF.checkEntry file image exitBytes

def entry (file : List Byte) (image : ELF.Image) (prior : Space) (initial : State) : State :=
  { initial with memory := toMemory (ELF.install file image prior), rip := ELF.codeAddress image }

/-- Userspace correctness, a nonempty kernel contract, all completed status
results and separately conditional progress. No Linux implementation is assumed
as a global axiom or silently included in the instruction cost. -/
def Exit42Guarantee (file : List Byte) (image : ELF.Image) (prior : Space) (initial : State) : Prop :=
  let user := entry file image prior initial
  let call := Examples.Compiler.Exit42.request user
  ELF.load file prior = .ok ⟨image, ELF.install file image prior⟩ ∧
  Invokes user call 3 ∧ ¬ Diverges user ∧
  (∀ other count, Invokes user other count → other = call ∧ count = 3) ∧
  OS.LinuxExit.supported call ∧
  (∃ trace, OS.LinuxExit.Trace call trace ∧ OS.LinuxExit.Fair trace) ∧
  (∀ trace, OS.LinuxExit.Trace call trace →
    (∀ index status, trace index = .exited status → status = 42) ∧
    (OS.LinuxExit.Fair trace → ∃ index, trace index = .exited 42))

theorem exit42_sound (file : List Byte) (image : ELF.Image)
    (checked : checkExit42 file image = true) (prior : Space) (initial : State)
    (free : ELF.fresh image prior = true) : Exit42Guarantee file image prior initial := by
  obtain ⟨parsed, codeChecked⟩ := Bool.and_eq_true_iff.mp checked
  have parsedImage := ELF.checkParsed_sound file image parsed
  have code := ELF.checked_entry_code file image exitBytes prior codeChecked
  have reaches := Examples.Compiler.Exit42.reaches_request (entry file image prior initial) code
  have allowed := Examples.Compiler.Exit42.request_supported (entry file image prior initial)
  refine ⟨ELF.load_success file prior image parsedImage free, reaches.1, reaches.2.1,
    reaches.2.2, allowed, ?_, ?_⟩
  · exact ⟨_, OS.LinuxExit.immediate_admitted _ allowed⟩
  · intro trace execution
    exact Examples.Compiler.Exit42.kernel_results _ trace execution

theorem empty_is_fresh (image : ELF.Image) : ELF.fresh image empty = true := by
  simp [ELF.fresh, allUnmapped, empty]

/-- All modeled startup registers/flags are admitted: this standalone entry
needs no caller return address, stack bytes, data mapping or runtime. -/
theorem exit42_standalone (file : List Byte) (image : ELF.Image)
    (checked : checkExit42 file image = true) (initial : State) :
    Exit42Guarantee file image empty initial :=
  exit42_sound file image checked empty initial (empty_is_fresh image)

end EDSL.Process
