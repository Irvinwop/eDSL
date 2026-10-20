/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.CallStack.Artifact
import EDSL.Grading.Hex
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.GradingCallStackContract
open X86 OS EDSL.CallStack EDSL.Grading.CallStack

-- A RET before the entry and an unsupported byte must both remain bound to
-- the selected whole file; selection does not decode or truncate at a RET.
example : ((Artifact.raw [0xc3, 0xff, 0x90] 2).selectedProgram.map
    (fun program => (program.bytes, program.entry))) = some ([0xc3, 0xff, 0x90], 2) := by
  decide

-- Independent ELF64LE ET_EXEC: RX file interval [0x400080, 0x40008e),
-- BSS through 0x400094, entry 0x400085. A five-byte helper precedes CALL.
def file : List Byte := Grading.Hex.literal (
  "7f454c46020101000000000000000000" ++
  "02003e00010000008500400000000000" ++
  "40000000000000000000000000000000" ++
  "00000000400038000100000000000000" ++
  "01000000050000008000000000000000" ++
  "80004000000000000000000000000000" ++
  "0e000000000000001400000000000000" ++
  "00100000000000000000000000000000" ++
  "488d4701c3e8f6ffffff48ffc0c3")

-- Host evaluation checks independent byte/address expectations. The installed
-- window theorem below separately checks the universal prior-space proof.
#eval (show IO Unit from do
  let expected : List Byte :=
    [0x48, 0x8d, 0x47, 1, 0xc3, 0xe8, 0xf6, 0xff, 0xff, 0xff, 0x48, 0xff, 0xc0, 0xc3]
  match (Artifact.elf file 14 5).select with
  | .error error => throw (IO.userError s!"helper-prefix ELF rejected: {repr error}")
  | .ok selected =>
    unless selected.program.bytes == expected && selected.program.entry == 5 &&
        selected.start == some 0x400080 &&
        selected.image.map (·.entry) == some 0x400085 do
      throw (IO.userError "ELF selection lost the helper prefix or entry binding")
  for candidate in [Artifact.raw [] 0, Artifact.raw [0xc3] 1,
      Artifact.raw [0xc3] 100, Artifact.raw (List.replicate 4097 0x90) 0,
      Artifact.elf file 0 0, Artifact.elf file 4097 5,
      Artifact.elf file 14 14, Artifact.elf file 14 6,
      Artifact.elf file 14 0, Artifact.elf file 15 5,
      Artifact.elf (file.take 141) 14 5,
      Artifact.elf (file.set 96 15) 14 5,
      Artifact.elf (file.set 68 4) 14 5] do
    unless candidate.selectedProgram.isNone do
      throw (IO.userError "invalid entry, extent, file backing or execute permission admitted")
  let longer := ((file.take 128 ++ List.replicate 65 0x90).set 96 65).set 104 65
  match (Artifact.elf longer 65 5).selectedProgram with
  | none => throw (IO.userError "complete 65-byte code window rejected")
  | some program =>
    unless program.bytes == List.replicate 65 0x90 && program.entry == 5 do
      throw (IO.userError "65-byte whole code window was truncated"))

-- The current installed code proof ranges over arbitrary existing cells,
-- without a freshness hypothesis. Entry RIP is the ELF entry, not the start.
theorem installed_window (prior : OS.AddressSpace.Space) :
    CodeAt (OS.AddressSpace.toMemory (ELF.install file
      ⟨0x400085, [⟨128, 0x400080, 14, 20, 5, 4096⟩]⟩ prior))
      0x400080 [0x48, 0x8d, 0x47, 1, 0xc3, 0xe8, 0xf6, 0xff, 0xff, 0xff,
        0x48, 0xff, 0xc0, 0xc3] := by
  exact Artifact.checked_window_code file _ 0x400080 ⟨_, 5⟩ prior (by decide +kernel)

-- Truncated FF group bytes still have useful OS-admitted inputs. This
-- would fail if admission started requiring a decode, trace or postcondition.
theorem unsupported_nonvacuous : Nonvacuous Domain.unsupported :=
  domain_nonvacuous Domain.unsupported (by decide) (by decide)

-- Resource admission alone cannot prove raw or resource-first correctness.
-- The actual CallReturn decoder faults fetching the missing ModRM byte.
theorem unsupported_not_semantic : ¬SemanticClaim Domain.unsupported := by
  intro claim
  obtain ⟨_, _, covered, _⟩ := claim _ _ Domain.unsupported_admitted (fun _ => false)
  obtain ⟨_, instruction, _, decoded, _⟩ := covered.fetchWithin
  have rejected : CallReturn.decodeAt (Domain.initial Domain.unsupported 0xfffffffffffffffe) =
      .error (.inaccessibleInstruction 4097) := rfl
  rw [rejected] at decoded
  cases decoded

theorem unsupported_not_claim : ¬Claim Domain.unsupported :=
  fun claim => unsupported_not_semantic claim.1

-- Corrupting the live frame ticket must invalidate admission even with the
-- same real initialized memory, code loan, caller loan and machine state.
def stale : Resources :=
  let original := Domain.resource Domain.unsupported 0xfffffffffffffffe
  { original with frame := { original.frame with ticket := ⟨4, 1⟩ } }

theorem stale_resource_rejected :
    ¬ResourcePre Domain.unsupported stale
      (Domain.initial Domain.unsupported 0xfffffffffffffffe) := by
  intro pre
  obtain ⟨allocation, authorized, _⟩ := pre.current.contract.allocation
  cases authorized

-- These execute the real OS borrowing/ownership gates. Whole-word containment
-- rejects a one-byte overrun into the immutable original caller slot.
#eval (show IO Unit from do
  let resource := Domain.resource Domain.unsupported 0xfffffffffffffffe
  let rejected := fun operation =>
    match Borrowing.mutate resource.shared operation with
    | .error _ => true
    | .ok _ => false
  for operation in [
      Ownership.Mutation.store64 resource.frame.owner ⟨4, 1⟩ 65536 0xffffffffffffffff,
      .store64 (resource.frame.owner + 1) resource.frame.ticket 65536 0xffffffffffffffff,
      .store64 resource.frame.owner resource.frame.ticket 65537 0xffffffffffffffff] do
    unless rejected operation do
      throw (IO.userError "stale ticket, wrong owner or partial private qword admitted")
  unless !(rejected (.store64 resource.frame.owner resource.frame.ticket 65536 0xfedcba9876543210)) do
    throw (IO.userError "current complete private qword store rejected"))

end EDSL.Tests.GradingCallStackContract

#print axioms EDSL.Grading.CallStack.domain_nonvacuous
#print axioms EDSL.Grading.CallStack.SemanticClaim.run
#print axioms EDSL.Grading.CallStack.SemanticClaim.all_results
#print axioms EDSL.Grading.CallStack.SemanticClaim.actual
#print axioms EDSL.Grading.CallStack.Returned.store64
#print axioms EDSL.Grading.CallStack.Artifact.certify
#print axioms EDSL.Grading.CallStack.Artifact.selected_elf_code
#audit_edsl
