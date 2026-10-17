/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.CallMemory64.Artifact
import EDSL.Grading.Hex
import tests.fixtures.CallMemory64.Covered
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.GradingCallMemory64Artifact
open X86 OS EDSL.CallMemory64 EDSL.Grading.CallMemory64

-- Independent literal final text includes the helper AFTER the caller's RET.
-- Eq.refl must reduce the real selector, just as the grading wrapper does.
def gccRaw : Artifact := .raw
  [0x50,0xe8,5,0,0,0,0x5a,0x48,0xff,0xc0,0xc3,0x48,0x89,0x37,0x48,0x8b,7,0xc3] 0

def clangRaw : Artifact := .raw
  [0x50,0xe8,5,0,0,0,0x48,0xff,0xc0,0x59,0xc3,0x48,0x89,0x37,0x48,0x8b,7,0xc3] 0

theorem gcc_raw : Artifact.Claim gccRaw :=
  Artifact.certify gccRaw (Compiler.program .gccSeparate) rfl Client.gccSeparate

theorem clang_raw : Artifact.Claim clangRaw :=
  Artifact.certify clangRaw (Compiler.program .clangSeparate) rfl Client.clangSeparate

-- Recover the independent DATA-word contract for the exact literal bytes and
-- entry. Accidentally aliasing the old x+2 task makes this theorem ill-typed.
theorem raw_semantics {bytes entry} (claim : Artifact.Claim (.raw bytes entry)) :
    EDSL.CallMemory64.Claim ⟨bytes, entry⟩ := by
  obtain ⟨selected, selection, semantic⟩ := claim
  obtain ⟨sameBytes, sameEntry, _⟩ := Grading.CallStack.Artifact.select_raw selection
  have same : selected.program = ⟨bytes, entry⟩ := by
    rw [← sameBytes, ← sameEntry]
  exact same ▸ semantic

-- The artifact theorem yields actual execution and current authority for
-- BOTH allocations in the same endpoint world, including the stored DATA8.
theorem raw_owner_resources {bytes entry resource initial}
    (claim : Artifact.Claim (.raw bytes entry))
    (pre : ResourcePre ⟨bytes, entry⟩ resource initial) (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.run choices result.instructions initial = .ok result ∧
      OS.CallMemory64.Current resource.descriptor evolved result.state ∧
      OS.CallMemory64.History resource.descriptor resource.shared evolved ∧
      OS.CallMemory64.Preservation resource.descriptor resource.shared evolved ∧
      StackFrame.Contract resource.descriptor.frame evolved ∧
      Borrowing.loadOwnedWord64 evolved resource.descriptor.owner resource.descriptor.ticket
        resource.descriptor.target = .ok resource.value ∧
      Post (resourceInput resource) initial result.state := by
  obtain ⟨evolved, result, actual, returned⟩ := (raw_semantics claim).run pre choices
  exact ⟨evolved, result, actual, returned.current, returned.history, returned.preservation,
    returned.current.contract.stack, returned.target_read, returned.post⟩

-- A closed artifact proof specializes to every full-width scalar and old
-- target word, arbitrary remaining registers, flags and AF streams.
theorem gcc_domain (input old : Word) (registers : Register → Word) (flags : Word)
    (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.run choices result.instructions
        (Domain.initial (Compiler.program .gccSeparate) input old registers flags) = .ok result ∧
      Borrowing.loadOwnedWord64 evolved
        (Domain.descriptor (Compiler.bytes .gccSeparate)).owner
        (Domain.descriptor (Compiler.bytes .gccSeparate)).ticket Domain.target = .ok input ∧
      OS.CallMemory64.Current (Domain.descriptor (Compiler.bytes .gccSeparate)) evolved
        result.state ∧
      Post (resourceInput (Domain.resource (Compiler.program .gccSeparate) input old))
        (Domain.initial (Compiler.program .gccSeparate) input old registers flags) result.state := by
  have pre := Domain.resource_pre (Compiler.program .gccSeparate) (by decide) (by decide)
    input old registers flags
  obtain ⟨evolved, result, actual, current, _, _, _, owned, post⟩ :=
    raw_owner_resources gcc_raw pre choices
  exact ⟨evolved, result, actual, owned, current, post⟩

-- Turn decidable byte/entry observations into selection of the same Program,
-- without adding an equality instance to the existing artifact library.
theorem selected_program (artifact : Artifact) (program : Program)
    (coordinates : (Grading.CallStack.Artifact.selectedProgram artifact).map
      (fun selected => (selected.bytes, selected.entry)) = some (program.bytes, program.entry)) :
    Grading.CallStack.Artifact.selectedProgram artifact = some program := by
  cases selection : Grading.CallStack.Artifact.selectedProgram artifact with
  | none => simp [selection] at coordinates
  | some actual =>
    have observed : (actual.bytes, actual.entry) = (program.bytes, program.entry) := by
      simpa only [selection, Option.map_some, Option.some.injEq] using coordinates
    have same : actual = program := by
      cases actual
      cases program
      simpa only [Prod.mk.injEq, CallStack.Program.mk.injEq] using observed
    exact congrArg some same

-- Independent ELF64LE ET_EXEC: code starts at 0x400080, file-backed extent
-- 18, RAM extent 26. The complete literal container is kernel checked.
def gccFile : List Byte := Grading.Hex.literal (
  "7f454c46020101000000000000000000" ++
  "02003e00010000008000400000000000" ++
  "40000000000000000000000000000000" ++
  "00000000400038000100000000000000" ++
  "01000000050000008000000000000000" ++
  "80004000000000000000000000000000" ++
  "12000000000000001a00000000000000" ++
  "00100000000000000000000000000000" ++
  "50e8050000005a48ffc0c3488937488b07c3")

theorem gcc_elf : Artifact.Claim (.elf gccFile 18 0) :=
  Artifact.certify (.elf gccFile 18 0) (Compiler.program .gccSeparate)
    (selected_program _ _ (by decide +kernel)) Client.gccSeparate

-- Appended non-code container bytes change literal file identity. Reusing a
-- program proof is legitimate when this new whole file passes selection too.
theorem gcc_other_container : Artifact.Claim (.elf (gccFile ++ [0xa5, 0x5a]) 18 0) :=
  Artifact.certify (.elf (gccFile ++ [0xa5, 0x5a]) 18 0)
    (Compiler.program .gccSeparate) (selected_program _ _ (by decide +kernel)) Client.gccSeparate

-- The same artifact proof retains successful full-file parsing, exact entry
-- and span, plus checked installed code for arbitrary occupied prior memory.
theorem elf_semantics_and_code {file span entry}
    (claim : Artifact.Claim (.elf file span entry)) (prior : AddressSpace.Space) :
    ∃ selected image start,
      Grading.CallStack.Artifact.select (.elf file span entry) = .ok selected ∧
      ELF.parse file = .ok image ∧
      selected.program.entry = entry ∧ selected.program.bytes.length = span ∧
      EDSL.CallMemory64.Claim selected.program ∧
      CodeAt (AddressSpace.toMemory (ELF.install file image prior))
        (BitVec.ofNat 64 start) selected.program.bytes ∧
      BitVec.ofNat 64 start + BitVec.ofNat 64 selected.program.entry = ELF.codeAddress image := by
  obtain ⟨selected, selection, semantic⟩ := claim
  obtain ⟨image, start, parsed, _, _, sameEntry, length, code, address⟩ :=
    Grading.CallStack.Artifact.selected_elf_code selection prior
  exact ⟨selected, image, start, selection, parsed, sameEntry, length, semantic, code, address⟩

-- RET and an unsupported byte precede entry. Neither may be scanned away;
-- the trailing helper after another RET must remain in this whole window.
def prefixedFile : List Byte :=
  (((gccFile.take 128 ++ [0xc3, 0xff] ++ gccFile.drop 128).set 24 0x82).set 96 20).set 104 28

theorem prefix_installed (prior : AddressSpace.Space) :
    CodeAt (AddressSpace.toMemory (ELF.install prefixedFile
      ⟨0x400082, [⟨128, 0x400080, 20, 28, 5, 4096⟩]⟩ prior)) 0x400080
      [0xc3,0xff,0x50,0xe8,5,0,0,0,0x5a,0x48,0xff,0xc0,0xc3,
        0x48,0x89,0x37,0x48,0x8b,7,0xc3] :=
  Grading.CallStack.Artifact.checked_window_code prefixedFile _ 0x400080 ⟨_, 2⟩ prior
    (by decide +kernel)

-- This computes the right scalar result but omits the required DATA store.
def scalarOnly : Program := ⟨[0x48,0x8d,0x46,1,0xc3], 0⟩

-- This is a real returning machine execution over arbitrary admitted
-- resources. Its correct scalar output cannot substitute for a DATA effect.
theorem scalar_only_execution {resource initial}
    (pre : ResourcePre scalarOnly resource initial) (choices : CallReturn.Choices) :
    ∃ result, CallReturn.Executes choices initial result ∧
      (result.state.registers .rax).toNat = resultNat resource.value ∧
      result.state.memory = initial.memory := by
  let middle := CallReturn.leaState initial .rax (.plain .rsi) 1
  let final := { middle.writeRegister .rsp (middle.registers .rsp + 8) with
    rip := resource.descriptor.frame.call.returnAddress }
  have code := pre.codeAt
  rw [pre.code_base] at code
  have pc : initial.rip = resource.descriptor.frame.call.code := by
    simpa only [scalarOnly, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using pre.entry
  have decoded : CallReturn.decodeAt initial = .ok (.leaDisp8 .rax (.plain .rsi) 1) :=
    CallReturn.decodeAt_code code (by decide) (by decide : 0 < scalarOnly.bytes.length)
      initial rfl (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using pc) rfl
  have first : OS.CallMemory64.CPU.Step resource.descriptor resource.shared resource.shared
      initial middle (choices 0) ⟨.next middle, []⟩ :=
    OS.CallMemory64.CPU.lift_stack
      ⟨_, _, decoded, rfl, rfl, rfl, .unchanged rfl rfl, by simp⟩
  have middlePC : middle.rip = resource.descriptor.frame.call.code + 4 := by
    change initial.rip + 4 = _
    rw [pc]
  have lastDecoded : CallReturn.decodeAt middle = .ok (.sequential (.legacy .ret)) :=
    CallReturn.decodeAt_code code (by decide) (by decide : 4 < scalarOnly.bytes.length)
      middle rfl middlePC rfl
  have current := first.current pre.current
  have last := OS.CallMemory64.CPU.lift_stack
    (StackFrame.CPU.original_ret_step current.stack (show middle.registers .rsp =
      resource.descriptor.frame.top from pre.stack) ((choices.drop 1) 0) lastDecoded)
  let result : CallReturn.Result := ⟨final, 2, [⟨.stack, middle.registers .rsp, 8⟩]⟩
  have actual : CallReturn.ExecutesFrom resource.descriptor.frame.top choices initial result :=
    .next first.machine (.ret last.machine)
  refine ⟨result, ?_, ?_, rfl⟩
  · simpa only [CallReturn.Executes, pre.stack] using actual
  · change (initial.registers .rsi + 1).toNat = resultNat resource.value
    rw [pre.argument]
    exact one_addition resource.value

theorem scalar_only_not_claim : ¬Artifact.Claim (.raw scalarOnly.bytes 0) := by
  intro artifact
  have semantic : SemanticClaim scalarOnly := (raw_semantics artifact).1
  have pre := Domain.resource_pre scalarOnly (by decide) (by decide) 1 0
  obtain ⟨result, actual, _, memory⟩ := scalar_only_execution pre (fun _ => false)
  obtain ⟨_, returned⟩ := semantic.all_results pre actual
  have observed := returned.post.stored
  change readWord result.state.memory Domain.target = .ok (1 : Word) at observed
  rw [memory] at observed
  have old := (Domain.target_read scalarOnly.bytes (by decide) (by decide) 0).2
  exact (by decide : (0 : Word) ≠ 1) (Except.ok.inj (old.symm.trans observed))

-- Host checks run the real selector, loader, decoder and machine against
-- independently specified bytes, absolute addresses and observable outputs.
#eval (show IO Unit from do
  let wide : List Byte := List.replicate 4096 0xff
  match (Grading.CallStack.Artifact.raw wide 4095).selectedProgram with
  | none => throw (IO.userError "bounded unsupported code was rejected during pure selection")
  | some program =>
    unless program.bytes == wide && program.entry == 4095 do
      throw (IO.userError "4096-byte code window or its last-byte entry was truncated")
  for candidate in [Grading.CallStack.Artifact.raw (List.replicate 4097 0xff) 0,
      .raw wide 4096] do
    unless candidate.selectedProgram.isNone do
      throw (IO.userError "raw code limit or entry bound was weakened")
  match Grading.CallStack.Artifact.select (.elf prefixedFile 20 2) with
  | .error error => throw (IO.userError s!"prefix ELF rejected: {repr error}")
  | .ok selected =>
    unless selected.program.bytes ==
        [0xc3,0xff,0x50,0xe8,5,0,0,0,0x5a,0x48,0xff,0xc0,0xc3,
          0x48,0x89,0x37,0x48,0x8b,7,0xc3] &&
        selected.program.entry == 2 && selected.start == some 0x400080 &&
        selected.image.map (·.entry) == some 0x400082 do
      throw (IO.userError "prefix, complete helper bytes or ELF entry address lost")
  for candidate in [
      Grading.CallStack.Artifact.elf prefixedFile 20 0,
      .elf prefixedFile 20 1, .elf prefixedFile 20 20,
      .elf prefixedFile 21 2, .elf (prefixedFile.take 147) 20 2,
      .elf (prefixedFile.set 68 4) 20 2,
      .elf prefixedFile 0 0, .elf prefixedFile 4097 2] do
    unless candidate.selectedProgram.isNone do
      throw (IO.userError "bad entry, span, backing or execute permission admitted")
  let expected : List Byte :=
    [0x50,0xe8,5,0,0,0,0x5a,0x48,0xff,0xc0,0xc3,0x48,0x89,0x37,0x48,0x8b,7,0xc3]
  let some helper := (Grading.CallStack.Artifact.raw expected 11).selectedProgram
    | throw (IO.userError "in-bounds helper entry was rejected during pure selection")
  unless helper.bytes == expected && helper.entry == 11 do
    throw (IO.userError "raw selection dropped bytes or replaced the literal entry")
  let observe : Program → Except Error (Word × Except Error Word) := fun program =>
    (CallReturn.run (fun _ => false) 8 (Domain.initial program 7 42)).map fun result =>
      (result.state.registers .rax, readWord result.state.memory Domain.target)
  let check : Program → Word → Word → String → IO Unit := fun program value stored message => do
    match observe program with
    | .ok (actual, .ok target) =>
      unless actual == value && target == stored do throw (IO.userError message)
    | _ => throw (IO.userError message)
  check ⟨expected, 0⟩ 8 7 "complete caller did not return x+1 and store the DATA word"
  check helper 7 7 "helper entry was silently rebound to the caller"
  match observe ⟨expected.take 11, 0⟩ with
  | .error (.inaccessibleInstruction 0x100b) => pure ()
  | _ => throw (IO.userError "truncated helper did not fault at its actual CALL target")
  check scalarOnly 8 42 "scalar-only code unexpectedly satisfied the DATA store contract"
  let unsupported : Program := ⟨[0xff], 0⟩
  match observe unsupported with
  | .error (.unsupportedOpcode 0xff) => pure ()
  | _ => throw (IO.userError "unsupported opcode was silently lowered"))

-- This uses actual current resource admission for unsupported code, then
-- proves that successful pure selection cannot supply functional correctness.
theorem unsupported_not_claim : ¬Artifact.Claim (.raw [0xff] 0) := by
  intro artifact
  have semantic := (raw_semantics artifact).1
  have pre := Domain.resource_pre ⟨[0xff], 0⟩ (by decide) (by decide) 1 0
  obtain ⟨_, _, covered, _⟩ := semantic _ _ pre (fun _ => false)
  obtain ⟨_, _, _, decoded, _⟩ := covered.fetchWithin
  have rejected : CallReturn.decodeAt (Domain.initial ⟨[0xff], 0⟩ 1 0) =
      .error (.unsupportedOpcode 0xff) := rfl
  rw [rejected] at decoded
  cases decoded

end EDSL.Tests.GradingCallMemory64Artifact

#print axioms EDSL.Grading.CallMemory64.Artifact.certify
#print axioms EDSL.Tests.GradingCallMemory64Artifact.gcc_raw
#print axioms EDSL.Tests.GradingCallMemory64Artifact.clang_raw
#print axioms EDSL.Tests.GradingCallMemory64Artifact.raw_semantics
#print axioms EDSL.Tests.GradingCallMemory64Artifact.raw_owner_resources
#print axioms EDSL.Tests.GradingCallMemory64Artifact.gcc_domain
#print axioms EDSL.Tests.GradingCallMemory64Artifact.gcc_elf
#print axioms EDSL.Tests.GradingCallMemory64Artifact.gcc_other_container
#print axioms EDSL.Tests.GradingCallMemory64Artifact.elf_semantics_and_code
#print axioms EDSL.Tests.GradingCallMemory64Artifact.prefix_installed
#print axioms EDSL.Tests.GradingCallMemory64Artifact.scalar_only_execution
#print axioms EDSL.Tests.GradingCallMemory64Artifact.scalar_only_not_claim
#print axioms EDSL.Tests.GradingCallMemory64Artifact.unsupported_not_claim
#audit_edsl
