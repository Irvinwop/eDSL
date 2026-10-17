/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.CallMemoryLoop64.Artifact
import EDSL.Grading.Hex
import tests.fixtures.CallMemoryLoop64.GCC
import tests.fixtures.CallMemoryLoop64.Clang
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.GradingCallMemoryLoop64Artifact
open X86 OS EDSL.CallMemoryLoop64 EDSL.Grading.CallMemoryLoop64

-- Independent complete text literals retain the helpers beyond caller RET.
-- These use the same reducible selection equality as the fixed controller.
def gccRaw : Artifact := .raw
  [0x55,0x48,0x89,0xfd,0x53,0x48,0x89,0xd3,0x51,0x48,0x85,0xdb,0x74,0x11,
   0x48,0x89,0xef,0x48,0xff,0xcb,0xe8,0x0d,0,0,0,0x48,0x8d,0x70,1,0xeb,0xea,
   0x5a,0x48,0x89,0xf0,0x5b,0x5d,0xc3,0x48,0x89,0x37,0x48,0x8b,7,0xc3] 0

def clangRaw : Artifact := .raw
  [0x48,0x89,0xf0,0x48,0x85,0xd2,0x74,0x24,0x41,0x56,0x53,0x50,0x48,0x89,
   0xd3,0x49,0x89,0xfe,0x4c,0x89,0xf7,0x48,0x89,0xc6,0xe8,0x10,0,0,0,0x48,
   0xff,0xc0,0x48,0xff,0xcb,0x75,0xed,0x48,0x83,0xc4,8,0x5b,0x41,0x5e,0xc3,
   0x48,0x89,0x37,0x48,0x8b,7,0xc3] 0

theorem gcc_raw : Artifact.Claim gccRaw :=
  Artifact.certify gccRaw (Compiler.program .gccSeparate) rfl GCC.claim

theorem clang_raw : Artifact.Claim clangRaw :=
  Artifact.certify clangRaw (Compiler.program .clangSeparate) rfl Clang.claim

-- Recover the independent counted contract for exactly the literal bytes
-- and entry. An alias of the scalar CallMemory64 claim cannot typecheck here.
theorem raw_semantics {bytes entry} (claim : Artifact.Claim (.raw bytes entry)) :
    EDSL.CallMemoryLoop64.Claim ⟨bytes, entry⟩ := by
  obtain ⟨selected, selection, semantic⟩ := claim
  obtain ⟨sameBytes, sameEntry, _⟩ := Grading.CallStack.Artifact.select_raw selection
  have same : selected.program = ⟨bytes, entry⟩ := by
    rw [← sameBytes, ← sameEntry]
  exact same ▸ semantic

-- Both current allocations, the covered history and the owned DATA read
-- belong to the same actual endpoint, for arbitrary admitted resources.
-- Zero retains an independently observed old word; every nonzero full64
-- count yields the independently specified last stored value.
theorem raw_owner_resources {bytes entry resource initial old}
    (claim : Artifact.Claim (.raw bytes entry))
    (pre : ResourcePre ⟨bytes, entry⟩ resource initial)
    (before : readWord initial.memory resource.descriptor.target = .ok old)
    (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.run choices result.instructions initial = .ok result ∧
      OS.CallMemory64.Current resource.descriptor evolved result.state ∧
      OS.CallMemory64.History resource.descriptor resource.shared evolved ∧
      OS.CallMemory64.Preservation resource.descriptor resource.shared evolved ∧
      StackFrame.Contract resource.descriptor.frame evolved ∧
      Borrowing.loadOwnedWord64 evolved resource.descriptor.owner resource.descriptor.ticket
        resource.descriptor.target =
          .ok (if resource.count = 0 then old else targetWord resource.value resource.count) ∧
      Post (resourceInput resource) initial result.state := by
  obtain ⟨evolved, result, actual, returned⟩ := (raw_semantics claim).run pre choices
  refine ⟨evolved, result, actual, returned.current, returned.history, returned.preservation,
    returned.current.contract.stack, ?_, returned.post⟩
  by_cases zero : resource.count = 0
  · simpa only [zero, ↓reduceIte] using returned.target_read_zero zero before
  · simpa only [zero, ↓reduceIte] using returned.target_read_nonzero zero

-- Successful raw selection supplies the bounds for checked capacity-32 and
-- DATA allocation. Admission and execution cover every count, arbitrary old
-- contents, arbitrary unbound registers/flags, and every AF stream.
theorem raw_domain_outputs {bytes entry} (claim : Artifact.Claim (.raw bytes entry))
    (input count old : Word) (registers : Register → Word) (flags : Word)
    (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.run choices result.instructions
        (Domain.initial ⟨bytes, entry⟩ input count old registers flags) = .ok result ∧
      OS.CallMemory64.Current (Domain.resource ⟨bytes, entry⟩ input count old).descriptor
        evolved result.state ∧
      Borrowing.loadOwnedWord64 evolved
        (Domain.resource ⟨bytes, entry⟩ input count old).descriptor.owner
        (Domain.resource ⟨bytes, entry⟩ input count old).descriptor.ticket
        CallMemory64.CapacityDomain.target =
          .ok (if count = 0 then old else targetWord input count) ∧
      (result.state.registers .rax).toNat = resultNat input count := by
  have boundsClaim := claim
  obtain ⟨selected, selection, _⟩ := boundsClaim
  obtain ⟨_, _, _, _, entryBound, bound⟩ := Grading.CallStack.Artifact.select_raw selection
  have pre := Domain.resource_pre ⟨bytes, entry⟩ entryBound bound
    input count old registers flags
  have before := (CallMemory64.CapacityDomain.target_read 32
    CallStack.CapacityDomain.supported32 bytes (by omega) bound old).2
  obtain ⟨evolved, result, actual, current, _, _, _, owned, post⟩ :=
    raw_owner_resources claim pre before choices
  exact ⟨evolved, result, actual, current, owned, post.value⟩

-- A concrete zero-count consequence still quantifies over the actual initial
-- DATA value and all machine choices; it does not replace the old word by x.
theorem gcc_zero (input old : Word) (registers : Register → Word) (flags : Word)
    (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.run choices result.instructions
        (Domain.initial (Compiler.program .gccSeparate) input 0 old registers flags) = .ok result ∧
      Borrowing.loadOwnedWord64 evolved
        (Domain.resource (Compiler.program .gccSeparate) input 0 old).descriptor.owner
        (Domain.resource (Compiler.program .gccSeparate) input 0 old).descriptor.ticket
        CallMemory64.CapacityDomain.target = .ok old ∧
      (result.state.registers .rax).toNat = input.toNat := by
  obtain ⟨evolved, result, actual, _, owned, value⟩ :=
    raw_domain_outputs gcc_raw input 0 old registers flags choices
  refine ⟨evolved, result, actual, ?_, ?_⟩
  · exact owned
  · change (result.state.registers .rax).toNat = input.toNat % 2^64 at value
    simpa only [Nat.mod_eq_of_lt input.isLt] using value

-- This wraparound case requires 2^64-1 iterations in the nested fixture.
-- It follows from the artifact proof without running or bounding that loop.
theorem clang_maximum_count (old : Word) (registers : Register → Word) (flags : Word)
    (choices : CallReturn.Choices) :
    ∃ evolved result,
      CallReturn.run choices result.instructions
        (Domain.initial (Compiler.program .clangSeparate) 1 0xffffffffffffffff old
          registers flags) = .ok result ∧
      Borrowing.loadOwnedWord64 evolved
        (Domain.resource (Compiler.program .clangSeparate) 1 0xffffffffffffffff old).descriptor.owner
        (Domain.resource (Compiler.program .clangSeparate) 1 0xffffffffffffffff old).descriptor.ticket
        CallMemory64.CapacityDomain.target = .ok 0xffffffffffffffff ∧
      (result.state.registers .rax).toNat = 0 := by
  obtain ⟨evolved, result, actual, _, owned, value⟩ :=
    raw_domain_outputs clang_raw 1 0xffffffffffffffff old registers flags choices
  exact ⟨evolved, result, actual, owned, value⟩

-- Observe byte/entry coordinates without changing the shared Program type.
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

-- Small complete ELF64LE ET_EXEC: code at 0x400080, file-backed extent 45,
-- memory extent 53. This literal container is checked by the kernel.
def gccFile : List Byte := Grading.Hex.literal (
  "7f454c46020101000000000000000000" ++
  "02003e00010000008000400000000000" ++
  "40000000000000000000000000000000" ++
  "00000000400038000100000000000000" ++
  "01000000050000008000000000000000" ++
  "80004000000000000000000000000000" ++
  "2d000000000000003500000000000000" ++
  "00100000000000000000000000000000" ++
  "554889fd534889d3514885db74114889ef48ffcbe80d000000488d7001ebea" ++
  "5a4889f05b5dc3488937488b07c3")

theorem gcc_elf : Artifact.Claim (.elf gccFile 45 0) :=
  Artifact.certify (.elf gccFile 45 0) (Compiler.program .gccSeparate)
    (selected_program _ _ (by decide +kernel)) GCC.claim

-- Whole-file identity changes, but reuse of a program proof is legitimate
-- after checking selection against the new literal container as well.
theorem gcc_other_container : Artifact.Claim (.elf (gccFile ++ [0xa5, 0x5a]) 45 0) :=
  Artifact.certify (.elf (gccFile ++ [0xa5, 0x5a]) 45 0) (Compiler.program .gccSeparate)
    (selected_program _ _ (by decide +kernel)) GCC.claim

-- Recover the counted claim, parse, entire span and entry, and actual code
-- installation for every prior space, including arbitrary occupied memory.
theorem elf_semantics_and_code {file span entry}
    (claim : Artifact.Claim (.elf file span entry)) (prior : AddressSpace.Space) :
    ∃ selected image start,
      Grading.CallStack.Artifact.select (.elf file span entry) = .ok selected ∧
      ELF.parse file = .ok image ∧
      selected.program.entry = entry ∧ selected.program.bytes.length = span ∧
      EDSL.CallMemoryLoop64.Claim selected.program ∧
      CodeAt (AddressSpace.toMemory (ELF.install file image prior))
        (BitVec.ofNat 64 start) selected.program.bytes ∧
      BitVec.ofNat 64 start + BitVec.ofNat 64 selected.program.entry = ELF.codeAddress image := by
  obtain ⟨selected, selection, semantic⟩ := claim
  obtain ⟨image, start, parsed, _, _, sameEntry, length, code, address⟩ :=
    Grading.CallStack.Artifact.selected_elf_code selection prior
  exact ⟨selected, image, start, selection, parsed, sameEntry, length, semantic, code, address⟩

-- A RET and unsupported byte before the entry must survive whole-window
-- installation, as must the helper after the caller's RET.
def prefixedFile : List Byte :=
  (((gccFile.take 128 ++ [0xc3, 0xff] ++ gccFile.drop 128).set 24 0x82).set 96 47).set 104 55

theorem prefix_installed (prior : AddressSpace.Space) :
    CodeAt (AddressSpace.toMemory (ELF.install prefixedFile
      ⟨0x400082, [⟨128, 0x400080, 47, 55, 5, 4096⟩]⟩ prior)) 0x400080
      ([0xc3, 0xff] ++ Compiler.bytes .gccSeparate) :=
  Grading.CallStack.Artifact.checked_window_code prefixedFile _ 0x400080 ⟨_, 2⟩ prior
    (by decide +kernel)

-- This owned synthetic program implements the old task's scalar/DATA pair
-- on an actual execution, ignoring count. The second has the correct scalar
-- zero-count result but overwrites the old DATA word.
def oldTask : Program := ⟨[0x48,0x89,0x37,0x48,0x8d,0x46,1,0xc3], 0⟩
def storeAndReturn : Program := ⟨[0x48,0x89,0x37,0x48,0x89,0xf0,0xc3], 0⟩

def observe (program : Program) (value count old : Word) (fuel : Nat) :
    Option (Word × Option Word) :=
  (CallReturn.run (fun _ => false) fuel (Domain.initial program value count old)).toOption.map
    fun result => (result.state.registers .rax,
      (readWord result.state.memory CallMemory64.CapacityDomain.target).toOption)

private theorem except_ok {result : Except ε α} {value : α}
    (observed : result.toOption = some value) : result = .ok value := by
  cases result with
  | error fault => cases observed
  | ok actual => exact congrArg Except.ok (Option.some.inj observed)

theorem old_task_not_count_claim : ¬Artifact.Claim (.raw oldTask.bytes 0) := by
  intro claim
  have observed : observe oldTask 7 2 42 3 = some (8, some 7) := by decide +kernel
  have pre := Domain.resource_pre oldTask (by decide) (by decide) 7 2 42
  cases actual : CallReturn.run (fun _ => false) 3 (Domain.initial oldTask 7 2 42) with
  | error error =>
    unfold observe at observed
    rw [actual] at observed
    cases observed
  | ok result =>
    obtain ⟨_, returned⟩ := (raw_semantics claim).1.actual pre actual
    have output : result.state.registers .rax = 8 := by
      exact (Prod.mk.inj (Option.some.inj (by
        simpa only [observe, actual, Except.toOption, Option.map_some] using observed))).1
    have value := returned.post.value
    rw [output] at value
    exact (by decide : (8 : Word).toNat ≠ resultNat 7 2) value

theorem zero_store_not_count_claim : ¬Artifact.Claim (.raw storeAndReturn.bytes 0) := by
  intro claim
  have observed : observe storeAndReturn 7 0 42 3 = some (7, some 7) := by decide +kernel
  have pre := Domain.resource_pre storeAndReturn (by decide) (by decide) 7 0 42
  cases actual : CallReturn.run (fun _ => false) 3 (Domain.initial storeAndReturn 7 0 42) with
  | error error =>
    unfold observe at observed
    rw [actual] at observed
    cases observed
  | ok result =>
    obtain ⟨_, returned⟩ := (raw_semantics claim).1.actual pre actual
    have stored : readWord result.state.memory CallMemory64.CapacityDomain.target = .ok 7 := by
      exact except_ok (Prod.mk.inj (Option.some.inj (by
        simpa only [observe, actual, Except.toOption, Option.map_some] using observed))).2
    have old : readWord (Domain.initial storeAndReturn 7 0 42).memory
        CallMemory64.CapacityDomain.target = .ok 42 :=
      (CallMemory64.CapacityDomain.target_read 32
        CallStack.CapacityDomain.supported32 storeAndReturn.bytes (by decide) (by decide) 42).2
    have retained := returned.post.stored
    change readWord result.state.memory CallMemory64.CapacityDomain.target =
      readWord (Domain.initial storeAndReturn 7 0 42).memory CallMemory64.CapacityDomain.target at retained
    rw [old] at retained
    exact (by decide : (7 : Word) ≠ 42) (Except.ok.inj (stored.symm.trans retained))

-- Host checks execute the actual selector and machine. Their expected
-- arithmetic, helper entry, fault addresses and retained DATA are independent
-- observations, rather than restatements of the fixture definitions.
#eval (show IO Unit from do
  let select : Artifact → IO Program := fun artifact => do
    match Grading.CallStack.Artifact.select artifact with
    | .error error => throw (IO.userError s!"selection failed: {repr error}")
    | .ok selected => pure selected.program
  let check : Program → Word → Word → Word → Word → Word → IO Unit :=
      fun program value count old output stored => do
    unless observe program value count old 64 == some (output, some stored) do
      throw (IO.userError "actual execution violated its independent scalar/DATA observation")
  let gcc ← select gccRaw
  let clang ← select clangRaw
  for program in [gcc, clang] do
    check program 7 0 42 7 42
    check program 7 1 42 8 7
    check program 7 3 42 10 9
    check program 0xfffffffffffffffe 2 42 0 0xffffffffffffffff
  for (program, offset) in [(gcc, 38), (clang, 45)] do
    let helper ← select (.raw program.bytes offset)
    check helper 7 3 42 7 7
    let truncated ← select (.raw (program.bytes.take offset) 0)
    match CallReturn.run (fun _ => false) 64 (Domain.initial truncated 7 1 42) with
    | .error (.inaccessibleInstruction address) =>
      unless address == 0x1000 + BitVec.ofNat 64 offset do
        throw (IO.userError "truncated text faulted away from the actual CALL target")
    | _ => throw (IO.userError "selection manufactured a missing helper")
  let prefixed ← select (.elf prefixedFile 47 2)
  unless prefixed.bytes == [0xc3, 0xff] ++ gcc.bytes && prefixed.entry == 2 do
    throw (IO.userError "whole-window prefix or exact ELF entry was lost")
  check prefixed 7 3 42 10 9
  for candidate in [Grading.CallStack.Artifact.elf prefixedFile 47 0,
      .elf prefixedFile 48 2, .elf (prefixedFile.take 174) 47 2,
      .elf (prefixedFile.set 68 4) 47 2] do
    unless candidate.selectedProgram.isNone do
      throw (IO.userError "incorrect ELF entry, span, backing or permissions admitted")
  check oldTask 7 2 42 8 7
  check storeAndReturn 7 0 42 7 7)

end EDSL.Tests.GradingCallMemoryLoop64Artifact

#print axioms EDSL.Grading.CallMemoryLoop64.Artifact.certify
#print axioms EDSL.Tests.GradingCallMemoryLoop64Artifact.gcc_raw
#print axioms EDSL.Tests.GradingCallMemoryLoop64Artifact.clang_raw
#print axioms EDSL.Tests.GradingCallMemoryLoop64Artifact.raw_semantics
#print axioms EDSL.Tests.GradingCallMemoryLoop64Artifact.raw_owner_resources
#print axioms EDSL.Tests.GradingCallMemoryLoop64Artifact.raw_domain_outputs
#print axioms EDSL.Tests.GradingCallMemoryLoop64Artifact.gcc_zero
#print axioms EDSL.Tests.GradingCallMemoryLoop64Artifact.clang_maximum_count
#print axioms EDSL.Tests.GradingCallMemoryLoop64Artifact.gcc_elf
#print axioms EDSL.Tests.GradingCallMemoryLoop64Artifact.gcc_other_container
#print axioms EDSL.Tests.GradingCallMemoryLoop64Artifact.elf_semantics_and_code
#print axioms EDSL.Tests.GradingCallMemoryLoop64Artifact.prefix_installed
#print axioms EDSL.Tests.GradingCallMemoryLoop64Artifact.old_task_not_count_claim
#print axioms EDSL.Tests.GradingCallMemoryLoop64Artifact.zero_store_not_count_claim
#audit_edsl
