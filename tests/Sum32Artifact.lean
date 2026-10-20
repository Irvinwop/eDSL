/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.Artifact
import EDSL.Audit

namespace EDSL.Tests.Sum32Artifact
open X86 Sum32 OS.AddressSpace OS.ArrayResources
set_option maxRecDepth 100000

-- Literal final .text windows from the owned GCC/Clang artifacts. The same
-- discovery/checker handles both, with no compiler identifier as an input.
def compilerBytes : Bool → List Byte
  | false => [0x31, 0xc0, 0x48, 0x85, 0xf6, 0x74, 0x0b, 0x03, 0x07,
      0x48, 0xff, 0xce, 0x48, 0x83, 0xc7, 0x04, 0xeb, 0xf0, 0xc3]
  | true => [0x31, 0xc0, 0x31, 0xc9, 0x48, 0x39, 0xce, 0x74, 0x08,
      0x03, 0x04, 0x8f, 0x48, 0xff, 0xc1, 0xeb, 0xf3, 0xc3]

def compilerPlan : Bool → Sum32.Plan
  | false => ⟨.pointerCount, [⟨0, .xorSelf32 .rax⟩], 2, ⟨5, 11⟩, 7,
      [⟨9, .dec64 .rsi⟩, ⟨12, .addImm64 .rdi 4⟩], ⟨16, 240⟩, 18⟩
  | true => ⟨.index, [⟨0, .xorSelf32 .rax⟩, ⟨2, .xorSelf32 .rcx⟩], 4,
      ⟨7, 8⟩, 9, [⟨12, .inc64 .rcx⟩], ⟨15, 243⟩, 17⟩

theorem compiler_checked (indexed : Bool) :
    Sum32.check (compilerBytes indexed) = some (compilerPlan indexed) := by
  cases indexed <;> decide

def caller (bytes : List Byte) : Space where
  cells address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length then
      (bytes[address.toNat - 4096]?).map fun byte => ⟨byte, readExecute⟩
    else if (⟨65544, 8⟩ : Region).Contains address then
      some ⟨if address = 65545 then 0x20 else 0, readOnly⟩
    else if (⟨131072, 8⟩ : Region).Contains address then
      ([0xff, 0xff, 0xff, 0xff, 2, 0, 0, 0][address.toNat - 131072]?).map
        fun byte => ⟨byte, readOnly⟩
    else none

def codeOwned (indexed : Bool) : OS.Ownership.World :=
  OS.Ownership.install (OS.Ownership.empty (caller (compilerBytes indexed)))
    (caller (compilerBytes indexed)) 7 ⟨4096, (compilerBytes indexed).length⟩

def stackOwned (indexed : Bool) : OS.Ownership.World :=
  OS.Ownership.install (codeOwned indexed) (caller (compilerBytes indexed)) 7 ⟨65544, 8⟩

theorem codeOwned_valid (indexed : Bool) : OS.Ownership.WellFormed (codeOwned indexed) :=
  (OS.Ownership.adopt_wellFormed (OS.Ownership.empty (caller (compilerBytes indexed)))
    7 ⟨4096, (compilerBytes indexed).length⟩
    (codeOwned indexed, ⟨0, 0⟩) (OS.Ownership.empty_wellFormed (caller (compilerBytes indexed)))
      (by cases indexed <;> rfl)).1

theorem stackOwned_valid (indexed : Bool) : OS.Ownership.WellFormed (stackOwned indexed) :=
  (OS.Ownership.adopt_wellFormed _ 7 ⟨65544, 8⟩ (stackOwned indexed, ⟨1, 0⟩)
    (codeOwned_valid indexed) (by cases indexed <;> rfl)).1

def codeHeld (indexed : Bool) : OS.Borrowing.State := OS.Borrowing.installLoan
  (OS.Borrowing.empty (stackOwned indexed))
    ⟨⟨0, 0⟩, 7, 11, ⟨4096, (compilerBytes indexed).length⟩⟩

def emptyHeld (indexed : Bool) : OS.Borrowing.State := OS.Borrowing.installLoan
  (codeHeld indexed) ⟨⟨1, 0⟩, 7, 11, ⟨65544, 8⟩⟩

theorem codeHeld_valid (indexed : Bool) : OS.Borrowing.WellFormed (codeHeld indexed) :=
  (OS.Borrowing.readBorrow_wellFormed _ 7 ⟨0, 0⟩ 11
    ⟨4096, (compilerBytes indexed).length⟩ (codeHeld indexed, 0)
    (OS.Borrowing.empty_wellFormed _ (stackOwned_valid indexed))
    (by cases indexed <;> rfl)).1

theorem emptyHeld_valid (indexed : Bool) : OS.Borrowing.WellFormed (emptyHeld indexed) :=
  (OS.Borrowing.readBorrow_wellFormed _ 7 ⟨1, 0⟩ 11 ⟨65544, 8⟩
    (emptyHeld indexed, 1) (codeHeld_valid indexed) (by cases indexed <;> rfl)).1

def emptyCall (indexed : Bool) (unusedBase : Word) (unusedLoan : Nat) : Call :=
  ⟨10, ⟨0, 1, unusedLoan⟩, 4096, compilerBytes indexed, 65544, unusedBase, [], 8192⟩

theorem code_current (indexed : Bool) :
    CodeAt (toMemory (caller (compilerBytes indexed))) 4096 (compilerBytes indexed) :=
  ELF.checkCode_sound _ _ _ (by cases indexed <;> decide)

theorem empty_contract (indexed : Bool) (unusedBase : Word) (unusedLoan : Nat) :
    Contract (emptyHeld indexed) (emptyCall indexed unusedBase unusedLoan) := by
  refine ⟨emptyHeld_valid indexed, ?_, code_current indexed, ?_, currentArrayAt_nil _ _,
    arrayBound_nil _, ?_, ?_, ?_⟩
  · refine ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · intro nonempty; exact False.elim (nonempty rfl)
    · change OS.Ownership.Disjoint ⟨4096, (compilerBytes indexed).length⟩ ⟨65544, 8⟩
      cases indexed <;> decide
    all_goals intro nonempty; exact False.elim (nonempty rfl)
  · change readWord (toMemory (caller (compilerBytes indexed))) 65544 = .ok 8192
    cases indexed <;> rfl
  · change canonical 8192 = true
    decide
  · change (65544 : Word).toNat + 8 < 2^64
    decide
  · change canonical ((65544 : Word) + 8) = true
    decide

def entry (bytes : List Byte) (base : Word) (count : Nat) : X86.State where
  registers register := match register with
    | .rdi => base | .rsi => BitVec.ofNat 64 count | .rsp => 65544
    | _ => 0xfedcba9876543210
  rip := 4096
  flags := 0xa02
  memory := toMemory (caller bytes)

theorem empty_admission (indexed : Bool) (unusedBase : Word) (unusedLoan : Nat) :
    Admission (emptyHeld indexed) (emptyCall indexed unusedBase unusedLoan)
      (entry (compilerBytes indexed) unusedBase 0) :=
  ⟨empty_contract indexed unusedBase unusedLoan, rfl⟩

def arrayAllocated (indexed : Bool) : OS.Borrowing.State :=
  let before := emptyHeld indexed
  { before with resources := OS.Ownership.install before.resources (caller (compilerBytes indexed)) 7 ⟨131072, 8⟩ }

def arrayHeld (indexed : Bool) : OS.Borrowing.State := OS.Borrowing.installLoan
  (arrayAllocated indexed) ⟨⟨2, 0⟩, 7, 11, ⟨131072, 8⟩⟩

theorem array_history (indexed : Bool) : OS.Borrowing.History (emptyHeld indexed) (arrayHeld indexed) :=
  .next (.mutate (show OS.Borrowing.mutate (emptyHeld indexed)
    (.adopt 7 ⟨131072, 8⟩) = .ok (arrayAllocated indexed, some ⟨2, 0⟩) from
      by cases indexed <;> rfl))
  (.next (.readBorrow (show OS.Borrowing.readBorrow (arrayAllocated indexed)
    7 ⟨2, 0⟩ 11 ⟨131072, 8⟩ = .ok (arrayHeld indexed, 2) from
      by cases indexed <;> rfl)) .refl)

def wrappingCall (indexed : Bool) : Call :=
  { emptyCall indexed 131072 2 with values := [0xffffffff, 2] }

theorem wrapping_contract (indexed : Bool) : Contract (arrayHeld indexed) (wrappingCall indexed) := by
  have prior := (empty_contract indexed 131072 2).frame (array_history indexed)
    ⟨rfl, rfl, fun nonempty => False.elim (nonempty rfl)⟩
  refine ⟨prior.wellFormed, ?_, prior.code, prior.stack, ?_,
    show (131072 : Word).toNat + 4 * 2 ≤ 2^64 by decide,
    prior.returnCanonical, prior.stackBound, prior.postStackCanonical⟩
  · exact ⟨prior.held.code, prior.held.stack, fun _ => ⟨_, rfl, rfl, rfl⟩,
      prior.held.code_stack, fun _ => by
        change OS.Ownership.Disjoint ⟨131072, 8⟩ ⟨4096, (compilerBytes indexed).length⟩
        cases indexed <;> decide, fun _ => by
        change OS.Ownership.Disjoint ⟨131072, 8⟩ ⟨65544, 8⟩
        decide⟩
  · intro index value present
    match index with
    | 0 | 1 => simp [wrappingCall, emptyCall] at present; subst value; cases indexed <;> rfl
    | index + 2 => simp [wrappingCall, emptyCall] at present

theorem wrapping_admission (indexed : Bool) :
    Admission (arrayHeld indexed) (wrappingCall indexed)
      (entry (compilerBytes indexed) 131072 2) :=
  ⟨wrapping_contract indexed, rfl⟩

-- Both native code windows have genuinely admitted executions, with no input
-- loan or pointer condition at n=0. These conclusions include the complete
-- shared Post, current retained resources, and permission for actual reads.
theorem empty_total (indexed : Bool) (unusedBase : Word) (unusedLoan : Nat)
    (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices ((compilerPlan indexed).cost 0)
        (entry (compilerBytes indexed) unusedBase 0) = .ok result ∧
      Post (entry (compilerBytes indexed) unusedBase 0) [] 8192 result.state ∧
      result.state.registers .rax = 0 ∧ result.instructions = (if indexed then 5 else 4) ∧
      result.reads = [⟨.stack, 65544, 8⟩] ∧
      Admission (emptyHeld indexed) (emptyCall indexed unusedBase unusedLoan) result.state ∧
      ∀ read ∈ result.reads, ReadPermission (emptyHeld indexed) 10 read := by
  have correct := Artifact.resource_sound (Sum32.check_sound (compiler_checked indexed))
    (empty_admission indexed unusedBase unusedLoan) rfl rfl rfl rfl
  obtain ⟨result, execution, post, cost, reads, retained, permissions⟩ := correct choices
  refine ⟨result, execution, post, ?_, ?_, reads, retained, permissions⟩
  · exact post.value.trans (by decide : (sum32 []).setWidth 64 = 0)
  · apply cost.trans
    change (compilerPlan indexed).cost 0 = (if indexed then 5 else 4)
    cases indexed <;> decide

-- Modular arithmetic has an independently known result: FFFFFFFF + 2 is 1
-- in uint32, then zero-extended to full RAX. Exactly two array reads occur,
-- with no read at the one-past address; all AF streams satisfy the full Post.
theorem wrapping_total (indexed : Bool) (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices ((compilerPlan indexed).cost 2)
        (entry (compilerBytes indexed) 131072 2) = .ok result ∧
      Post (entry (compilerBytes indexed) 131072 2) [0xffffffff, 2] 8192 result.state ∧
      result.state.registers .rax = 1 ∧ result.instructions = (if indexed then 15 else 16) ∧
      result.reads = [⟨.data, 131072, 4⟩, ⟨.data, 131076, 4⟩, ⟨.stack, 65544, 8⟩] ∧
      Admission (arrayHeld indexed) (wrappingCall indexed) result.state ∧
      ∀ read ∈ result.reads, ReadPermission (arrayHeld indexed) 10 read := by
  have correct := Artifact.resource_sound (Sum32.check_sound (compiler_checked indexed))
    (wrapping_admission indexed) rfl rfl rfl rfl
  obtain ⟨result, execution, post, cost, reads, retained, permissions⟩ := correct choices
  refine ⟨result, execution, post, ?_, ?_, reads, retained, permissions⟩
  · exact post.value.trans (by decide : (sum32 [0xffffffff, 2]).setWidth 64 = 1)
  · apply cost.trans
    cases indexed <;> decide

def windowImage (length : Nat) : ELF.Image := ⟨4096, [⟨0, 4096, length, length, 5, 1⟩]⟩

-- ELF selection stops at a real decoded RET. Raw inputs instead denote their
-- complete supplied window, so unsupported suffixes cannot disappear there.
example (indexed : Bool) :
    Artifact.entryWindow (compilerBytes indexed ++ [0x67])
      (windowImage ((compilerBytes indexed).length + 1)) = .ok (compilerBytes indexed) := by
  cases indexed <;> rfl
example (indexed : Bool) : Sum32.check (compilerBytes indexed ++ [0x67]) = none := by
  cases indexed <;> decide

-- Linear decoding preserves an unsupported boundary even when a JMP would
-- skip it. Discovery never silently selects disjoint byte islands as code.
example : Artifact.entryWindow [0xeb, 1, 0x67, 0xc3] (windowImage 4) =
    .error (.decode 2 (.unsupportedOpcode 0x67)) := by rfl

-- These synthetic candidates stay inside the supported ISA. Each rejection
-- accompanies an independently observable semantic failure, rather than a
-- comparison with a permitted whole-byte profile.
def wrongResult : List Byte := [0xb8, 1, 0, 0, 0] ++ (compilerBytes false).drop 2
def wrongGuard : List Byte := (compilerBytes false).take 4 ++ [0xff] ++ (compilerBytes false).drop 5
def wrongStride : List Byte := (compilerBytes false).take 15 ++ [8] ++ (compilerBytes false).drop 16
def overread : List Byte := (compilerBytes false).take 6 ++ [0] ++ (compilerBytes false).drop 7
def forever : List Byte := [0xeb, 0xfe, 0xc3]

def observation (bytes : List Byte) (base : Word) (count fuel : Nat) :
    Except X86.Error (Word × List Sequential.Read) :=
  (Sequential.run (fun _ => false) fuel (entry bytes base count)).map
    fun result => (result.state.registers .rax, result.reads)

example : Sum32.check wrongResult = none := by decide
example : observation wrongResult 0 0 4 = .ok (1, [⟨.stack, 65544, 8⟩]) := by rfl
example : Sum32.check wrongGuard = none := by decide
example : observation wrongGuard 0x800000000000 0 4 =
    .error (.inaccessibleData 0x800000000000) := by rfl
example : Sum32.check wrongStride = none := by decide
example : observation wrongStride 131072 2 10 = .error (.inaccessibleData 131080) := by rfl
example : Sum32.check overread = none := by decide
example : observation overread 0x800000000000 0 4 =
    .error (.inaccessibleData 0x800000000000) := by rfl
example : Sum32.check forever = none := by decide

-- This is an actual infinite trace of the sequential machine, not a timeout
-- or a bounded execution used to infer nontermination.
theorem forever_diverges : Sequential.Diverges (entry forever 0 0) := by
  refine ⟨fun _ => false, fun _ => entry forever 0 0, rfl, ?_⟩
  intro _
  refine ⟨[], .next (entry forever 0 0), ?_, rfl⟩
  change Sequential.step false (entry forever 0 0) = .ok ⟨.next (entry forever 0 0), []⟩
  rfl

end EDSL.Tests.Sum32Artifact

#audit_edsl
