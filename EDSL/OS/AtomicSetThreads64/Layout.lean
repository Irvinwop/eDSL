/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Atomics64.LogicalMachine
import EDSL.OS.AtomicThreads64.Machine

namespace EDSL.OS.AtomicSetThreads64
open X86 AddressSpace

/-- The supported syntax is a finite literal sequence of strict full64 LOCK
logical instructions, followed by precisely one near RET. -/
def bodyBytes : List Sequential.LogicalOp → List Byte
  | [] => [0xc3]
  | op :: operations => LockedSet64.Instruction.bytes (.logicalRdiRsi op) ++ bodyBytes operations

@[simp] theorem bodyBytes_nil : bodyBytes [] = [0xc3] := rfl
@[simp] theorem bodyBytes_cons (op : Sequential.LogicalOp) (operations) :
    bodyBytes (op :: operations) = [0xf0, 0x48, LockedSet64.logicalOpcode op, 0x37] ++ bodyBytes operations := rfl

@[simp] theorem bodyBytes_length (operations : List Sequential.LogicalOp) :
    (bodyBytes operations).length = 4 * operations.length + 1 := by
  induction operations with
  | nil => rfl
  | cons op operations ih => simp [ih]; omega

/-- Pure syntax recognition; this checker neither executes code nor names a
requested mathematical result. Truncation, trailing bytes, aliases and every
encoding outside the strict profile fail. -/
def checkLayout : List Byte → Option (List Sequential.LogicalOp)
  | [last] => if last = 0xc3 then some [] else none
  | b0 :: b1 :: opcode :: b3 :: rest =>
    if b0 = 0xf0 ∧ b1 = 0x48 ∧ b3 = 0x37 then
      match LockedSet64.decodeLogicalOpcode opcode, checkLayout rest with
      | .ok op, some operations => some (op :: operations)
      | _, _ => none
    else none
  | _ => none

theorem checkLayout_sound {bytes : List Byte} {operations : List Sequential.LogicalOp}
    (checked : checkLayout bytes = some operations) : bytes = bodyBytes operations := by
  match bytes with
  | [last] =>
    simp only [checkLayout] at checked
    split at checked
    · cases checked; simp_all
    · cases checked
  | b0 :: b1 :: opcode :: b3 :: rest =>
    simp only [checkLayout] at checked
    split at checked
    · rename_i headCode
      rcases headCode with ⟨rfl, rfl, rfl⟩
      cases decoded : LockedSet64.decodeLogicalOpcode opcode with
      | error fault => simp [decoded] at checked
      | ok op =>
        cases tail : checkLayout rest with
        | none => simp [decoded, tail] at checked
        | some tailOps =>
          simp only [decoded, tail, Option.some.injEq] at checked
          subst operations
          rw [LockedSet64.decodeLogicalOpcode_code decoded, checkLayout_sound tail]
          rfl
    · cases checked
  | [] | [_ , _] | [_, _, _] => simp_all [checkLayout]
termination_by bytes.length

@[simp] theorem checkLayout_bodyBytes (operations : List Sequential.LogicalOp) :
    checkLayout (bodyBytes operations) = some operations := by
  induction operations with
  | nil => rfl
  | cons op operations ih =>
    simp only [bodyBytes_cons, List.cons_append, List.nil_append, checkLayout]
    simp only [and_self, ↓reduceIte, LockedSet64.decodeLogicalOpcode_of_code, ih]

theorem checkLayout_iff (bytes : List Byte) (operations : List Sequential.LogicalOp) :
    checkLayout bytes = some operations ↔ bytes = bodyBytes operations :=
  ⟨checkLayout_sound, by intro equal; rw [equal]; exact checkLayout_bodyBytes operations⟩

structure Layout (bytes : List Byte) where
  operations : List Sequential.LogicalOp
  exactBytes : bytes = bodyBytes operations

/-- Checks the complete original fetch interval, not adjacent executable bytes. -/
def codeMatches (space : Space) (entry : Word) (bytes : List Byte) : Bool :=
  decide (entry.toNat + bytes.length ≤ 2^64) && (List.range bytes.length).all fun offset =>
    match bytes[offset]? with
    | none => false
    | some byte => Threads.byteMatches (toMemory space) (entry + BitVec.ofNat 64 offset) byte

theorem codeMatches_sound {space : Space} {entry : Word} {bytes : List Byte}
    (checked : codeMatches space entry bytes = true) :
    CodeAt (toMemory space) entry bytes := by
  simp only [codeMatches, Bool.and_eq_true, decide_eq_true_eq] at checked
  refine ⟨checked.1, ?_⟩
  intro offset byte atOffset
  obtain ⟨bound, _⟩ := List.getElem_of_getElem? atOffset
  have matched := List.all_eq_true.mp checked.2 offset (List.mem_range.mpr bound)
  simp only [atOffset] at matched
  exact Threads.byteMatches_sound _ _ _ matched

theorem codeMatches_complete {space : Space} {entry : Word} {bytes : List Byte}
    (code : CodeAt (toMemory space) entry bytes) : codeMatches space entry bytes = true := by
  simp only [codeMatches, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨code.1, List.all_eq_true.mpr ?_⟩
  intro offset member
  have bound := List.mem_range.mp member
  have present : bytes[offset]? = some bytes[offset] := List.getElem?_eq_getElem bound
  simp only [present]
  unfold Threads.byteMatches
  rw [code.2 offset _ present]
  simp

end EDSL.OS.AtomicSetThreads64

namespace EDSL.OS.AtomicSetThreads64
open X86 AddressSpace

/-- Byte cursor and logical cursor agree for every supported finite body. -/
theorem bodyBytes_drop (operations : List Sequential.LogicalOp) (cursor : Nat)
    (bound : cursor ≤ operations.length) :
    (bodyBytes operations).drop (4 * cursor) = bodyBytes (operations.drop cursor) := by
  induction operations generalizing cursor with
  | nil =>
    have zero : cursor = 0 := by simpa using bound
    subst cursor
    rfl
  | cons op operations ih =>
    cases cursor with
    | zero => simp
    | succ cursor =>
      have smaller : cursor ≤ operations.length := by simpa using bound
      change (bodyBytes (op :: operations)).drop (4 * (cursor + 1)) = bodyBytes (operations.drop cursor)
      rw [show 4 * (cursor + 1) = 4 * cursor + 1 + 1 + 1 + 1 by omega]
      simpa only [bodyBytes_cons, List.cons_append, List.nil_append,
        List.drop_succ_cons] using ih cursor smaller

/-- Complete actual logical encoding lies inside the ORIGINAL literal window. -/
theorem bodyBytes_logical_code {memory : Memory} {entry : Word}
    {operations : List Sequential.LogicalOp} (code : CodeAt memory entry (bodyBytes operations))
    {cursor : Nat} {op : Sequential.LogicalOp} (selected : operations[cursor]? = some op) :
    CodeAt memory (entry + BitVec.ofNat 64 (4 * cursor))
      (LockedSet64.Instruction.bytes (.logicalRdiRsi op)) := by
  obtain ⟨cursorBound, same⟩ := List.getElem_of_getElem? selected
  have tail : operations.drop cursor = op :: operations.drop (cursor + 1) := by
    rw [List.drop_eq_getElem_cons cursorBound, same]
  apply code.window (4 * cursor)
  · simp only [LockedSet64.Instruction.bytes, List.length_cons, List.length_nil, bodyBytes_length]
    omega
  · have bound := code.1
    simp only [bodyBytes_length] at bound
    omega
  · intro index byte present
    have indexBound : index < 4 := by
      obtain ⟨bound, _⟩ := List.getElem_of_getElem? present
      exact bound
    rw [← List.getElem?_drop, bodyBytes_drop _ _ (Nat.le_of_lt cursorBound), tail, bodyBytes_cons,
      List.getElem?_append_left indexBound]
    exact present

/-- The single terminal RET is covered even for an empty logical body. -/
theorem bodyBytes_ret_code {memory : Memory} {entry : Word}
    {operations : List Sequential.LogicalOp} (code : CodeAt memory entry (bodyBytes operations)) :
    CodeAt memory (entry + BitVec.ofNat 64 (4 * operations.length))
      (LockedSet64.Instruction.bytes .ret) := by
  apply code.window (4 * operations.length)
  · simp [LockedSet64.Instruction.bytes]
  · have bound := code.1
    simp only [bodyBytes_length] at bound
    omega
  · intro index byte present
    rw [← List.getElem?_drop, bodyBytes_drop _ _ (Nat.le_refl _), List.drop_length]
    exact present

end EDSL.OS.AtomicSetThreads64

namespace EDSL.OS.AtomicSetThreads64

theorem bodyBytes_injective {left right : List X86.Sequential.LogicalOp}
    (equal : bodyBytes left = bodyBytes right) : left = right := by
  have same := congrArg checkLayout equal
  simpa only [checkLayout_bodyBytes, Option.some.injEq] using same

theorem Layout.unique {bytes : List X86.Byte} (left right : Layout bytes) :
    left.operations = right.operations :=
  bodyBytes_injective (left.exactBytes.symm.trans right.exactBytes)

end EDSL.OS.AtomicSetThreads64
