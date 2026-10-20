/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.ArrayResources64
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.ArrayResources64
open X86 OS.AddressSpace OS.ArrayResources64

-- Literal bytes are independent of the qword writer. The input is unaligned,
-- above 4 GiB, read-only, and has a readable byte beyond the exact input loan.
-- The false variant has only code and the original complete caller slot.
def space (withInput : Bool) : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0x48, readExecute⟩
    | 4097 => some ⟨0x8b, readExecute⟩
    | 4098 => some ⟨0x3c, readExecute⟩
    | 4099 => some ⟨0xd7, readExecute⟩
    | 4100 => some ⟨0xc3, readExecute⟩
    | 65544 => some ⟨0, readOnly⟩
    | 65545 => some ⟨0x20, readOnly⟩
    | 65546 | 65547 | 65548 | 65549 | 65550 | 65551 => some ⟨0, readOnly⟩
    | _ => if withInput then
        match address.toNat with
        | 0x100000001 => some ⟨0x10, readOnly⟩
        | 0x100000002 => some ⟨0x32, readOnly⟩
        | 0x100000003 => some ⟨0x54, readOnly⟩
        | 0x100000004 => some ⟨0x76, readOnly⟩
        | 0x100000005 => some ⟨0x98, readOnly⟩
        | 0x100000006 => some ⟨0xba, readOnly⟩
        | 0x100000007 => some ⟨0xdc, readOnly⟩
        | 0x100000008 => some ⟨0xfe, readOnly⟩
        | 0x100000009 => some ⟨0xef, readOnly⟩
        | 0x10000000a => some ⟨0xcd, readOnly⟩
        | 0x10000000b => some ⟨0xab, readOnly⟩
        | 0x10000000c => some ⟨0x89, readOnly⟩
        | 0x10000000d => some ⟨0x67, readOnly⟩
        | 0x10000000e => some ⟨0x45, readOnly⟩
        | 0x10000000f => some ⟨0x23, readOnly⟩
        | 0x100000010 => some ⟨0x01, readOnly⟩
        | 0x100000011 => some ⟨0x5a, readOnly⟩
        | _ => none
      else none

def codeOwned (withInput : Bool) : OS.Ownership.World :=
  OS.Ownership.install (OS.Ownership.empty (space withInput)) (space withInput) 7 ⟨4096, 5⟩

def stackOwned (withInput : Bool) : OS.Ownership.World :=
  OS.Ownership.install (codeOwned withInput) (space withInput) 7 ⟨65544, 8⟩

theorem codeOwned_valid (withInput : Bool) : OS.Ownership.WellFormed (codeOwned withInput) :=
  (OS.Ownership.adopt_wellFormed (OS.Ownership.empty (space withInput)) 7 ⟨4096, 5⟩ (codeOwned withInput, ⟨0, 0⟩)
    (OS.Ownership.empty_wellFormed _) (by rfl)).1

theorem stackOwned_valid (withInput : Bool) : OS.Ownership.WellFormed (stackOwned withInput) :=
  (OS.Ownership.adopt_wellFormed _ 7 ⟨65544, 8⟩ (stackOwned withInput, ⟨1, 0⟩)
    (codeOwned_valid withInput) (by rfl)).1

def codeHeld (withInput : Bool) : OS.Borrowing.State :=
  OS.Borrowing.installLoan (OS.Borrowing.empty (stackOwned withInput))
    ⟨⟨0, 0⟩, 7, 11, ⟨4096, 5⟩⟩

def stackHeld (withInput : Bool) : OS.Borrowing.State :=
  OS.Borrowing.installLoan (codeHeld withInput) ⟨⟨1, 0⟩, 7, 11, ⟨65544, 8⟩⟩

theorem codeHeld_valid (withInput : Bool) : OS.Borrowing.WellFormed (codeHeld withInput) :=
  (OS.Borrowing.readBorrow_wellFormed _ 7 ⟨0, 0⟩ 11 ⟨4096, 5⟩ (codeHeld withInput, 0)
    (OS.Borrowing.empty_wellFormed _ (stackOwned_valid withInput)) (by rfl)).1

theorem stackHeld_valid (withInput : Bool) : OS.Borrowing.WellFormed (stackHeld withInput) :=
  (OS.Borrowing.readBorrow_wellFormed _ 7 ⟨1, 0⟩ 11 ⟨65544, 8⟩ (stackHeld withInput, 1)
    (codeHeld_valid withInput) (by rfl)).1

def pureCall : OS.CallResources.Call :=
  ⟨10, 4096, 65544, 8192, [0x48, 0x8b, 0x3c, 0xd7, 0xc3], 0, 1⟩

theorem pure_admitted (withInput : Bool) : OS.CallResources.Contract pureCall (stackHeld withInput) := by
  refine ⟨stackHeld_valid withInput, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
    ?_, ?_, by decide, by decide, by decide⟩
  · refine ⟨by decide, ?_⟩
    intro index byte present
    match index with
    | 0 | 1 | 2 | 3 | 4 => simp [pureCall] at present; subst byte; rfl
    | index + 5 => simp [pureCall] at present
  · rfl

def emptyCall (unusedBase : Word) (unusedLoan : Nat) : Call :=
  { toCall := pureCall, base := unusedBase, values := [], inputLoan := unusedLoan }

-- No input mapping, allocation or loan is installed. This universal admission
-- includes absent/aliased IDs and noncanonical or unaligned unused pointers.
theorem every_unused_pointer_admitted (unusedBase : Word) (unusedLoan : Nat) :
    Contract (emptyCall unusedBase unusedLoan) (stackHeld false) :=
  Contract.of_nil (pure_admitted false) rfl

-- A compatible read-only alias may reuse both the region and the loan ID.
-- Copying the old array32 disjointness restrictions would reject this call.
def stackAlias : Call :=
  { toCall := pureCall, base := 65544, values := [8192], inputLoan := 1 }

theorem readonly_stack_alias_admitted : Contract stackAlias (stackHeld false) := by
  refine ⟨pure_admitted false, ?_, ?_, fun _ => ⟨_, rfl, rfl, rfl⟩⟩
  · intro index value present
    cases index with
    | zero => simp [stackAlias] at present; subst value; rfl
    | succ index => simp [stackAlias] at present
  · change (65544 : Word).toNat + 8 * 1 ≤ 2^64
    decide

def inputAdopted : OS.Borrowing.State :=
  { (stackHeld true) with
    resources := OS.Ownership.install ((stackHeld true).resources)
      (space true) 7 ⟨0x100000001, 17⟩ }

theorem inputAdopted_valid : OS.Borrowing.WellFormed inputAdopted :=
  OS.Borrowing.mutate_wellFormed _ (.adopt 7 ⟨0x100000001, 17⟩)
    (inputAdopted, some ⟨2, 0⟩) (stackHeld_valid true) (by rfl)

def arrayHeld : OS.Borrowing.State := OS.Borrowing.installLoan inputAdopted
  ⟨⟨2, 0⟩, 7, 11, ⟨0x100000001, 16⟩⟩

theorem arrayHeld_valid : OS.Borrowing.WellFormed arrayHeld :=
  (OS.Borrowing.readBorrow_wellFormed _ 7 ⟨2, 0⟩ 11 ⟨0x100000001, 16⟩
    (arrayHeld, 2) inputAdopted_valid (by rfl)).1

def arrayCall : Call :=
  { toCall := pureCall, base := 0x100000001,
    values := [0xfedcba9876543210, 0x0123456789abcdef], inputLoan := 2 }

theorem array_admitted : Contract arrayCall arrayHeld := by
  refine ⟨?_, ?_, ?_, fun _ => ⟨_, rfl, rfl, rfl⟩⟩
  · exact ⟨arrayHeld_valid, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
      (pure_admitted true).code, (pure_admitted true).stack,
      by decide, by decide, by decide⟩
  · intro index value present
    match index with
    | 0 | 1 => simp [arrayCall] at present; subst value; rfl
    | index + 2 => simp [arrayCall] at present
  · change (0x100000001 : Word).toNat + 8 * 2 ≤ 2^64
    decide

-- Dropping an element must advance eight bytes and retain the high half.
example : loadQWord (toMemory arrayHeld.resources.space) 0x100000009 =
    .ok 0x0123456789abcdef := by
  simpa [arrayCall] using (array_admitted.array.drop 1).head

example : arrayCall.inputRegion.Contains 0x100000010 ∧ canonical 0x100000010 = true := by
  simpa [arrayCall] using element_bytes array_admitted (index := 1) (offset := 7)
    (by decide) (by decide)

-- Readable RAM does not enlarge the exact sixteen-byte input authority.
example : loadQWord (toMemory arrayHeld.resources.space) 0x10000000a =
      .ok 0x5a0123456789abcd ∧
    OS.Borrowing.loadWord64 arrayHeld 11 2 0x10000000a = .error .outsideLoan := by
  exact ⟨rfl, rfl⟩

def before : X86.State where
  registers register := if register = .rdi then 0x100000001
    else if register = .rdx then 1 else if register = .rsp then 65544
    else 0xa5a5a5a5deadbeef
  rip := 4096
  flags := 0xfedcba9876543210
  memory := toMemory arrayHeld.resources.space

theorem before_current : Current arrayCall arrayHeld before := ⟨array_admitted, rfl⟩

-- The literal SIB load overwrites its base register. Its observation must use
-- the old full-width base, index one and scale eight, in the same OS world.
theorem actual_indexed_alias_load (af : Bool) :
    ∃ after,
      Sequential.step af before = .ok ⟨.next after, [⟨.data, 0x100000009, 8⟩]⟩ ∧
      after.registers .rdi = 0x0123456789abcdef ∧ after.registers .rdx = 1 ∧
      after.flags = 0xfedcba9876543210 ∧ after.rip = 4100 ∧
      after.memory = before.memory ∧ Current arrayCall arrayHeld after ∧
      OS.ArrayResources.ReadPermission arrayHeld 10 ⟨.data, 0x100000009, 8⟩ ∧
      Sequential.OperandReadSucceeds before ⟨.data, 0x100000009, 8⟩ := by
  have address := indexed_address array_admitted .rdi .rdx (position := 1)
    (machine := before) (by decide) rfl rfl
  have decoded : Sequential.decodeAt before =
      .ok (.loadMem64 .rdi (.indexed .rdi .rdx 3)) := by rfl
  obtain ⟨after, actual, current, assigned, other, memory, flags, pc, permission, succeeds⟩ :=
    current_loadMem64_step before_current decoded (position := 1)
      (value := 0x0123456789abcdef) rfl address.1 af
  exact ⟨after, actual, assigned, other .rdx (by decide), flags, pc,
    memory, current, permission, succeeds⟩

-- Truncating this index to 32 bits would incorrectly read the mapped second
-- qword. The literal SIB instead uses all 64 bits and faults at the full
-- effective address 0x100000001 + 8 * 0x100000001.
def highIndex : X86.State :=
  { before with registers := fun register =>
      if register = .rdx then 0x100000001 else before.registers register }

theorem high_index_is_not_truncated (af : Bool) :
    Sequential.step af highIndex = .error (.inaccessibleData 0x900000009) := by
  rfl

-- Code, stack and both qwords still agree. Changing only an unrelated RAM
-- permission must nevertheless violate complete current coupling.
def differentPermission : X86.State :=
  { before with memory := { before.memory with writable := fun address =>
      if address = 196608 then true else before.memory.writable address } }

example : ¬Current arrayCall arrayHeld differentPermission := by
  intro current
  have same := congrArg (fun memory : Memory => memory.writable 196608) current.coupled
  change true = false at same
  cases same

-- Omitting only the final byte invalidates the complete second qword.
def missingLast : OS.Borrowing.State :=
  { arrayHeld with resources := { arrayHeld.resources with space :=
      ⟨fun address => if address = 0x100000010 then none
        else arrayHeld.resources.space.cells address⟩ } }

example : ¬Contract arrayCall missingLast := by
  intro contract
  have read := contract.array 1 0x0123456789abcdef rfl
  have failed : loadQWord (toMemory missingLast.resources.space) 0x100000009 =
      .error (.inaccessibleData 0x100000010) := by rfl
  change loadQWord (toMemory missingLast.resources.space) 0x100000009 =
    .ok 0x0123456789abcdef at read
  rw [failed] at read
  cases read

-- A complete final qword may end exactly at 2^64, but not one byte later.
example : ArrayBound64 0xfffffffffffffff8 [1] ∧
    ¬ArrayBound64 0xfffffffffffffff9 [1] := by
  unfold ArrayBound64
  decide

end EDSL.Tests.ArrayResources64

#print axioms EDSL.Tests.ArrayResources64.every_unused_pointer_admitted
#print axioms EDSL.Tests.ArrayResources64.readonly_stack_alias_admitted
#print axioms EDSL.Tests.ArrayResources64.actual_indexed_alias_load
#print axioms EDSL.Tests.ArrayResources64.high_index_is_not_truncated

#audit_edsl
