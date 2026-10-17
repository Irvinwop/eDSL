/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.ReadOnlyArithmetic64
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialAddMemory64Resources
open EDSL X86 X86.Sequential OS OS.AddressSpace

-- ADD RDI,[RDI+RDX*8]; ADD RSP,[RDI+RDX*8]; RET. The first
-- destination aliases the base; the second changes the actual return pointer.
private def bytes : List Byte := [0x48,0x03,0x3c,0xd7,0x48,0x03,0x24,0xd7,0xc3]

-- Independent literal bytes, with no qword writer or arithmetic encoder.
-- The two read-only input qwords start at an unaligned address above 4 GiB.
def space : Space where
  cells address := match address.toNat with
    | 4096 | 4100 => some ⟨0x48, readExecute⟩
    | 4097 | 4101 => some ⟨0x03, readExecute⟩
    | 4098 => some ⟨0x3c, readExecute⟩
    | 4099 | 4103 => some ⟨0xd7, readExecute⟩
    | 4102 => some ⟨0x24, readExecute⟩
    | 4104 => some ⟨0xc3, readExecute⟩
    | 65544 => some ⟨0, readOnly⟩
    | 65545 => some ⟨0x20, readOnly⟩
    | 65546 | 65547 | 65548 | 65549 | 65550 | 65551 => some ⟨0, readOnly⟩
    | 0x100000001 => some ⟨0x02, readOnly⟩
    | 0x100000002 | 0x100000003 | 0x100000004 => some ⟨0, readOnly⟩
    | 0x100000005 => some ⟨0x01, readOnly⟩
    | 0x100000006 | 0x100000007 | 0x100000008 => some ⟨0, readOnly⟩
    | 0x100000009 | 0x10000000a | 0x10000000b | 0x10000000c => some ⟨0xff, readOnly⟩
    | 0x10000000d => some ⟨0xfe, readOnly⟩
    | 0x10000000e | 0x10000000f | 0x100000010 => some ⟨0xff, readOnly⟩
    | _ => none

def codeOwned : Ownership.World :=
  Ownership.install (Ownership.empty space) space 7 ⟨4096, 9⟩

def stackOwned : Ownership.World := Ownership.install codeOwned space 7 ⟨65544, 8⟩

theorem codeOwned_valid : Ownership.WellFormed codeOwned :=
  (Ownership.adopt_wellFormed _ 7 ⟨4096, 9⟩ (codeOwned, ⟨0, 0⟩)
    (Ownership.empty_wellFormed space) (by rfl)).1

theorem stackOwned_valid : Ownership.WellFormed stackOwned :=
  (Ownership.adopt_wellFormed _ 7 ⟨65544, 8⟩ (stackOwned, ⟨1, 0⟩)
    codeOwned_valid (by rfl)).1

def codeHeld : Borrowing.State := Borrowing.installLoan (Borrowing.empty stackOwned)
  ⟨⟨0, 0⟩, 7, 11, ⟨4096, 9⟩⟩

def stackHeld : Borrowing.State :=
  Borrowing.installLoan codeHeld ⟨⟨1, 0⟩, 7, 11, ⟨65544, 8⟩⟩

theorem codeHeld_valid : Borrowing.WellFormed codeHeld :=
  (Borrowing.readBorrow_wellFormed _ 7 ⟨0, 0⟩ 11 ⟨4096, 9⟩ (codeHeld, 0)
    (Borrowing.empty_wellFormed _ stackOwned_valid) (by rfl)).1

theorem stackHeld_valid : Borrowing.WellFormed stackHeld :=
  (Borrowing.readBorrow_wellFormed _ 7 ⟨1, 0⟩ 11 ⟨65544, 8⟩ (stackHeld, 1)
    codeHeld_valid (by rfl)).1

def pureCall : CallResources.Call := ⟨10, 4096, 65544, 8192, bytes, 0, 1⟩

theorem pure_admitted : CallResources.Contract pureCall stackHeld := by
  refine ⟨stackHeld_valid, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
    ?_, rfl, by decide, by decide, by decide⟩
  refine ⟨by decide, ?_⟩
  intro index byte present
  match index with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 =>
    simp [pureCall, bytes] at present
    subst byte
    rfl
  | index + 9 => simp [pureCall, bytes] at present

-- These worlds are the results of real adopt/readBorrow operations; the
-- well-formedness proofs above and below check their successful transitions.
def inputAdopted : Borrowing.State :=
  { stackHeld with resources := Ownership.install stackHeld.resources space 7 ⟨0x100000001, 16⟩ }

theorem inputAdopted_valid : Borrowing.WellFormed inputAdopted :=
  Borrowing.mutate_wellFormed _ (.adopt 7 ⟨0x100000001, 16⟩)
    (inputAdopted, some ⟨2, 0⟩) stackHeld_valid (by rfl)

def arrayHeld : Borrowing.State := Borrowing.installLoan inputAdopted
  ⟨⟨2, 0⟩, 7, 11, ⟨0x100000001, 16⟩⟩

theorem arrayHeld_valid : Borrowing.WellFormed arrayHeld :=
  (Borrowing.readBorrow_wellFormed _ 7 ⟨2, 0⟩ 11 ⟨0x100000001, 16⟩
    (arrayHeld, 2) inputAdopted_valid (by rfl)).1

def arrayCall : ArrayResources64.Call :=
  { toCall := pureCall, base := 0x100000001,
    values := [0x0000000100000002, 0xfffffffeffffffff], inputLoan := 2 }

theorem array_admitted : ArrayResources64.Contract arrayCall arrayHeld := by
  refine ⟨?_, ?_, ?_, fun _ => ⟨_, rfl, rfl, rfl⟩⟩
  · exact ⟨arrayHeld_valid, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
      pure_admitted.code, pure_admitted.stack, by decide, by decide, by decide⟩
  · intro index value present
    match index with
    | 0 | 1 => simp [arrayCall] at present; subst value; rfl
    | index + 2 => simp [arrayCall] at present
  · change (0x100000001 : Word).toNat + 8 * 2 ≤ 2^64
    decide

def before : X86.State where
  registers register := if register = .rdi then 0x100000001
    else if register = .rdx then 1 else if register = .rsp then 65544
    else 0x13579bdf2468ace0
  rip := 4096
  flags := 0xa5a5000000000602
  memory := toMemory arrayHeld.resources.space

theorem before_current : ArrayResources64.Current arrayCall arrayHeld before :=
  ⟨array_admitted, rfl⟩

private theorem decoded {call : CallResources.Call} {shared : CallResources.Shared}
    {machine : X86.State} (current : CallResources.Current call shared machine)
    (codeBytes : call.bytes = bytes) (offset : Nat) (inside : offset < bytes.length)
    (pc : machine.rip = call.code + BitVec.ofNat 64 offset)
    {instruction : Sequential.Instruction}
    (literal : Sequential.decodeAt (codeState bytes offset) = .ok instruction) :
    Sequential.decodeAt machine = .ok instruction := by
  have code : CodeAt machine.memory call.code bytes := by
    rw [current.coupled, ← codeBytes]
    exact current.contract.code
  exact decodeAt_transport (code_fetch_transport code (by decide) offset inside machine rfl pc) literal

/-- Reading the OLD indexed address must happen before overwriting its base.
The independent literal sum is zero with CF/PF/AF/ZF set and SF/OF clear. A
32-bit load/add or a post-write address would fail these observations. -/
theorem actual_unaligned_base_alias (af : Bool) :
    ∃ after,
      Sequential.step af before = .ok ⟨.next after, [⟨.data, 0x100000009, 8⟩]⟩ ∧
      after.registers .rdi = 0 ∧ after.registers .rdx = 1 ∧ after.registers .rsp = 65544 ∧
      after.flags = 0xa5a5000000000657 ∧ after.rip = 4100 ∧
      after.memory = before.memory ∧ ArrayResources64.Current arrayCall arrayHeld after ∧
      ArrayResources.ReadPermission arrayHeld 10 ⟨.data, 0x100000009, 8⟩ ∧
      OperandReadSucceeds before ⟨.data, 0x100000009, 8⟩ ∧
      Threads.HasLoan arrayHeld 10 arrayCall.codeLoan ⟨arrayCall.code, arrayCall.bytes.length⟩ ∧
      Threads.HasLoan arrayHeld 10 arrayCall.stackLoan ⟨arrayCall.stack, 8⟩ ∧
      Threads.HasLoan arrayHeld 10 arrayCall.inputLoan arrayCall.inputRegion ∧
      readWord after.memory arrayCall.stack = .ok arrayCall.returnAddress ∧
      Borrowing.loadWord64 arrayHeld 11 arrayCall.inputLoan 0x100000009 = .ok 0xfffffffeffffffff := by
  have effective := ArrayResources64.indexed_address array_admitted .rdi .rdx
    (machine := before) (position := 1) (by decide) rfl rfl
  have decode : Sequential.decodeAt before =
      .ok (.addMem64 .rdi (.indexed .rdi .rdx 3)) := rfl
  obtain ⟨after, actual, current, assigned, other, memory, flags, _, pc, permission, succeeds⟩ :=
    ArrayResources64.current_addMem64_step before_current decode
      (position := 1) (value := 0xfffffffeffffffff) rfl effective.1 af
  refine ⟨after, actual, ?_, other .rdx (by decide), other .rsp (by decide), ?_, pc,
    memory, current, permission, succeeds, current.contract.pureCall.codeLoan,
    current.contract.pureCall.stackLoan, current.contract.input (by decide),
    current.current.2.1, ArrayResources64.element_loadWord64 current.contract (index := 1) rfl⟩
  · exact assigned.trans (by decide)
  · exact flags.trans (by decide)

def rspBefore : X86.State :=
  { before with rip := 4100, registers := fun register =>
      if register = .rdx then 0 else before.registers register }

/-- The named-loan generic bridge changes real RSP, while retaining the same
array world and ORIGINAL caller-slot authority. A following decoded RET uses
the new canonical but unmapped RSP and faults; it cannot reuse that old slot. -/
theorem rsp_add_retains_original_slot_and_ret_faults (afAdd afRet : Bool) :
    ∃ after,
      Sequential.step afAdd rspBefore = .ok ⟨.next after, [⟨.data, 0x100000001, 8⟩]⟩ ∧
      after.registers .rsp = 0x10001000a ∧ canonical (after.registers .rsp) = true ∧
      after.registers .rsp ≠ arrayCall.stack ∧
      ArrayResources64.Current arrayCall arrayHeld after ∧ after.memory = rspBefore.memory ∧
      Threads.HasLoan arrayHeld 10 arrayCall.stackLoan ⟨arrayCall.stack, 8⟩ ∧
      readWord after.memory arrayCall.stack = .ok arrayCall.returnAddress ∧
      (¬CallResources.ReadAllowed pureCall arrayHeld ⟨.stack, after.registers .rsp, 8⟩) ∧
      ArrayResources.ReadPermission arrayHeld 10 ⟨.data, 0x100000001, 8⟩ ∧
      Sequential.step afRet after = .error (.inaccessibleStack 0x10001000a) := by
  have currentBefore : ArrayResources64.Current arrayCall arrayHeld rspBefore := ⟨array_admitted, rfl⟩
  have decode : Sequential.decodeAt rspBefore =
      .ok (.addMem64 .rsp (.indexed .rdi .rdx 3)) := rfl
  have checked : Borrowing.loadWord64 arrayHeld 11 arrayCall.inputLoan
      ((Address.indexed .rdi .rdx 3).eval rspBefore) = .ok 0x100000002 :=
    ArrayResources64.element_loadWord64 array_admitted (index := 0) rfl
  obtain ⟨after, actual, _, assigned, _, memory, _, _, pc, _, permission, _, _⟩ :=
    CallResources.current_addMem64_step currentBefore.pureCall decode checked afAdd
  have rsp : after.registers .rsp = 0x10001000a := assigned.trans (by decide)
  have current : ArrayResources64.Current arrayCall arrayHeld after := currentBefore.sameMemory memory
  have atRet : after.rip = arrayCall.code + 8 := pc
  have retDecoded := decoded current.pureCall rfl 8 (by decide) atRet
    (instruction := .legacy .ret) rfl
  have failed : readWord after.memory 0x10001000a = .error (.inaccessibleStack 0x10001000a) := by
    rw [memory]
    rfl
  refine ⟨after, actual, rsp, ?_, ?_, current, memory, current.contract.pureCall.stackLoan,
    current.current.2.1, ?_, permission, ?_⟩
  · rw [rsp]; decide
  · rw [rsp]; decide
  · intro allowed
    have bound := allowed.2.1
    rw [rsp] at bound
    exact (by decide : (0x10001000a : Word) ≠ pureCall.stack) bound
  · rw [step_eq_execute afRet retDecoded]
    simp only [execute, X86.executeInstruction, X86.executeRet, rsp, failed, error_bind]

-- Both input and caller-slot handles use live loan 1 for this compatible
-- read-only alias. No allocation/region/loan-ID disjointness is warranted.
def stackAlias : ArrayResources64.Call :=
  { toCall := pureCall, base := 65544, values := [8192], inputLoan := 1 }

theorem stackAlias_admitted : ArrayResources64.Contract stackAlias stackHeld := by
  refine ⟨pure_admitted, ?_, ?_, fun _ => ⟨_, rfl, rfl, rfl⟩⟩
  · intro index value present
    cases index with
    | zero => simp [stackAlias] at present; subst value; rfl
    | succ index => simp [stackAlias] at present
  · change (65544 : Word).toNat + 8 * 1 ≤ 2^64
    decide

def aliasBefore : X86.State :=
  { before with registers := fun register => if register = .rdi then 65544
      else if register = .rdx then 0 else before.registers register }

/-- A real ADD may read the caller-slot qword as input through that same live
loan. Both input and the original return slot remain available afterward. -/
theorem compatible_alias_uses_caller_loan (af : Bool) :
    ∃ after,
      Sequential.step af aliasBefore = .ok ⟨.next after, [⟨.data, 65544, 8⟩]⟩ ∧
      after.registers .rdi = 73736 ∧ after.registers .rsp = 65544 ∧
      ArrayResources64.Current stackAlias stackHeld after ∧ after.memory = aliasBefore.memory ∧
      ArrayResources.ReadPermission stackHeld 10 ⟨.data, 65544, 8⟩ ∧
      Borrowing.loadWord64 stackHeld 11 stackAlias.stackLoan 65544 = .ok 8192 ∧
      readWord after.memory stackAlias.stack = .ok stackAlias.returnAddress := by
  have currentBefore : ArrayResources64.Current stackAlias stackHeld aliasBefore :=
    ⟨stackAlias_admitted, rfl⟩
  have decode : Sequential.decodeAt aliasBefore =
      .ok (.addMem64 .rdi (.indexed .rdi .rdx 3)) := rfl
  obtain ⟨after, actual, current, assigned, other, memory, _, _, _, permission, _⟩ :=
    ArrayResources64.current_addMem64_step currentBefore decode (position := 0)
      (value := 8192) rfl rfl af
  exact ⟨after, actual, assigned.trans (by decide), other .rsp (by decide), current, memory,
    permission, ArrayResources64.element_loadWord64 current.contract (index := 0) rfl,
    current.current.2.1⟩

private theorem missing_input_permission :
    ¬ArrayResources.ReadPermission inputAdopted 10 ⟨.data, 0x100000009, 8⟩ := by
  rintro ⟨identifier, loan, authorized, fits⟩
  have live := (Borrowing.authorize_ok _ _ _ _ authorized).1
  have below := (inputAdopted_valid.2 _ _ live).1
  change identifier < 2 at below
  have alternatives : identifier = 0 ∨ identifier = 1 := by omega
  rcases alternatives with rfl | rfl
  · have regions := congrArg (Option.map Borrowing.Loan.region) live
    change some (⟨4096, 9⟩ : Region) = some loan.region at regions
    rw [← Option.some.inj regions] at fits
    exact (by decide : ¬Borrowing.Subregion ⟨(0x100000009 : Word), 8⟩ ⟨4096, 9⟩) fits
  · have regions := congrArg (Option.map Borrowing.Loan.region) live
    change some (⟨65544, 8⟩ : Region) = some loan.region at regions
    rw [← Option.some.inj regions] at fits
    exact (by decide : ¬Borrowing.Subregion ⟨(0x100000009 : Word), 8⟩ ⟨65544, 8⟩) fits

private theorem wrong_borrower_permission :
    ¬ArrayResources.ReadPermission arrayHeld 11 ⟨.data, 0x100000009, 8⟩ := by
  rintro ⟨identifier, loan, authorized, _⟩
  obtain ⟨live, borrower⟩ := Borrowing.authorize_ok _ _ _ _ authorized
  have below := (arrayHeld_valid.2 _ _ live).1
  change identifier < 3 at below
  have alternatives : identifier = 0 ∨ identifier = 1 ∨ identifier = 2 := by omega
  rcases alternatives with rfl | rfl | rfl
  all_goals
    have borrowers := congrArg (Option.map Borrowing.Loan.borrower) live
    change some 11 = some loan.borrower at borrowers
    have impossible : 11 = 12 := (Option.some.inj borrowers).trans borrower
    omega

/-- The very same decoded DATA8 succeeds on CPU RAM when no input loan exists.
Neither decoding, full readability, an unrelated loan ID, nor another borrower
can authorize the bridge's checked read at its actual observed address. -/
theorem raw_success_does_not_supply_resource_authority (af : Bool) :
    ∃ after,
      CallResources.Current pureCall inputAdopted before ∧
      Sequential.step af before = .ok ⟨.next after, [⟨.data, 0x100000009, 8⟩]⟩ ∧
      loadQWord before.memory 0x100000009 = .ok 0xfffffffeffffffff ∧
      Borrowing.loadWord64 inputAdopted 11 2 0x100000009 = .error (.authority .missingLoan) ∧
      Borrowing.loadWord64 arrayHeld 11 1 0x100000009 = .error .outsideLoan ∧
      Borrowing.loadWord64 arrayHeld 12 2 0x100000009 = .error (.authority .wrongBorrower) ∧
      (¬ArrayResources.ReadPermission inputAdopted 10 ⟨.data, 0x100000009, 8⟩) ∧
      (¬ArrayResources.ReadPermission arrayHeld 11 ⟨.data, 0x100000009, 8⟩) := by
  obtain ⟨after, actual, _⟩ := actual_unaligned_base_alias af
  have current : CallResources.Current pureCall inputAdopted before := by
    refine ⟨?_, rfl⟩
    exact ⟨inputAdopted_valid, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
      pure_admitted.code, pure_admitted.stack, by decide, by decide, by decide⟩
  exact ⟨after, current, actual, rfl, rfl, rfl, rfl,
    missing_input_permission, wrong_borrower_permission⟩

end EDSL.Tests.SequentialAddMemory64Resources

#print axioms EDSL.OS.CallResources.addMem64_enabled
#print axioms EDSL.OS.CallResources.current_addMem64_step
#print axioms EDSL.OS.ArrayResources64.addMem64_enabled
#print axioms EDSL.OS.ArrayResources64.current_addMem64_step
#print axioms EDSL.Tests.SequentialAddMemory64Resources.actual_unaligned_base_alias
#print axioms EDSL.Tests.SequentialAddMemory64Resources.rsp_add_retains_original_slot_and_ret_faults
#print axioms EDSL.Tests.SequentialAddMemory64Resources.compatible_alias_uses_caller_loan
#print axioms EDSL.Tests.SequentialAddMemory64Resources.raw_success_does_not_supply_resource_authority

#audit_edsl
