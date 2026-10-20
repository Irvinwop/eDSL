/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallResources.Domain
import EDSL.Audit

namespace EDSL.Tests.CallResourcesDomain
open X86 OS OS.AddressSpace OS.CallResources

-- The numeric entry deliberately differs from the old Grading.Domain's4096.
-- These are ordinary Clang min bytes; this local fixture is not an ELF binding
-- or a proof of the min function's mathematics.
def bytes : List Byte := [0x48, 0x89, 0xf0, 0x48, 0x39, 0xf7, 0x48, 0x0f, 0x42, 0xc7, 0xc3]
def codeBase : Word := 0x4012e0
def stackBase : Word := 0x700008
def continuation : Word := 0x654321

def supplied : Space where
  cells address :=
    if (⟨codeBase, bytes.length⟩ : Region).Contains address then
      (bytes[address.toNat - codeBase.toNat]?).map fun byte => ⟨byte, readExecute⟩
    else if (⟨stackBase, 8⟩ : Region).Contains address then
      some ⟨continuation.extractLsb' ((address.toNat - stackBase.toNat) * 8) 8, readOnly⟩
    else if address = 0x900001 then some ⟨0xa5, inaccessible⟩
    else none

def declared : Domain.Initial :=
  ⟨supplied, 17, 29, 41, codeBase, bytes, stackBase, continuation⟩

theorem ready : Domain.check declared = true := by decide +kernel

theorem admitted (registers : Register → Word) (flags : Word) :
    Current (Domain.call declared) (Domain.shared declared) (Domain.machine declared registers flags) :=
  Domain.current (Domain.check_sound ready) registers flags

/-- Arbitrary caller registers/flags have an actual usable original caller
loan at this non4096 address. The decoded final RET reads its real eight bytes,
returns to the expected continuation and retains the SAME complete OS world. -/
theorem actual_return (registers : Register → Word) (flags : Word) (af : Bool) :
    let before := { Domain.machine declared registers flags with rip := codeBase + 10 }
    Sequential.step af before = .ok ⟨.returned (returnAfter before continuation),
      [⟨.stack, stackBase, 8⟩]⟩ ∧
    Current (Domain.call declared) (Domain.shared declared) (returnAfter before continuation) ∧
    ReadAllowed (Domain.call declared) (Domain.shared declared) ⟨.stack, stackBase, 8⟩ := by
  let before := { Domain.machine declared registers flags with rip := codeBase + 10 }
  have current : Current (Domain.call declared) (Domain.shared declared) before :=
    (admitted registers flags).sameMemory rfl
  have code : CodeAt (toMemory supplied) codeBase bytes := (Domain.check_sound ready).code
  have decoded : Sequential.decodeAt before = .ok (.legacy .ret) :=
    Sequential.decodeAt_transport
      (Sequential.code_fetch_transport code (by decide) 10 (by decide) before rfl rfl) (by rfl)
  have stack : before.registers .rsp = (Domain.call declared).stack := by rfl
  obtain ⟨executed, retained, allowed, _⟩ := current_ret_step current decoded stack af
  exact ⟨executed, retained, allowed⟩

-- The new registry's loans do not authenticate another worker merely because
-- that worker can observe the same accessible machine memory.
example : Borrowing.authorize (Domain.shared declared) (Threads.principal 42) 1 =
    .error .wrongBorrower := by rfl

-- Disjointness is the ONLY failed condition: these shared bytes are both
-- executable RET code and the exact little-endian canonical return0xc3.
def overlappingSpace : Space where
  cells address :=
    if (⟨codeBase, 8⟩ : Region).Contains address then
      some ⟨if address = codeBase then 0xc3 else 0, readExecute⟩
    else none

def overlap : Domain.Initial :=
  { declared with
    space := overlappingSpace
    bytes := [0xc3]
    stack := codeBase
    returnAddress := 0xc3 }

example : (Domain.codeRegion overlap).valid = true ∧ (Domain.stackRegion overlap).valid = true ∧
    Borrowing.allReadable overlappingSpace (Domain.codeRegion overlap) = true ∧
    Borrowing.allReadable overlappingSpace (Domain.stackRegion overlap) = true ∧
    X86.checkCode (toMemory overlappingSpace) codeBase [0xc3] = true ∧
    Domain.checkStack overlap = true ∧ canonical overlap.returnAddress = true ∧
    overlap.stack.toNat + 8 < 2^64 ∧ canonical (overlap.stack + 8) = true := by decide +kernel

example : Domain.check overlap = false := by decide +kernel
example : ¬Nonempty (Domain.Callable overlap) := by
  intro inhabited
  have accepted := (Domain.nonempty_iff overlap).mp inhabited
  have rejected : Domain.check overlap = false := by decide +kernel
  rw [rejected] at accepted
  contradiction

def missingLast : Space where
  cells address := if address = stackBase + 7 then none else supplied.cells address

def missingCaller : Domain.Initial := { declared with space := missingLast }
example : Domain.check missingCaller = false := by decide +kernel

-- Mere mappedness cannot authorize a readable caller slot.
def unreadableLast : Space where
  cells address := if address = stackBase + 7 then some ⟨0, inaccessible⟩ else supplied.cells address

def unreadableCaller : Domain.Initial := { declared with space := unreadableLast }
example : allMapped unreadableLast (Domain.stackRegion unreadableCaller) = true := by decide +kernel
example : Domain.check unreadableCaller = false := by decide +kernel
example : ¬Nonempty (Domain.Callable unreadableCaller) := by
  intro inhabited
  have accepted := (Domain.nonempty_iff unreadableCaller).mp inhabited
  have rejected : Domain.check unreadableCaller = false := by decide +kernel
  rw [rejected] at accepted
  contradiction

-- Readable byte equality without executable permission is insufficient.
def noExecute : Space where
  cells address :=
    if (Domain.codeRegion declared).Contains address then
      (supplied.cells address).map fun cell => { cell with permissions := readOnly }
    else supplied.cells address

def nonExecutableCode : Domain.Initial := { declared with space := noExecute }
example : Borrowing.allReadable noExecute (Domain.codeRegion nonExecutableCode) = true := by decide +kernel
example : Domain.check nonExecutableCode = false := by decide +kernel

-- The same readable/executable span with a different claimed first opcode
-- cannot establish current exact-code evidence or a current callable domain.
def wrongCode : Domain.Initial := { declared with bytes := 0x49 :: bytes.tail }
example : Domain.check wrongCode = false := by decide +kernel
example : ¬Nonempty (Domain.Callable wrongCode) := by
  intro inhabited
  have accepted := (Domain.nonempty_iff wrongCode).mp inhabited
  have rejected : Domain.check wrongCode = false := by decide +kernel
  rw [rejected] at accepted
  contradiction

-- A live readable caller slot does not justify a different expected return.
def wrongReturn : Domain.Initial := { declared with returnAddress := 0x654322 }
example : Borrowing.allReadable supplied (Domain.stackRegion wrongReturn) = true := by decide +kernel
example : Domain.check wrongReturn = false := by decide +kernel

-- Empty CodeAt alone can be vacuous; a live code allocation/loan cannot be.
def emptyCode : Domain.Initial := { declared with bytes := [] }
example : Domain.check emptyCode = false := by decide +kernel

-- Initialization is intentionally independent of instruction semantics. A
-- mapped UD2 encoding has a modeled resource domain, with no safety/result claim.
def uninterpreted : Domain.Initial :=
  { declared with
    bytes := [0x0f, 0x0b]
    space := { cells := fun address =>
      if address = codeBase then some ⟨0x0f, readExecute⟩
      else if address = codeBase + 1 then some ⟨0x0b, readExecute⟩
      else supplied.cells address } }
example : Nonempty (Domain.Callable uninterpreted) := Domain.checked_nonempty (by decide +kernel)

end EDSL.Tests.CallResourcesDomain

#audit_edsl
