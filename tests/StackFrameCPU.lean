/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.StackFrame.CPU
import EDSL.X86.CodeCheck
import EDSL.Audit

set_option warningAsError true
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

namespace EDSL.Tests.StackFrameCPU
open X86 OS OS.AddressSpace OS.StackFrame

-- Owned synthetic CALL +1; RET; RET. The helper RET must continue at the
-- caller RET, which then loads the separate original full-width return word.
-- Neither stack bytes nor expected return words use a qword encoder.
def loader : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0xe8, readExecute⟩
    | 4097 => some ⟨1, readExecute⟩
    | 4098 | 4099 | 4100 => some ⟨0, readExecute⟩
    | 4101 | 4102 => some ⟨0xc3, readExecute⟩
    | 65544 | 65545 => some ⟨0x44, readOnly⟩
    | 65546 | 65547 | 65548 => some ⟨0, readOnly⟩
    | 65549 => some ⟨0x80, readOnly⟩
    | 65550 | 65551 => some ⟨0xff, readOnly⟩
    | _ => none

def frame : Descriptor :=
  ⟨⟨0, 4096, 65544, 0xffff800000004444, [0xe8,1,0,0,0,0xc3,0xc3], 0, 1⟩, ⟨2, 0⟩, 16⟩

def evolve (shared : Shared) (operation : Ownership.Mutation) : Shared :=
  match Borrowing.mutate shared operation with | .ok (after, _) => after | .error _ => shared

def lend (shared : Shared) (ticket : Ownership.Ticket) (region : Region) : Shared :=
  match Borrowing.readBorrow shared 0 ticket frame.owner region with
  | .ok (after, _) => after | .error _ => shared

def initial : Shared := Borrowing.empty (Ownership.empty loader)
def code : Shared := evolve initial (.adopt 0 ⟨4096, 7⟩)
def caller : Shared := evolve code (.adopt 0 ⟨65544, 8⟩)
def codeLoan : Shared := lend caller ⟨0, 0⟩ ⟨4096, 7⟩
def callerLoan : Shared := lend codeLoan ⟨1, 0⟩ ⟨65544, 8⟩
def seed : Shared := evolve callerLoan (.allocate frame.owner frame.region readWrite)

theorem initialized : Borrowing.WellFormed seed := by
  have history : Borrowing.History initial seed :=
    .next (.mutate (show Borrowing.mutate initial (.adopt 0 ⟨4096, 7⟩) =
      .ok (code, some ⟨0, 0⟩) by rfl))
    (.next (.mutate (show Borrowing.mutate code (.adopt 0 ⟨65544, 8⟩) =
      .ok (caller, some ⟨1, 0⟩) by rfl))
    (.next (.readBorrow (show Borrowing.readBorrow caller 0 ⟨0, 0⟩ frame.owner ⟨4096, 7⟩ =
      .ok (codeLoan, 0) by rfl))
    (.next (.readBorrow (show Borrowing.readBorrow codeLoan 0 ⟨1, 0⟩ frame.owner ⟨65544, 8⟩ =
      .ok (callerLoan, 1) by rfl))
    (.next (.mutate (show Borrowing.mutate callerLoan (.allocate frame.owner frame.region readWrite) =
      .ok (seed, some frame.ticket) by rfl)) .refl))))
  exact history.wellFormed (Borrowing.empty_wellFormed _ (Ownership.empty_wellFormed _))

theorem ready : Contract frame seed := by
  refine ⟨⟨initialized, ?_, ?_, ?_, ?_, by decide, by decide, by decide⟩,
    ⟨⟨1, 0, frame.region⟩, rfl, rfl⟩, by decide, ?_, ?_⟩
  · exact ⟨⟨⟨0, 0⟩, 0, 1, ⟨4096, 7⟩⟩, rfl, rfl, rfl⟩
  · exact ⟨⟨⟨1, 0⟩, 0, 1, ⟨65544, 8⟩⟩, rfl, rfl, rfl⟩
  · exact checkCode_sound _ _ _ (by rfl)
  · rfl
  · intro address slot
    have lower : 65528 ≤ address.toNat := slot.1
    have upper : address.toNat + 8 ≤ 65544 := slot.2
    have choices : address.toNat = 65528 ∨ address.toNat = 65529 ∨ address.toNat = 65530 ∨
        address.toNat = 65531 ∨ address.toNat = 65532 ∨ address.toNat = 65533 ∨
        address.toNat = 65534 ∨ address.toNat = 65535 ∨ address.toNat = 65536 := by omega
    rcases choices with h | h | h | h | h | h | h | h | h
    all_goals
      have same : address = BitVec.ofNat 64 address.toNat := by simp
      rw [same, h]
      exact ⟨⟨1, 0, frame.region⟩, rfl, rfl, rfl, by decide, by decide⟩
  · intro identifier loan live
    by_cases one : identifier = 1
    · subst identifier
      have same : (⟨⟨1, 0⟩, 0, 1, ⟨65544, 8⟩⟩ : Borrowing.Loan) = loan := Option.some.inj live
      subst loan
      decide
    · by_cases zero : identifier = 0
      · subst identifier
        have same : (⟨⟨0, 0⟩, 0, 1, ⟨4096, 7⟩⟩ : Borrowing.Loan) = loan := Option.some.inj live
        subst loan
        decide
      · have missing : seed.loans identifier = none := by
          change (if identifier = 1 then _ else if identifier = 0 then _ else none) = none
          simp [one, zero]
        rw [missing] at live
        cases live

def start : X86.State :=
  ⟨fun r => if r = .rsp then 65544 else if r = .rax then 0x89abcdef01234567 else 0,
    4096, 0x203, toMemory seed.resources.space⟩

theorem startCurrent : Current frame seed start := ⟨ready, rfl⟩

def calledWorld : Shared := evolve seed (.store64 frame.owner frame.ticket 65536 4101)
def called : X86.State := CallReturn.callState start 1 (toMemory calledWorld.resources.space)
def resumed : X86.State := { called.writeRegister .rsp 65544 with rip := 4101 }
def finished : X86.State := { resumed.writeRegister .rsp 65552 with rip := 0xffff800000004444 }

theorem callStep (af : Bool) : CPU.Step frame seed calledWorld start called af ⟨.next called, []⟩ := by
  have stored := (Borrowing.store64_effect (show Borrowing.mutate seed
    (.store64 frame.owner frame.ticket 65536 4101) = .ok (calledWorld, none) by rfl)).machine
  have actual : CallReturn.execute start (.callRelative32 1) af = .ok ⟨.next called, []⟩ :=
    CallReturn.execute_call start 1 af _ (by rfl) stored
  exact ⟨.callRelative32 1, ⟨.next called, []⟩, rfl, actual, rfl, rfl, .call (by decide) (by rfl),
    by intro read member; cases member⟩

theorem internalStep (af : Bool) : CPU.Step frame calledWorld calledWorld called resumed af
    ⟨.next resumed, [⟨.stack,65536,8⟩]⟩ := by
  exact CPU.private_ret_step ((callStep af).current startCurrent) (by decide) (by rfl) (by rfl)

theorem terminalStep (af : Bool) : CPU.Step frame calledWorld calledWorld resumed finished af
    ⟨.returned finished, [⟨.stack,65544,8⟩]⟩ := by
  exact CPU.original_ret_step ((internalStep af).current ((callStep af).current startCurrent)) rfl af rfl

-- This is a real decoded CPU/OS trace, including the internal continuation.
-- It catches premature terminal RET, next-RIP errors, and detached OS stores.
theorem complete (choices : CallReturn.Choices) : CPU.Execution frame choices seed start calledWorld
    ⟨finished, 3, [⟨.stack,65536,8⟩,⟨.stack,65544,8⟩]⟩ :=
  .next (callStep (choices 0))
    (.next (internalStep ((choices.drop 1) 0))
      (.ret (terminalStep (((choices.drop 1).drop 1) 0))))

example (choices : CallReturn.Choices) :
    (CallReturn.run choices 3 start).map
      (fun result => (result.state.rip, result.state.registers .rsp, result.instructions, result.reads)) =
      .ok (0xffff800000004444,65552,3,[⟨.stack,65536,8⟩,⟨.stack,65544,8⟩]) := by
  have actual := CallReturn.runFrom_complete (complete choices).machine (by decide : 3 ≤ 3)
  exact congrArg (Except.map _) actual

-- The caller and code loans survive the CPU writes; no private read introduces
-- a loan. The dirty return word remains in the frame after both RETs.
example (choices : CallReturn.Choices) :
    Current frame calledWorld finished ∧ calledWorld.loans = seed.loans ∧
    calledWorld.nextLoan = seed.nextLoan ∧
    readWord finished.memory 65536 = .ok 4101 ∧
    readWord finished.memory 65544 = .ok 0xffff800000004444 :=
  ⟨(complete choices).current startCurrent, (complete choices).preserves.loans,
    (complete choices).preserves.nextLoan, rfl, rfl⟩

example (choices : CallReturn.Choices) (query : Word) (outside : ¬frame.region.Contains query) :
    calledWorld.resources.space.cells query = seed.resources.space.cells query :=
  (complete choices).preserves.outside query outside

-- A successful owner read at one slot does not freeze the other slot. This
-- actual follow-up mutation would fail if a POP/RET bridge created a loan.
example : Borrowing.loadOwnedWord64 calledWorld frame.owner frame.ticket 65536 = .ok 4101 ∧
    ∃ after, Borrowing.mutate calledWorld
      (.store64 frame.owner frame.ticket 65528 0xfedcba9876543210) = .ok (after, none) := by
  refine ⟨rfl, ?_⟩
  exact current_store64_enabled ((callStep false).current startCurrent) (by decide) _

-- PUSH RSP must save the old RSP, and POP RSP must end at that saved word,
-- rather than old-RSP+8. These independent ISA expectations also pass through
-- the same full-memory owner bridge despite not belonging to the code window.
def pushedWorld : Shared := evolve seed (.store64 frame.owner frame.ticket 65536 65544)
def pushed : X86.State := CallReturn.pushState start false (toMemory pushedWorld.resources.space)
def popped : X86.State := CallReturn.popState pushed .rsp false 65544

example : ∃ evolved, Current frame evolved pushed ∧
    Borrowing.loadOwnedWord64 evolved frame.owner frame.ticket 65536 = .ok 65544 := by
  have stored := (Borrowing.store64_effect (show Borrowing.mutate seed
    (.store64 frame.owner frame.ticket 65536 65544) = .ok (pushedWorld, none) by rfl)).machine
  have actual : CallReturn.execute start (.push64 .rsp false) false = .ok ⟨.next pushed, []⟩ :=
    CallReturn.execute_push start .rsp false false _ stored
  obtain ⟨evolved, success, current, _, _⟩ := CPU.push_current startCurrent (source := .rsp)
    (prefixed := false) (af := false) (by decide) actual
  exact ⟨evolved, current, Borrowing.store64_owned_readback success⟩

example : popped.registers .rsp = 65544 ∧ readWord popped.memory 65536 = .ok 65544 ∧
    Current frame pushedWorld popped := by
  have pushedCurrent : Current frame pushedWorld pushed :=
    ⟨(contract_store64 ready (show Borrowing.mutate seed
      (.store64 frame.owner frame.ticket 65536 65544) = .ok (pushedWorld, none) by rfl)).1, rfl⟩
  exact ⟨rfl, rfl, (CPU.pop_current pushedCurrent (destination := .rsp) (prefixed := false)
    (af := false) (by decide) (show CallReturn.execute pushed (.pop64 .rsp false) false =
      .ok ⟨.next popped, [⟨.stack,65536,8⟩]⟩ by rfl)).1⟩

-- Neighboring readable RAM outside the complete private interval cannot be
-- used for a private RET receipt, even if a raw stack read accepts that word.
example : ¬Slot frame 65544 ∧ ¬ReadAllowed frame seed ⟨.stack,65540,8⟩ := by
  refine ⟨by decide, ?_⟩
  intro allowed
  cases allowed with
  | original original => exact (by decide : (65540 : Word) ≠ frame.call.stack) original.2.1
  | privateSlot _ _ present => exact (by decide : ¬Slot frame 65540) present.fits

end EDSL.Tests.StackFrameCPU

#print axioms EDSL.OS.StackFrame.CPU.call_enabled
#print axioms EDSL.OS.StackFrame.CPU.push_enabled
#print axioms EDSL.OS.StackFrame.CPU.private_ret_step
#print axioms EDSL.OS.StackFrame.CPU.original_ret_step
#print axioms EDSL.OS.StackFrame.CPU.Execution.machine
#print axioms EDSL.OS.StackFrame.CPU.Execution.current
#print axioms EDSL.OS.StackFrame.CPU.Execution.preserves
#print axioms EDSL.Tests.StackFrameCPU.complete
#audit_edsl
