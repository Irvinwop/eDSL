/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallStack.Correctness
import EDSL.X86.CodeCheck
import EDSL.Audit

set_option warningAsError true
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

namespace EDSL.Tests.CallStackAdmission
open X86 OS OS.AddressSpace OS.StackFrame

-- Real whole separate-unit GCC text, with independent literal caller bytes.
def loader : Space where
  cells address := match address.toNat with
    | 4096 => some ⟨0x50, readExecute⟩
    | 4097 => some ⟨0xe8, readExecute⟩
    | 4098 => some ⟨0x05, readExecute⟩
    | 4099 | 4100 | 4101 => some ⟨0, readExecute⟩
    | 4102 => some ⟨0x5a, readExecute⟩
    | 4103 | 4107 => some ⟨0x48, readExecute⟩
    | 4104 => some ⟨0xff, readExecute⟩
    | 4105 => some ⟨0xc0, readExecute⟩
    | 4106 | 4111 => some ⟨0xc3, readExecute⟩
    | 4108 => some ⟨0x8d, readExecute⟩
    | 4109 => some ⟨0x47, readExecute⟩
    | 4110 => some ⟨0x01, readExecute⟩
    | 65544 | 65545 => some ⟨0x44, readOnly⟩
    | 65546 | 65547 | 65548 => some ⟨0, readOnly⟩
    | 65549 => some ⟨0x80, readOnly⟩
    | 65550 | 65551 => some ⟨0xff, readOnly⟩
    | _ => none

def frame : Descriptor :=
  ⟨⟨0, 4096, 65544, 0xffff800000004444, CallStack.Compiler.bytes .gccSeparate, 0, 1⟩, ⟨2, 0⟩, 16⟩

def evolve (shared : Shared) (operation : Ownership.Mutation) : Shared :=
  match Borrowing.mutate shared operation with | .ok (after, _) => after | .error _ => shared

def lend (shared : Shared) (ticket : Ownership.Ticket) (region : Region) : Shared :=
  match Borrowing.readBorrow shared 0 ticket frame.owner region with
  | .ok (after, _) => after | .error _ => shared

def initial : Shared := Borrowing.empty (Ownership.empty loader)
def code : Shared := evolve initial (.adopt 0 ⟨4096, 16⟩)
def caller : Shared := evolve code (.adopt 0 ⟨65544, 8⟩)
def codeLoan : Shared := lend caller ⟨0, 0⟩ ⟨4096, 16⟩
def callerLoan : Shared := lend codeLoan ⟨1, 0⟩ ⟨65544, 8⟩
def seed : Shared := evolve callerLoan (.allocate frame.owner frame.region readWrite)

theorem initialized : Borrowing.WellFormed seed := by
  have history : Borrowing.History initial seed :=
    .next (.mutate (show Borrowing.mutate initial (.adopt 0 ⟨4096, 16⟩) =
      .ok (code, some ⟨0, 0⟩) by rfl))
    (.next (.mutate (show Borrowing.mutate code (.adopt 0 ⟨65544, 8⟩) =
      .ok (caller, some ⟨1, 0⟩) by rfl))
    (.next (.readBorrow (show Borrowing.readBorrow caller 0 ⟨0, 0⟩ frame.owner ⟨4096, 16⟩ =
      .ok (codeLoan, 0) by rfl))
    (.next (.readBorrow (show Borrowing.readBorrow codeLoan 0 ⟨1, 0⟩ frame.owner ⟨65544, 8⟩ =
      .ok (callerLoan, 1) by rfl))
    (.next (.mutate (show Borrowing.mutate callerLoan (.allocate frame.owner frame.region readWrite) =
      .ok (seed, some frame.ticket) by rfl)) .refl))))
  exact history.wellFormed (Borrowing.empty_wellFormed _ (Ownership.empty_wellFormed _))

theorem ready : Contract frame seed := by
  refine ⟨⟨initialized, ?_, ?_, ?_, ?_, by decide, by decide, by decide⟩,
    ⟨⟨1, 0, frame.region⟩, rfl, rfl⟩, by decide, ?_, ?_⟩
  · exact ⟨⟨⟨0, 0⟩, 0, 1, ⟨4096, 16⟩⟩, rfl, rfl, rfl⟩
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
        have same : (⟨⟨0, 0⟩, 0, 1, ⟨4096, 16⟩⟩ : Borrowing.Loan) = loan := Option.some.inj live
        subst loan
        decide
      · have missing : seed.loans identifier = none := by
          change (if identifier = 1 then _ else if identifier = 0 then _ else none) = none
          simp [one, zero]
        rw [missing] at live
        cases live

/-- This state is reached by successful owner/loan operations above, rather
than by assuming an arbitrary well-formed OS endpoint. -/
def resource : CallStack.Resources := ⟨seed, frame, 0xffffffffffffffff⟩
def entry : X86.State :=
  ⟨fun r => if r = .rsp then 65544 else if r = .rdi then 0xffffffffffffffff else 0,
    4096, 0x203, toMemory seed.resources.space⟩

theorem admitted : CallStack.ResourcePre (CallStack.Compiler.program .gccSeparate) resource entry :=
  ⟨⟨ready, rfl⟩, rfl, rfl, by decide, rfl, rfl, by decide, by decide⟩

-- A wrapping full64 input has the independent mathematical answer one. The
-- result CPU is produced by the checked returning execution, not a fixture.
example (choices : CallReturn.Choices) : ∃ evolved, ∃ result : CallReturn.Result,
    CallReturn.run choices 7 entry = .ok result ∧
    CPU.Execution frame choices seed entry evolved result ∧
    result.instructions = 7 ∧ (result.state.registers .rax).toNat = 1 ∧
    result.state.rip = 0xffff800000004444 ∧ result.state.registers .rsp = 65552 := by
  obtain ⟨evolved, result, actual, trace, _, _, post, cost, _⟩ :=
    CallStack.Compiler.evaluated .gccSeparate admitted choices
  exact ⟨evolved, result, actual, trace, cost, post.value, post.returnAddress, post.stackPointer⟩

#print axioms EDSL.Tests.CallStackAdmission.admitted
#audit_edsl
end EDSL.Tests.CallStackAdmission
