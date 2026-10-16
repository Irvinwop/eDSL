/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordResources64

set_option warningAsError true

namespace EDSL.OS.WordResources64
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS

/-- The original complete caller slot supplies current STACK8 read authority. -/
theorem stackRead_permission {call : Call} {shared : Shared}
    (contract : Contract call shared) :
    ArrayResources.ReadPermission shared call.worker ⟨.stack, call.stack, 8⟩ := by
  obtain ⟨loan, live, borrower, sameRegion⟩ := contract.stackLoan
  refine ⟨call.stackLoan, loan, ?_, ?_⟩
  · simp [Borrowing.authorize, live, borrower]
  · rw [← sameRegion]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- Full current return-slot contents plus the machine's actual RSP binding. -/
structure RetReady (call : Call) (machine : State) : Prop where
  stack : readWord machine.memory (machine.registers .rsp) = .ok call.returnAddress
  returnCanonical : canonical call.returnAddress = true
  stackBound : (machine.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : canonical (machine.registers .rsp + 8) = true

theorem Current.retReady {call : Call} {shared : Shared} {machine : State}
    (current : Current call shared machine) (stack : machine.registers .rsp = call.stack) :
    RetReady call machine := by
  refine ⟨?_, current.contract.returnCanonical, ?_, ?_⟩
  · rw [stack, current.coupled]
    exact current.contract.stack
  · rw [stack]
    exact current.contract.stackBound
  · rw [stack]
    exact current.contract.postStackCanonical

def returnAfter (before : State) (returnAddress : Word) : State :=
  { before.writeRegister .rsp (before.registers .rsp + 8) with rip := returnAddress }

/-- Successful RET follows from the actual current eight retained bytes and
actual RSP = original call.stack; retaining a loan alone does not supply it. -/
theorem current_ret_step {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.legacy .ret))
    (stack : before.registers .rsp = call.stack) (af : Bool) :
    step af before = .ok ⟨.returned (returnAfter before call.returnAddress),
      [⟨.stack, call.stack, 8⟩]⟩ ∧
    Current call shared (returnAfter before call.returnAddress) ∧
    ReadAllowed call shared before ⟨.stack, call.stack, 8⟩ ∧
    OperandReadSucceeds before ⟨.stack, call.stack, 8⟩ := by
  have ready := current.retReady stack
  have loaded : readWord before.memory call.stack = .ok call.returnAddress := by
    rw [← stack]
    exact ready.stack
  refine ⟨?_, ⟨current.contract, current.coupled⟩,
    ⟨rfl, rfl, stackRead_permission current.contract⟩, rfl, call.returnAddress, ?_⟩
  · rw [step_eq_execute af decoded]
    simp [execute, X86.executeInstruction, X86.executeRet, loaded,
      ready.returnCanonical, Sequential.Instruction.operandReads, returnAfter, stack]
  · rw [← stack]
    exact ready.stack

/-- Full owner/epoch and loan metadata, all permissions, and every byte outside
the target are accumulated on the same checked OS history. -/
structure Frame (target : Word) (seed evolved : Shared) : Prop where
  history : Borrowing.History seed evolved
  allocations : evolved.resources.allocations = seed.resources.allocations
  frontier : evolved.resources.frontier = seed.resources.frontier
  loans : evolved.loans = seed.loans
  nextLoan : evolved.nextLoan = seed.nextLoan
  permissions : ∀ query, (evolved.resources.space.cells query).map AddressSpace.Cell.permissions =
    (seed.resources.space.cells query).map AddressSpace.Cell.permissions
  outside : ∀ query, ¬(AddressSpace.qwordRegion target).Contains query →
    evolved.resources.space.cells query = seed.resources.space.cells query

theorem Frame.refl (target : Word) (seed : Shared) : Frame target seed seed :=
  ⟨.refl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem history_trans {a b c : Shared}
    (first : Borrowing.History a b) (last : Borrowing.History b c) : Borrowing.History a c := by
  induction first with
  | refl => exact last
  | next step _ ih => exact .next step (ih last)

theorem Frame.trans {target : Word} {a b c : Shared}
    (first : Frame target a b) (last : Frame target b c) : Frame target a c :=
  ⟨history_trans first.history last.history,
    last.allocations.trans first.allocations, last.frontier.trans first.frontier,
    last.loans.trans first.loans, last.nextLoan.trans first.nextLoan,
    fun query => (last.permissions query).trans (first.permissions query),
    fun query outside => (last.outside query outside).trans (first.outside query outside)⟩

theorem wordEffect_frame {owner ticket target shared before instruction observation evolved}
    (effect : WordEffect owner ticket target shared before instruction observation evolved) :
    Frame target shared evolved := by
  cases effect with
  | readOnly _ => exact Frame.refl _ _
  | store64 _ success =>
    have frame := Borrowing.store64_effect success
    exact ⟨.next (.mutate success) .refl, frame.allocations, frame.frontier,
      frame.loans, frame.nextLoan, frame.permissions, frame.outside⟩

/-- Every surviving loan retains its actual contents throughout the checked
frame, including existing four-byte loans elsewhere in the same world. -/
theorem Frame.loan_contents {target seed evolved} (frame : Frame target seed evolved)
    (valid : Borrowing.WellFormed seed) {identifier loan}
    (live : seed.loans identifier = some loan) :
    ∀ query, loan.region.Contains query →
      evolved.resources.space.cells query = seed.resources.space.cells query := by
  have below := (valid.2 _ _ live).1
  exact (frame.history.loan_stable valid identifier below loan
    ((congrFun frame.loans identifier).trans live)).2

end EDSL.OS.WordResources64
