/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Known
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.GradingTask
open X86 X86.Sequential Grading

-- Exercise the trusted expected type at literal candidate bytes, including
-- BOTH registered loop tasks. No task, postcondition, or premise is supplied.
theorem pair_claim : Claim .pair32
    [0x31, 0xc0, 0x48, 0x85, 0xf6, 0x74, 0x0b,
     0x03, 0x07, 0x48, 0xff, 0xce, 0x48, 0x83, 0xc7, 0x04, 0xeb, 0xf0,
     0x48, 0x85, 0xc9, 0x74, 0x0b, 0x03, 0x02, 0x48, 0xff, 0xc9,
     0x48, 0x83, 0xc2, 0x04, 0xeb, 0xf0, 0xc3] := Known.pair

theorem stride_claim : Claim .stride32
    [0x31, 0xc0, 0x48, 0x85, 0xf6, 0x74, 0x0b,
     0x03, 0x07, 0x48, 0xff, 0xce, 0x48, 0x83, 0xc7, 0x08, 0xeb, 0xf0, 0xc3] := Known.stride

-- Independent current witnesses inhabit the registered raw Pre even when
-- actual execution faults. Refute totality even with the weakest Post=True.
theorem unsupported_pair : ∃ input initial,
    pairTask.useful input ∧ pairTask.pre [0xff] input initial ∧
      ¬AllExecutions initial (fun _ => True) := by
  refine ⟨⟨Domain.valuesA, Domain.valuesB, 8192⟩, Domain.pairEntry [0xff],
    ⟨by decide, by decide⟩, Domain.pair_raw_pre _ (by decide), ?_⟩
  intro total
  have fault : Sequential.run (fun _ => false) 1 (Domain.pairEntry [0xff]) =
      .error (.unsupportedOpcode 0xff) := rfl
  have impossible := total.no_fault_prefix (fun _ => false) fault
  cases impossible

theorem unsupported_stride : ∃ input initial,
    strideTask.useful input ∧ strideTask.pre [0xff] input initial ∧
      ¬AllExecutions initial (fun _ => True) := by
  refine ⟨⟨Domain.valuesA, 2, 8192⟩, Domain.strideEntry [0xff],
    (by change 0 < 2; decide), Domain.stride_raw_pre _ (by decide), ?_⟩
  intro total
  have fault : Sequential.run (fun _ => false) 1 (Domain.strideEntry [0xff]) =
      .error (.unsupportedOpcode 0xff) := rfl
  have impossible := total.no_fault_prefix (fun _ => false) fault
  cases impossible

theorem unsupported_pair_claim : ¬Claim .pair32 [0xff] := by
  intro claim
  obtain ⟨input, initial, _, pre, notTotal⟩ := unsupported_pair
  apply notTotal
  intro choices
  obtain ⟨result, execution, _⟩ := (claim.1.machine input initial pre).1 choices
  exact ⟨result, execution, trivial⟩

theorem unsupported_stride_claim : ¬Claim .stride32 [0xff] := by
  intro claim
  obtain ⟨input, initial, _, pre, notTotal⟩ := unsupported_stride
  apply notTotal
  intro choices
  obtain ⟨result, execution, _⟩ := (claim.1.machine input initial pre).1 choices
  exact ⟨result, execution, trivial⟩

-- Rebind private context while retaining the independent witness's full RAM.
-- These adapters require no copies of the domain's current OS worlds.
private def abi (initial : State) (a b : OS.ArrayResources.Call) : State :=
  { initial with
    rip := a.code
    registers := fun register => match register with
      | .rdi => a.base
      | .rsi => BitVec.ofNat 64 a.values.length
      | .rdx => b.base
      | .rcx => BitVec.ofNat 64 b.values.length
      | .rsp => a.stack
      | _ => initial.registers register }

-- A and B share both base and input loan ID. Adding input/input separation or
-- distinct IDs to resourcePre would reject this currently admitted case.
theorem same_loan_alias {bytes : List Byte} (witness : Domain.PairWitness bytes) :
    ∃ initial, pairTask.resourcePre bytes ⟨witness.shared, witness.callA, witness.callA⟩ initial := by
  let initial := abi witness.initial witness.callA witness.callA
  have admitted : OS.ArrayResources.Admission witness.shared witness.callA initial :=
    witness.admitted.admittedA.unchangedMemory rfl
  exact ⟨initial, witness.code, ⟨admitted, admitted, .refl _⟩,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

private def emptyCall (call : OS.ArrayResources.Call) (base : Word) (identifier : Nat) :
    OS.ArrayResources.Call :=
  { call with base := base, values := [], loans := { call.loans with input := identifier } }

private theorem empty_contract {shared : OS.Borrowing.State} {call : OS.ArrayResources.Call}
    (contract : OS.ArrayResources.Contract shared call) (base : Word) (identifier : Nat) :
    OS.ArrayResources.Contract shared (emptyCall call base identifier) := by
  refine ⟨contract.wellFormed, ?_, contract.code, contract.stack,
    OS.ArrayResources.currentArrayAt_nil _ _, OS.ArrayResources.arrayBound_nil _, contract.returnCanonical,
    contract.stackBound, contract.postStackCanonical⟩
  refine ⟨contract.held.code, contract.held.stack, ?_, contract.held.code_stack, ?_, ?_⟩
  all_goals intro nonempty; exact False.elim (nonempty rfl)

-- Arbitrary unused pointers and absent/aliased input IDs remain admissible;
-- current code, stack, and complete RAM coupling still have to be proved.
theorem pair_empty {bytes : List Byte} (witness : Domain.PairWitness bytes)
    (baseA baseB : Word) (loanA loanB : Nat) :
    ∃ initial, pairTask.resourcePre bytes
      ⟨witness.shared, emptyCall witness.callA baseA loanA, emptyCall witness.callB baseB loanB⟩ initial := by
  let a := emptyCall witness.callA baseA loanA
  let b := emptyCall witness.callB baseB loanB
  let initial := abi witness.initial a b
  have admittedA : OS.ArrayResources.Admission witness.shared a initial :=
    ⟨empty_contract witness.admitted.admittedA.resources baseA loanA, witness.admitted.admittedA.coupled⟩
  have admittedB : OS.ArrayResources.Admission witness.shared b initial :=
    ⟨empty_contract witness.admitted.admittedB.resources baseB loanB, witness.admitted.admittedB.coupled⟩
  have compatible : Pair32.CallCompatibility a b :=
    ⟨witness.admitted.compatible.worker, witness.admitted.compatible.code,
      witness.admitted.compatible.bytes, witness.admitted.compatible.stack,
      witness.admitted.compatible.target⟩
  exact ⟨initial, witness.code, ⟨admittedA, admittedB, compatible⟩,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem stride_empty {bytes : List Byte} (witness : Domain.StrideWitness bytes)
    (base : Word) (loan : Nat) :
    ∃ initial, strideTask.resourcePre bytes ⟨witness.shared, emptyCall witness.call base loan, 0⟩ initial := by
  let call := emptyCall witness.call base loan
  let initial := abi witness.initial call call
  have admitted : OS.ArrayResources.Admission witness.shared call initial :=
    ⟨empty_contract witness.admitted.resources base loan, witness.admitted.coupled⟩
  exact ⟨initial, witness.code, admitted, rfl, rfl, rfl, rfl, rfl⟩

namespace Stores

-- Synthetic owned negative fixture: MOV [RDI],ESI; MOV ESI,0;
-- MOV [RDI],ESI; RET. The data and complete return slot start as zero RAM.
def memory : Memory where
  read address := some
    (if address = 0 ∨ address = 7 then 0x89
     else if address = 1 ∨ address = 8 then 0x37
     else if address = 2 then 0xbe else if address = 9 then 0xc3 else 0)
  executable := fun _ => true
  writable := fun _ => true

def initial : State where
  registers register := if register = .rdi then 8192 else if register = .rsp then 16384 else 0
  rip := 0
  flags := 0x602
  memory := memory

private theorem zero_write : writeDWordUnchecked memory 8192 0 = memory := by
  apply congrArg (fun read => ({ memory with read := read } : Memory))
  funext address
  by_cases a0 : address = 0
  · subst address; rfl
  by_cases a1 : address = 1
  · subst address; rfl
  by_cases a2 : address = 2
  · subst address; rfl
  by_cases a7 : address = 7
  · subst address; rfl
  by_cases a8 : address = 8
  · subst address; rfl
  by_cases a9 : address = 9
  · subst address; rfl
  simp only [storedDWordByte]
  split <;> simp_all [memory]

-- Actual no-op store preserves the full Memory on its successful step.
-- A policy using only stepwise memory equality would incorrectly admit it.
theorem no_op_step (af : Bool) : step af initial = .ok ⟨.next { initial with rip := 2 }, []⟩ := by
  have actual : step af initial = .ok ⟨.next { initial with
      memory := writeDWordUnchecked memory 8192 0, rip := 2 }, []⟩ := rfl
  rw [zero_write] at actual
  exact actual

theorem no_op_rejected (Current : State → Prop) (AllowedRead : State → Read → Prop) :
    ¬ReadOnlyPolicy initial Current AllowedRead := by
  intro policy
  exact policy_rejects_store policy rfl

def temporary : State :=
  { initial with registers := fun register => if register = .rsi then 7 else initial.registers register }

def changed : State :=
  { temporary with memory := writeDWordUnchecked memory 8192 7, rip := 2 }

def moved : State := { changed.writeRegister .rsi 0 with rip := 7 }

def restored : State :=
  { moved with memory := writeDWordUnchecked moved.memory 8192 0, rip := 9 }

def returned : State :=
  { restored.writeRegister .rsp (restored.registers .rsp + 8) with rip := 0 }

theorem temporary_step (af : Bool) : step af temporary = .ok ⟨.next changed, []⟩ := rfl

theorem temporary_changes_memory : changed.memory ≠ temporary.memory := by
  intro equal
  have byte := congrArg (fun current : Memory => current.read 8192) equal
  change some (7 : Byte) = some 0 at byte
  cases byte

-- The actual decoded execution returns with the initial Memory restored.
-- Final memory equality alone therefore cannot implement the required policy.
theorem temporary_returns (choices : Choices) :
    Sequential.run choices 4 temporary = .ok ⟨returned, 4, [⟨.stack, 16384, 8⟩]⟩ := rfl

theorem temporary_restores_memory : returned.memory = temporary.memory := by
  change writeDWordUnchecked (writeDWordUnchecked memory 8192 7) 8192 0 = memory
  have overwrite : writeDWordUnchecked (writeDWordUnchecked memory 8192 7) 8192 0 =
      writeDWordUnchecked memory 8192 0 := by
    apply congrArg (fun read => ({ memory with read := read } : Memory))
    funext address
    simp only [storedDWordByte]
    split <;> simp_all [writeDWordUnchecked, storedDWordByte]
  exact overwrite.trans zero_write

theorem temporary_rejected (Current : State → Prop) (AllowedRead : State → Read → Prop) :
    ¬ReadOnlyPolicy temporary Current AllowedRead := by
  intro policy
  exact policy_rejects_store policy rfl

end Stores

#print axioms pair_claim
#print axioms stride_claim
#print axioms Grading.domain_nonvacuous
#print axioms unsupported_pair_claim
#print axioms unsupported_stride_claim
#print axioms pair_empty
#print axioms stride_empty
#print axioms Stores.no_op_rejected
#print axioms Stores.temporary_returns
#print axioms Stores.temporary_restores_memory
#print axioms Stores.temporary_rejected

end EDSL.Tests.GradingTask

-- Forbidden effects must also reject after a permitted executed prefix.
namespace EDSL.Tests.GradingPolicyPrefixes
open X86 X86.Sequential Grading

def start (suffix : List Byte) : State := codeState ([0x89, 0xf8] ++ suffix) 0
def afterMove (suffix : List Byte) : State :=
  { (start suffix).writeRegister .rax 0 with rip := 2 }

theorem move_prefix (suffix : List Byte) : Reachable (start suffix) (afterMove suffix) := by
  refine ⟨fun _ => false, 1, [], Block.next (middle := afterMove suffix)
    (reads := []) (rest := []) ?_ Block.nil⟩
  rfl

theorem syscall_rejected (Current : State → Prop) (Allowed : State → Read → Prop) :
    ¬ReadOnlyPolicy (start [0x0f, 0x05]) Current Allowed := by
  intro policy
  exact policy.rejects_instruction (move_prefix _) (instruction := .legacy .syscall) rfl rfl

theorem exchange_rejected (Current : State → Prop) (Allowed : State → Read → Prop) :
    ¬ReadOnlyPolicy (start [0x87, 0x07]) Current Allowed := by
  intro policy
  exact policy.rejects_instruction (move_prefix _) (instruction := .legacy .exchangeEaxRdi) rfl rfl

theorem locked_add_rejected (Current : State → Prop) (Allowed : State → Read → Prop) :
    ¬ReadOnlyPolicy (start [0xf0, 0x0f, 0xc1, 0x07]) Current Allowed := by
  intro policy
  exact policy.rejects_instruction (move_prefix _) (instruction := .legacy .fetchAddEaxRdi) rfl rfl

end EDSL.Tests.GradingPolicyPrefixes

#audit_edsl
