/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.MultiplyResources
import EDSL.Corpus.V1.MultiplyCertificatesFor
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.MultiplyResources
open X86 X86.Sequential OS
open Corpus.V1
open Corpus.V1.MultiplyResources

/-- A numeric regression observes a real selected-address loaded call, its
literal full64 result, actual original caller return, complete postcondition
and original current resources. It imposes no usefulness restriction. -/
private def Returns (compiler : Compiler) (left right expected : Word)
    (choices : ChoiceStream FlagChoices) : Prop :=
  ∃ result, ExecutesWith choices (initial compiler (left, right)) result ∧
    (initial compiler (left, right)).rip = (input compiler).function.window.base ∧
    result.state.registers .rax = expected ∧
    result.state.rip = caller.returnAddress ∧
    result.state.registers .rsp = caller.stack + 8 ∧
    PureCall.Post spec (PureCall.resourceInput (resource compiler (left, right)))
      (initial compiler (left, right)) result.state ∧
    CallResources.Current (resource compiler (left, right)).call
      (resource compiler (left, right)).shared result.state

private theorem numeric_result (compiler : Compiler) (left right expected : Word)
    (mathematics : WordMath.MulModulo left right expected)
    (choices : ChoiceStream FlagChoices) : Returns compiler left right expected choices := by
  obtain ⟨result, execution, post, current⟩ :=
    ((MultiplyCertificatesFor.certificate compiler).resource
      (loadedCall compiler (left, right))).1 choices
  have correct : WordMath.MulModulo left right (result.state.registers .rax) := post.result
  exact ⟨result, execution, initial_entry compiler (left, right),
    WordMath.mulModulo_unique correct mathematics, post.returnAddress, post.stackPointer,
    post, current⟩

/-- The independently supplied unbounded product wraps at 2^64. This applies
to both original compiler artifacts and every complete undefined-flag stream. -/
theorem wrapping_product (compiler : Compiler) (choices : ChoiceStream FlagChoices) :
    Returns compiler 0xffffffffffffffff 2 0xfffffffffffffffe choices :=
  numeric_result compiler _ _ _ (by unfold WordMath.MulModulo; decide +kernel) choices

/-- Both inputs contribute above bit31. A low32 multiply or result truncation
would return 1 instead of the independently specified 2^33 + 1. -/
theorem upper_word_product (compiler : Compiler) (choices : ChoiceStream FlagChoices) :
    Returns compiler 0x100000001 0x100000001 0x200000001 choices :=
  numeric_result compiler _ _ _ (by unfold WordMath.MulModulo; decide +kernel) choices

/-- Zero is admitted and returns through the original caller even though the
certificate's separate existential usefulness predicate excludes this pair. -/
theorem zero_is_admitted (compiler : Compiler) (choices : ChoiceStream FlagChoices) :
    PureCall.ResourcePre spec (bytes compiler) (resource compiler (0, 0xffffffffffffffff))
      (initial compiler (0, 0xffffffffffffffff)) ∧
    ¬spec.useful (0, 0xffffffffffffffff) ∧
    Returns compiler 0 0xffffffffffffffff 0 choices := by
  refine ⟨pre compiler _, ?_, numeric_result compiler _ _ _ (by unfold WordMath.MulModulo; decide +kernel) choices⟩
  intro useful
  exact useful.1 rfl

/-- The stack-kind footprint is produced only by actual RET, including all
currently supported memory instructions rather than just this graph. -/
private theorem stack_read_only_ret {instruction : Sequential.Instruction}
    {before : State} {read : Read} (member : read ∈ instruction.operandReads before)
    (stack : read.kind = .stack) : instruction = .legacy .ret := by
  cases instruction <;> simp_all [Instruction.operandReads]
  rename_i old
  cases old <;> simp_all

private theorem actual_stack_read_decodes_ret {before : State} {vector : FlagChoices}
    {observation : Observation} {read : Read}
    (actual : stepWith vector before = .ok observation)
    (member : read ∈ observation.reads) (stack : read.kind = .stack) :
    Sequential.decodeAt before = .ok (.legacy .ret) := by
  cases decoded : Sequential.decodeAt before with
  | error fault => simp only [stepWith, decoded, error_bind, reduceCtorEq] at actual
  | ok instruction =>
    have effect : executeWith before instruction vector = .ok observation := by
      rwa [stepWith_eq_executeWith vector decoded] at actual
    have origin := executeWith_reads effect
    have present : read ∈ instruction.operandReads before := by rwa [← origin]
    have isRet := stack_read_only_ret present stack
    simp only [isRet]

private theorem return_read_present (compiler : Compiler) (value : Word × Word)
    {choices : ChoiceStream FlagChoices} {result : Result}
    (execution : ExecutesWith choices (initial compiler value) result) :
    MultiplyBodies.stackRead (initial compiler value) ∈ result.reads := by
  have observed := MultiplyBodies.observations compiler (pre compiler value).machine execution
  rw [observed.2.2.2]
  exact List.mem_singleton.mpr rfl

/-- The nonempty read trace selects an actual decoded RET prefix. Its original
caller-slot read has current original authority and successful production
memory access under every complete vector stream. -/
theorem original_return_read_origin (compiler : Compiler) (value : Word × Word)
    (choices : ChoiceStream FlagChoices) :
    ∃ result, ExecutesWith choices (initial compiler value) result ∧
      PureCall.Post spec (PureCall.resourceInput (resource compiler value))
        (initial compiler value) result.state ∧
      CallResources.Current (resource compiler value).call
        (resource compiler value).shared result.state ∧
      ∃ count before priorReads observation, count < result.instructions ∧
        BlockWith choices (initial compiler value) before count priorReads ∧
        stepWith (choices count) before = .ok observation ∧
        Sequential.decodeAt before = .ok (.legacy .ret) ∧
        MultiplyBodies.stackRead (initial compiler value) ∈ observation.reads ∧
        CallResources.Current (resource compiler value).call
          (resource compiler value).shared before ∧
        CallResources.ReadAllowed (resource compiler value).call (resource compiler value).shared
          (MultiplyBodies.stackRead (initial compiler value)) ∧
        OperandReadSucceeds before (MultiplyBodies.stackRead (initial compiler value)) := by
  obtain ⟨executions, policy⟩ := (MultiplyCertificatesFor.certificate compiler).resource
    (loadedCall compiler value)
  obtain ⟨result, execution, post, current⟩ := executions choices
  obtain ⟨count, before, priorReads, observation, bound, block, actual, member,
    held, allowed, succeeds⟩ := policy.read_origin execution (return_read_present compiler value execution)
  exact ⟨result, execution, post, current, count, before, priorReads, observation,
    bound, block, actual, actual_stack_read_decodes_ret actual member rfl,
    member, held, allowed, succeeds⟩

/-- Finish exactly the original caller-slot loan. No cell, permission,
allocation, owner, epoch or other loan is changed. -/
private def ended (compiler : Compiler) (value : Word × Word) : Borrowing.State :=
  { (resource compiler value).shared with loans := fun query =>
      if query = (resource compiler value).call.stackLoan then none
      else (resource compiler value).shared.loans query }

private def revoked (compiler : Compiler) (value : Word × Word) : PureCall.Resources spec :=
  { resource compiler value with shared := ended compiler value }

private theorem original_loans (compiler : Compiler) (value : Word × Word) (identifier : Nat) :
    (resource compiler value).shared.loans identifier =
      if identifier = 1 then some (CallResources.Domain.stackLoan (environment compiler))
      else if identifier = 0 then some (CallResources.Domain.codeLoan (environment compiler))
      else none := by
  simp [resource, PureCall.Domain.resource, CallResources.Domain.shared,
    CallResources.Domain.codeBorrowed, Borrowing.installLoan, Borrowing.empty]
  rfl

/-- Unchanged readable RAM and the remaining code loan do not authorize the
original caller-slot operand once its own loan has ended. -/
private theorem ended_stack_denied (compiler : Compiler) (value : Word × Word) :
    ¬CallResources.ReadAllowed (resource compiler value).call (ended compiler value)
      ⟨.stack, (resource compiler value).call.stack, 8⟩ := by
  intro allowed
  obtain ⟨identifier, loan, authorized, inside⟩ := allowed.2.2.2
  have stackId : (resource compiler value).call.stackLoan = 1 := rfl
  by_cases gone : identifier = 1
  · have missing : (ended compiler value).loans identifier = none := by
      simp only [ended, stackId, gone, ↓reduceIte]
    simp only [Borrowing.authorize, missing, reduceCtorEq] at authorized
  by_cases zero : identifier = 0
  · have held : (ended compiler value).loans identifier =
        some (CallResources.Domain.codeLoan (environment compiler)) := by
      simp only [ended, stackId, original_loans, zero, Nat.zero_ne_one, ↓reduceIte]
    have borrower : (CallResources.Domain.codeLoan (environment compiler)).borrower =
        Threads.principal (resource compiler value).call.worker := rfl
    have same : CallResources.Domain.codeLoan (environment compiler) = loan := by
      simpa only [Borrowing.authorize, held, borrower, ↓reduceIte, Except.ok.injEq] using authorized
    subst loan
    have stackInside : caller.region.Contains caller.stack := by decide +kernel
    have overlap : (⟨(input compiler).function.window.base,
        (input compiler).bytes.length⟩ : AddressSpace.Region).Contains caller.stack :=
      Borrowing.subregion_inside inside stackInside
    exact (Ownership.disjoint_outside (separate compiler) stackInside) overlap
  · have missing : (ended compiler value).loans identifier = none := by
      simp only [ended, stackId, gone, ↓reduceIte, original_loans, zero]
    simp only [Borrowing.authorize, missing, reduceCtorEq] at authorized

/-- This is a successful production finishLoan operation. Even though every
RAM/permission observation is unchanged, no current loaded call can use the
revoked original resource record. -/
theorem original_stack_loan_revocation (compiler : Compiler) (value : Word × Word) :
    Borrowing.finishLoan (resource compiler value).shared
      (Threads.principal (resource compiler value).call.worker)
      (resource compiler value).call.stackLoan = .ok (ended compiler value) ∧
    (ended compiler value).resources = (resource compiler value).shared.resources ∧
    ¬CallResources.ReadAllowed (resource compiler value).call (ended compiler value)
      ⟨.stack, (resource compiler value).call.stack, 8⟩ ∧
    ¬∃ call : PureCall.ELFLoadedCall spec (file compiler) name (input compiler),
      call.resource = revoked compiler value := by
  obtain ⟨loan, live, borrower, _⟩ := (pre compiler value).current.contract.stackLoan
  refine ⟨?_, rfl, ended_stack_denied compiler value, ?_⟩
  · simp [Borrowing.finishLoan, Borrowing.authorize, live, borrower, ended]
  · rintro ⟨call, same⟩
    have held := call.pre.current.contract.stackLoan
    rw [same] at held
    obtain ⟨_, stillLive, _, _⟩ := held
    simp [revoked, ended] at stillLive

/-- The raw machine still executes and reads its original return slot, but no
vector policy can authorize that same actual read using the revoked world.
This does not misclassify logical authority loss as a machine fault. -/
theorem revoked_policy_rejected (compiler : Compiler) (value : Word × Word)
    (Current : State → Prop) :
    ¬Grading.ReadOnlyPolicyFor .flags (initial compiler value) Current
      (fun _ read => CallResources.ReadAllowed (resource compiler value).call
        (ended compiler value) read) := by
  intro policy
  obtain ⟨result, execution, _post, _current⟩ :=
    executes compiler (pre compiler value) (fun _ => FlagChoices.uniform false)
  obtain ⟨_count, _before, _priorReads, _observation, _bound, _block, _actual, _member,
    _held, allowed, _succeeds⟩ :=
    policy.read_origin execution (return_read_present compiler value execution)
  apply ended_stack_denied compiler value
  simpa only [MultiplyBodies.stackRead, (pre compiler value).stack] using allowed

/-- Owned synthetic MOV [RDI],ESI. All target bytes are already zero, the
complete store is permitted, and the real decoded instruction still lies
outside the read-only policy's allowed instruction family. -/
private def sameStore : State where
  registers := fun _ => 0
  rip := 4096
  flags := 0x202
  memory := {
    read := fun address => if address = 4096 then some 0x89
      else if address = 4097 then some 0x37 else some 0
    executable := fun address => decide (address = 4096 ∨ address = 4097)
    writable := fun _ => true }

private theorem sameStore_memory : writeDWordUnchecked sameStore.memory 0 0 = sameStore.memory := by
  have sameRead : (writeDWordUnchecked sameStore.memory 0 0).read = sameStore.memory.read := by
    funext query
    by_cases small : query.toNat < 4
    · have alternatives : query = 0 ∨ query = 1 ∨ query = 2 ∨ query = 3 := by
        have values : query.toNat = 0 ∨ query.toNat = 1 ∨
            query.toNat = 2 ∨ query.toNat = 3 := by omega
        rcases values with zero | one | two | three
        · exact .inl (BitVec.eq_of_toNat_eq zero)
        · exact .inr (.inl (BitVec.eq_of_toNat_eq one))
        · exact .inr (.inr (.inl (BitVec.eq_of_toNat_eq two)))
        · exact .inr (.inr (.inr (BitVec.eq_of_toNat_eq three)))
      rcases alternatives with rfl | rfl | rfl | rfl <;> rfl
    · exact writeDWord_frame sameStore.memory 0 query 0 (by simpa using Nat.le_of_not_gt small)
  exact congrArg (fun read => { sameStore.memory with read := read }) sameRead

/-- Successful same-value writes are rejected by their actual decoded effect,
not admitted merely because all memory values and permissions stay equal. -/
theorem same_value_store_rejected (vector : FlagChoices)
    (Current : State → Prop) (AllowedRead : State → Read → Prop) :
    stepWith vector sameStore = .ok ⟨.next { sameStore with rip := 4098 }, []⟩ ∧
    (writeDWordUnchecked sameStore.memory 0 0).read = sameStore.memory.read ∧
    ¬Grading.ReadOnlyPolicyFor .flags sameStore Current AllowedRead := by
  have decoded : Sequential.decodeAt sameStore = .ok (.legacy .storeEsiRdi) := rfl
  have stored : storeDWord sameStore.memory 0 0 = .ok sameStore.memory := by
    have writable : canStoreDWord sameStore.memory 0 = true := rfl
    simp only [storeDWord, writable, ↓reduceIte, sameStore_memory]
  refine ⟨?_, congrArg Memory.read sameStore_memory, ?_⟩
  · rw [stepWith_eq_executeWith vector decoded,
      executeWith_eq_execute sameStore (.legacy .storeEsiRdi) vector rfl]
    have regs : sameStore.registers .rdi = 0 ∧
        (sameStore.registers .rsi).setWidth 32 = 0 := ⟨rfl, rfl⟩
    simp only [execute, X86.executeInstruction, X86.executeStore, regs.1, regs.2, stored,
      Instruction.operandReads, ok_bind, pure_ok]
    rfl
  · intro policy
    exact policy.rejects_instruction
      ⟨fun _ => FlagChoices.uniform false, 0, [], .nil⟩ decoded rfl

#print axioms wrapping_product
#print axioms upper_word_product
#print axioms zero_is_admitted
#print axioms original_return_read_origin
#print axioms original_stack_loan_revocation
#print axioms revoked_policy_rejected
#print axioms same_value_store_rejected
end EDSL.Tests.MultiplyResources
#audit_edsl
