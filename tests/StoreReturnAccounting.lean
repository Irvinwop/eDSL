/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.StoreReturn32.Accounting
import EDSL.Grading.Write32.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.StoreReturnAccounting
open X86 X86.Sequential OS StoreReturn32
open Grading.Write32 (Input Pre Useful RawPolicy Resources ResourcePre ResourceReturn resourceInput)

/-- Every shape has a useful current-resource admission with an initially
different RAX, for every AF stream. The counted optimum and returned OS world
belong to the same actual execution, including its original caller read. -/
theorem admitted_optimum (shape : Shape) (choices : Choices) :
    ∃ resource initial result evolved,
      ResourcePre shape.bytes resource initial ∧ Useful (resourceInput resource) ∧
      initial.registers .rax ≠ (resourceInput resource).address ∧
      Sequential.Executes choices initial result ∧
      StoreReturn32.Post (resourceInput resource) initial result.state ∧
      result.instructions = 3 ∧ result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧
      Grading.Trace.LiftedExecutes (Grading.Write32.resourceRules resource.call)
        choices initial resource.seed result evolved ∧
      WordResources.Current resource.call evolved result.state ∧
      Grading.Write32.Frame resource.call.targetPointer resource.seed evolved ∧
      RawPolicy shape.bytes (resourceInput resource) initial ∧
      ∀ (candidateBytes : List Byte) (candidateInitial : State)
        (candidateChoices : Choices) (candidateResult : Result),
        Pre candidateBytes (resourceInput resource) candidateInitial →
        candidateInitial.registers .rax ≠ (resourceInput resource).address →
        RawPolicy candidateBytes (resourceInput resource) candidateInitial →
        Sequential.Executes candidateChoices candidateInitial candidateResult →
        StoreReturn32.Post (resourceInput resource) candidateInitial candidateResult.state →
        result.instructions ≤ candidateResult.instructions := by
  let witness := Grading.Write32.Domain.candidate shape.bytes
    (by cases shape <;> decide) (by cases shape <;> decide)
  let resource : Resources :=
    ⟨witness.shared, witness.call, witness.initial.registers .rsi, witness.oldValue⟩
  have pre : ResourcePre shape.bytes resource witness.initial :=
    ⟨witness.current, witness.raw.codeBytes, witness.raw.entry, witness.raw.stackPointer,
      witness.raw.targetPointer, rfl, witness.raw.old⟩
  have useful : Useful (resourceInput resource) := witness.raw.useful
  have needed : witness.initial.registers .rax ≠ (resourceInput resource).address := by
    change (0xfedcba9876543210 : Word) ≠ 262144
    decide
  obtain ⟨result, execution, post, returned, cost, reads⟩ := resource_exact_three pre choices
  obtain ⟨optimum, optimalExecution, _, _, _, policy, comparison⟩ :=
    optimal_for_useful_input pre.machine useful needed choices
  have same := Sequential.Executes.fixed_choices_unique optimalExecution execution
  rw [same] at comparison
  obtain ⟨evolved, lifted, current, frame⟩ := returned choices execution
  exact ⟨resource, witness.initial, result, evolved, pre, useful, needed, execution,
    post, cost, reads, lifted, current, frame, policy, comparison⟩

/-- Store/RET really satisfies the pointer contract in two when RAX already
contains the target. The ordinary store changes useful inputs; RET preserves
that pointer and consumes the original eight-byte caller slot. -/
theorem already_returned_pointer {input : Input} {initial : State}
    (pre : Pre Grading.Write32.bytes input initial)
    (pointer : initial.registers .rax = input.address) (choices : Choices) :
    ∃ result : Result, Sequential.Executes choices initial result ∧
      StoreReturn32.Post input initial result.state ∧ result.instructions = 2 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧
      RawPolicy Grading.Write32.bytes input initial := by
  have execution := Sequential.Executes.next (Grading.Write32.store_step pre (choices 0))
    (Sequential.Executes.ret (Grading.Write32.ret_step pre ((choices.drop 1) 0)))
  refine ⟨⟨Grading.Write32.returned initial input.returnAddress, 2,
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, ?_, ?_, rfl, rfl, Grading.Write32.raw_policy pre⟩
  · simpa only [Result.prepend, List.nil_append] using execution
  · refine ⟨Grading.Write32.returned_post pre, ?_⟩
    simpa [Grading.Write32.returned, Examples.Compiler.MemoryOps.storeFinal] using pointer

/-- An admitted useful input witnesses the missing-mismatch boundary. Updating
only RAX leaves the present code, memory permissions, ABI arguments, loans and
current OS world intact; its two-instruction return still has that world. -/
theorem initial_match_two_instructions (choices : Choices) :
    ∃ resource initial result,
      ResourcePre Grading.Write32.bytes resource initial ∧ Useful (resourceInput resource) ∧
      initial.registers .rax = (resourceInput resource).address ∧
      Sequential.Executes choices initial result ∧
      StoreReturn32.Post (resourceInput resource) initial result.state ∧
      result.instructions = 2 ∧ result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧
      RawPolicy Grading.Write32.bytes (resourceInput resource) initial ∧
      ResourceReturn resource initial result := by
  let witness := Grading.Write32.Domain.candidate Grading.Write32.bytes (by decide) (by decide)
  let initial := witness.initial.writeRegister .rax witness.call.targetPointer
  let resource : Resources :=
    ⟨witness.shared, witness.call, witness.initial.registers .rsi, witness.oldValue⟩
  have pre : ResourcePre Grading.Write32.bytes resource initial := by
    refine ⟨⟨witness.current.contract, witness.current.coupled⟩,
      witness.raw.codeBytes, witness.raw.entry, ?_, ?_, ?_, witness.raw.old⟩
    · simpa [initial, State.writeRegister] using witness.raw.stackPointer
    · simpa [initial, State.writeRegister] using witness.raw.targetPointer
    · simp [initial, State.writeRegister, resource]
  have pointer : initial.registers .rax = (resourceInput resource).address := by
    simp [initial, State.writeRegister, resourceInput, resource]
  obtain ⟨result, execution, post, cost, reads, policy⟩ :=
    already_returned_pointer pre.machine pointer choices
  exact ⟨resource, initial, result, pre, witness.raw.useful, pointer, execution, post,
    cost, reads, policy, (Grading.Write32.resource_policy pre).returned⟩

private def copyRetBytes : List Byte := [0x48, 0x89, 0xf8, 0xc3]

/-- If the target word already equals the desired value, an actual full-width
copy/RET meets the independent pointer/store/frame contract in two, with the
registered raw policy. Neither step performs a target write or target read. -/
theorem already_equal_copy_ret {input : Input} {initial : State}
    (pre : Pre copyRetBytes input initial)
    (equal : input.oldValue = input.argument.setWidth 32) (choices : Choices) :
    ∃ result : Result, Sequential.Executes choices initial result ∧
      StoreReturn32.Post input initial result.state ∧ result.instructions = 2 ∧
      result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧
      RawPolicy copyRetBytes input initial := by
  let middle : State :=
    { initial.writeRegister .rax (initial.registers .rdi) with rip := initial.rip + 3 }
  let final := WordResources.returnAfter middle input.returnAddress
  have decodedCopy : Sequential.decodeAt initial = .ok (.movReg64 .rax .rdi) :=
    decodeAt_transport
      (code_fetch_transport pre.code (by decide) 0 (by decide) initial rfl (by simp)) rfl
  have decodedRet : Sequential.decodeAt middle = .ok (.legacy .ret) :=
    decodeAt_transport
      (code_fetch_transport pre.code (by decide) 3 (by decide) middle rfl rfl) rfl
  have copyStep (af : Bool) : Sequential.step af initial = .ok ⟨.next middle, []⟩ := by
    rw [step_eq_execute af decodedCopy]
    rfl
  have retStep (af : Bool) : Sequential.step af middle =
      .ok ⟨.returned final, [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
    rw [step_eq_execute af decodedRet]
    simp [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
      executeRet, pre.stack, pre.returnCanonical, final, WordResources.returnAfter,
      middle, State.writeRegister]
  have copyFetch : Grading.Write32.FetchAllowed initial.rip copyRetBytes.length
      initial (.movReg64 .rax .rdi) := by
    change initial.rip.toNat ≤ initial.rip.toNat ∧ initial.rip.toNat + 3 ≤ initial.rip.toNat + 4
    omega
  have retFetch : Grading.Write32.FetchAllowed initial.rip copyRetBytes.length
      middle (.legacy .ret) := by
    have bound := pre.code.1
    change initial.rip.toNat + 4 ≤ 2^64 at bound
    have offset : (initial.rip + 3).toNat = initial.rip.toNat + 3 := by
      change (initial.rip.toNat + 3) % 2^64 = initial.rip.toNat + 3
      exact Nat.mod_eq_of_lt (by omega)
    change initial.rip.toNat ≤ (initial.rip + 3).toNat ∧
      (initial.rip + 3).toNat + 1 ≤ initial.rip.toNat + 4
    rw [offset]
    omega
  have policy : RawPolicy copyRetBytes input initial := by
    refine ⟨(fun (_ : Unit) before => before = initial ∨ before = middle), Or.inl rfl, ?_⟩
    intro ghost before inside
    rcases inside with same | same
    · subst before
      refine ⟨True.intro, .movReg64 .rax .rdi, decodedCopy, ?_⟩
      intro af
      exact ⟨⟨.next middle, []⟩, (), copyStep af, by simp,
        ⟨copyFetch, Or.inl rfl⟩, Or.inr rfl⟩
    · subst before
      refine ⟨True.intro, .legacy .ret, decodedRet, ?_⟩
      intro af
      refine ⟨⟨.returned final, [⟨.stack, initial.registers .rsp, 8⟩]⟩,
        (), retStep af, ?_, ⟨retFetch, Or.inl rfl⟩, True.intro⟩
      intro read member
      simp only [List.mem_singleton] at member
      subst read
      exact ⟨True.intro, rfl, input.returnAddress, pre.stack⟩
  have execution := Sequential.Executes.next (copyStep (choices 0))
    (Sequential.Executes.ret (retStep ((choices.drop 1) 0)))
  refine ⟨⟨final, 2, [⟨.stack, initial.registers .rsp, 8⟩]⟩, ?_, ?_, rfl, rfl, policy⟩
  · simpa only [Result.prepend, List.nil_append] using execution
  · refine ⟨⟨pre.oldValue.trans (congrArg Except.ok equal), (by intros; rfl),
      rfl, rfl, rfl, ?_, ?_, rfl⟩, ?_⟩
    · simp [final, WordResources.returnAfter, middle, State.writeRegister]
    · intro register member
      have notStack : register ≠ .rsp := by
        intro same
        subst register
        simp [Grading.Write32.calleeSaved] at member
      have notRax : register ≠ .rax := by
        intro same
        subst register
        simp [Grading.Write32.calleeSaved] at member
      simp [final, WordResources.returnAfter, middle, State.writeRegister, notStack, notRax]
    · simpa [final, WordResources.returnAfter, middle, State.writeRegister] using pre.pointer

/-- The non-useful boundary also has present writable current resources and
an initially different RAX. Thus mismatch and raw policy alone cannot justify
three: this actual copy/RET returns after two without changing the word. -/
theorem already_equal_two_instructions (choices : Choices) :
    ∃ resource initial result,
      ResourcePre copyRetBytes resource initial ∧ ¬Useful (resourceInput resource) ∧
      initial.registers .rax ≠ (resourceInput resource).address ∧
      Sequential.Executes choices initial result ∧
      StoreReturn32.Post (resourceInput resource) initial result.state ∧
      result.instructions = 2 ∧ result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧
      RawPolicy copyRetBytes (resourceInput resource) initial := by
  let witness := Grading.Write32.Domain.candidate copyRetBytes (by decide) (by decide)
  let initial := witness.initial.writeRegister .rsi 0
  let resource : Resources := ⟨witness.shared, witness.call, 0, witness.oldValue⟩
  have pre : ResourcePre copyRetBytes resource initial := by
    refine ⟨⟨witness.current.contract, witness.current.coupled⟩,
      witness.raw.codeBytes, witness.raw.entry, ?_, ?_, ?_, witness.raw.old⟩
    · simpa [initial, State.writeRegister] using witness.raw.stackPointer
    · simpa [initial, State.writeRegister] using witness.raw.targetPointer
    · simp [initial, State.writeRegister, resource]
  have equal : (resourceInput resource).oldValue = (resourceInput resource).argument.setWidth 32 := rfl
  have needed : initial.registers .rax ≠ (resourceInput resource).address := by
    change (0xfedcba9876543210 : Word) ≠ 262144
    decide
  obtain ⟨result, execution, post, cost, reads, policy⟩ := already_equal_copy_ret pre.machine equal choices
  exact ⟨resource, initial, result, pre, fun useful => useful equal, needed,
    execution, post, cost, reads, policy⟩

end EDSL.Tests.StoreReturnAccounting

#print axioms EDSL.StoreReturn32.exact_three
#print axioms EDSL.StoreReturn32.resource_exact_three
#print axioms EDSL.StoreReturn32.optimal_for_useful_input
#print axioms EDSL.Tests.StoreReturnAccounting.admitted_optimum
#print axioms EDSL.Tests.StoreReturnAccounting.initial_match_two_instructions
#print axioms EDSL.Tests.StoreReturnAccounting.already_equal_two_instructions
#audit_edsl
