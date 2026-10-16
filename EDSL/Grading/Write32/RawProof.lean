/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Write32.Contract

set_option warningAsError true

namespace EDSL.Grading.Write32
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS
open EDSL.Grading.Trace

/-- Concrete exact-byte fixture owned by this project. Acceptance still fixes
the independent contract, rather than defining it by this implementation. -/
def bytes : List Byte := [0x89, 0x37, 0xc3]

def afterStore (initial : State) : State :=
  { initial with
    memory := writeDWordUnchecked initial.memory (initial.registers .rdi)
      ((initial.registers .rsi).setWidth 32)
    rip := initial.rip + 2 }

abbrev returned (initial : State) (target : Word) : State :=
  EDSL.Examples.Compiler.MemoryOps.storeFinal initial target

theorem store_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt initial = .ok (.legacy .storeEsiRdi) := by
  apply decodeAt_legacy
  have b0 := pre.code.2 0 0x89 (by decide)
  have b1 := pre.code.2 1 0x37 (by decide)
  simp only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] at b0 b1
  simp [X86.decodeAt, b0, b1]

theorem store_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af initial = .ok ⟨.next (afterStore initial), []⟩ := by
  rw [step_eq_execute af (store_decoded pre)]
  have writable : canStoreDWord initial.memory (initial.registers .rdi) = true := by
    simpa only [pre.pointer] using pre.writable
  simp [Sequential.execute, Instruction.operandReads, X86.executeInstruction,
    executeStore, storeDWord, writable, afterStore]

theorem afterStore_code {input initial} (pre : Pre bytes input initial) :
    CodeAt (afterStore initial).memory initial.rip bytes := by
  apply writeDWord_preserves_code
  · exact pre.code
  · simpa only [pre.pointer] using pre.codeDisjoint

theorem afterStore_stack {input initial} (pre : Pre bytes input initial) :
    readWord (afterStore initial).memory (initial.registers .rsp) = .ok input.returnAddress := by
  apply (readWord_congr _ _ _ (writeDWord_agrees _ _ _ _ 8 ?_)).trans pre.stack
  simpa only [pre.pointer] using pre.stackDisjoint

theorem ret_decoded {input initial} (pre : Pre bytes input initial) :
    Sequential.decodeAt (afterStore initial) = .ok (.legacy .ret) := by
  apply decodeAt_legacy
  have b2 := (afterStore_code pre).2 2 0xc3 (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at b2
  change fetchByte (afterStore initial).memory (afterStore initial).rip = .ok 0xc3 at b2
  simp [X86.decodeAt, b2]

theorem ret_step {input initial} (pre : Pre bytes input initial) (af : Bool) :
    Sequential.step af (afterStore initial) =
      .ok ⟨.returned (returned initial input.returnAddress),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩ := by
  rw [step_eq_execute af (ret_decoded pre)]
  have stack : readWord (afterStore initial).memory ((afterStore initial).registers .rsp) =
      .ok input.returnAddress := afterStore_stack pre
  simp [Sequential.execute, Instruction.operandReads, X86.executeInstruction,
    executeRet, stack, pre.returnCanonical, State.writeRegister,
    returned, Examples.Compiler.MemoryOps.storeFinal]
  simp only [afterStore, and_self]

theorem returned_post {input initial} (pre : Pre bytes input initial) :
    Post input initial (returned initial input.returnAddress) := by
  have enabled : canStoreDWord initial.memory (initial.registers .rdi) = true := by simpa only [pre.pointer] using pre.writable
  have actualValue := (store_sound initial.memory (initial.registers .rdi)
    ((initial.registers .rsi).setWidth 32) enabled).2
  have noWrap : input.address.toNat + 3 < 2^64 := by
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp pre.target_addressable).1
  refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simpa [returned, Examples.Compiler.MemoryOps.storeFinal, pre.pointer, pre.source] using actualValue
  · intro query outside
    have large : 4 ≤ (query - input.address).toNat := by
      have excluded := mt (AddressSpace.word_contains_iff input.address query noWrap).mpr outside
      omega
    exact writeDWord_frame initial.memory _ query _ (by rwa [pre.pointer])
  · simp [returned, Examples.Compiler.MemoryOps.storeFinal]
  · intro register member
    have notStack : register ≠ .rsp := by
      intro same
      subst register
      simp [calleeSaved] at member
    simp [returned, Examples.Compiler.MemoryOps.storeFinal, notStack]

theorem store_fetch {input initial} (_pre : Pre bytes input initial) :
    FetchAllowed initial.rip bytes.length initial (.legacy .storeEsiRdi) := by
  change initial.rip.toNat ≤ initial.rip.toNat ∧ initial.rip.toNat + 2 ≤ initial.rip.toNat + 3
  exact ⟨Nat.le_refl _, by omega⟩

theorem ret_fetch {input initial} (pre : Pre bytes input initial) :
    FetchAllowed initial.rip bytes.length (afterStore initial) (.legacy .ret) := by
  have bound := pre.code.1
  change initial.rip.toNat + 3 ≤ 2^64 at bound
  have offset : (initial.rip + 2).toNat = initial.rip.toNat + 2 := by
    change (initial.rip.toNat + 2) % 2^64 = initial.rip.toNat + 2
    exact Nat.mod_eq_of_lt (by omega)
  change initial.rip.toNat ≤ (initial.rip + 2).toNat ∧
    (initial.rip + 2).toNat + 1 ≤ initial.rip.toNat + 3
  rw [offset]
  omega

/-- All-input raw trace policy for 89 37 c3, with both AF choices checked.
The invariant is proof evidence constructed after admission, not a Pre field. -/
theorem raw_policy {input initial} (pre : Pre bytes input initial) : RawPolicy bytes input initial := by
  refine ⟨(fun (_ : Unit) state => state = initial ∨ state = afterStore initial), Or.inl rfl, ?_⟩
  intro ghost before inside
  rcases inside with same | same
  · subst before
    refine ⟨True.intro, .legacy .storeEsiRdi, store_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.next (afterStore initial), []⟩, (), store_step pre af, ?_, ?_, Or.inr rfl⟩
    · simp
    · exact ⟨store_fetch pre, Or.inr ⟨(initial.registers .rsi).setWidth 32, by simp [Sequential.Instruction.storeIntent,
        X86.Instruction.storeIntent, pre.pointer]⟩⟩
  · subst before
    refine ⟨True.intro, .legacy .ret, ret_decoded pre, ?_⟩
    intro af
    refine ⟨⟨.returned (returned initial input.returnAddress),
      [⟨.stack, initial.registers .rsp, 8⟩]⟩, (), ret_step pre af, ?_, ?_, True.intro⟩
    · intro read member
      simp only [List.mem_singleton] at member
      subst read
      exact ⟨True.intro, rfl, _, afterStore_stack pre⟩
    · exact ⟨ret_fetch pre, Or.inl rfl⟩

/-- Universal raw functional semantics: this is only the machine half, not a
full registered Claim until current-resource semantics and witnesses agree. -/
theorem raw_semantics {input initial} (pre : Pre bytes input initial) :
    AllExecutions initial (fun result => Post input initial result.state) ∧ RawPolicy bytes input initial := by
  refine ⟨?_, raw_policy pre⟩
  intro choices
  refine ⟨⟨returned initial input.returnAddress, 2, [⟨.stack, initial.registers .rsp, 8⟩]⟩,
    ?_, returned_post pre⟩
  have execution : Sequential.Executes choices initial
      ((⟨returned initial input.returnAddress, 1, [⟨.stack, initial.registers .rsp, 8⟩]⟩ : Result).prepend 1 []) :=
    .next (store_step pre (choices 0)) (.ret (ret_step pre ((choices.drop 1) 0)))
  simpa [Result.prepend] using execution

end EDSL.Grading.Write32
