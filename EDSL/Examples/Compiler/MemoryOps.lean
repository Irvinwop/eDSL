/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Execution

namespace EDSL.Examples.Compiler.MemoryOps
open X86

def loadBytes : List Byte := [0x8b, 0x07, 0xc3]
def storeBytes : List Byte := [0x89, 0x37, 0xc3]

def loadFinal (initial : State) (value : BitVec 32) (returnAddress : Word) : State :=
  { initial with
    registers := fun register =>
      if register = .rsp then initial.registers .rsp + 8
      else if register = .rax then value.setWidth 64
      else initial.registers register
    rip := returnAddress }

def storeFinal (initial : State) (returnAddress : Word) : State :=
  { initial with
    registers := fun register =>
      if register = .rsp then initial.registers .rsp + 8 else initial.registers register
    memory := writeDWordUnchecked initial.memory (initial.registers .rdi)
      ((initial.registers .rsi).setWidth 32)
    rip := returnAddress }

theorem load_run (initial : State) (value : BitVec 32) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip loadBytes)
    (data : loadDWord initial.memory (initial.registers .rdi) = .ok value)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    run 2 initial = .ok ⟨loadFinal initial value returnAddress, 2⟩ := by
  have b0 := code.2 0 0x8b (by decide)
  have b1 := code.2 1 0x07 (by decide)
  have b2 := code.2 2 0xc3 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1 b2
  simp [run, step, decodeAt, b0, b1, b2, executeLoad, data, executeRet, stack,
    returnValid, State.writeRegister, loadFinal]

theorem store_run (initial : State) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip storeBytes)
    (allowed : canStoreDWord initial.memory (initial.registers .rdi) = true)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip storeBytes.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    run 2 initial = .ok ⟨storeFinal initial returnAddress, 2⟩ := by
  have newCode := writeDWord_preserves_code initial.memory (initial.registers .rdi)
    initial.rip ((initial.registers .rsi).setWidth 32) storeBytes code codeDisjoint
  have newStack := (readWord_congr _ _ _ (writeDWord_agrees initial.memory
    (initial.registers .rdi) (initial.registers .rsp) ((initial.registers .rsi).setWidth 32)
    8 stackDisjoint)).trans stack
  have b0 := code.2 0 0x89 (by decide)
  have b1 := code.2 1 0x37 (by decide)
  have b2 := newCode.2 2 0xc3 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1 b2
  simp [run, step, decodeAt, b0, b1, b2, executeStore, storeDWord, allowed,
    executeRet, newStack, returnValid, State.writeRegister, storeFinal]

theorem load_correct (initial : State) (value : BitVec 32) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip loadBytes)
    (data : loadDWord initial.memory (initial.registers .rdi) = .ok value)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    Executes initial (loadFinal initial value returnAddress) 2 ∧
    ¬ Diverges initial ∧
    ∀ final count, Executes initial final count →
      final = loadFinal initial value returnAddress ∧ count = 2 := by
  have execution := run_sound (load_run initial value returnAddress code data stack returnValid)
  exact ⟨execution, execution.no_divergence, fun _ _ other => other.deterministic execution⟩

theorem store_correct (initial : State) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip storeBytes)
    (allowed : canStoreDWord initial.memory (initial.registers .rdi) = true)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip storeBytes.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    Executes initial (storeFinal initial returnAddress) 2 ∧
    ¬ Diverges initial ∧
    ∀ final count, Executes initial final count →
      final = storeFinal initial returnAddress ∧ count = 2 := by
  have execution := run_sound
    (store_run initial returnAddress code allowed codeDisjoint stackDisjoint stack returnValid)
  exact ⟨execution, execution.no_divergence, fun _ _ other => other.deterministic execution⟩

theorem store_value_and_frame (initial : State) (returnAddress : Word)
    (allowed : canStoreDWord initial.memory (initial.registers .rdi) = true) :
    loadDWord (storeFinal initial returnAddress).memory (initial.registers .rdi) =
      .ok ((initial.registers .rsi).setWidth 32) ∧
    ∀ query, 4 ≤ (query - initial.registers .rdi).toNat →
      (storeFinal initial returnAddress).memory.read query = initial.memory.read query := by
  refine ⟨(store_sound initial.memory (initial.registers .rdi)
    ((initial.registers .rsi).setWidth 32) allowed).2, ?_⟩
  intro query outside
  exact writeDWord_frame initial.memory (initial.registers .rdi) query
    ((initial.registers .rsi).setWidth 32) outside

end EDSL.Examples.Compiler.MemoryOps
