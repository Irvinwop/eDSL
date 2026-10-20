/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Execution

namespace EDSL.Examples.Compiler.FetchAdd
open X86

def bytes : List Byte := [0x89, 0xf0, 0xf0, 0x0f, 0xc1, 0x07, 0xc3]

def event (initial : State) (old : BitVec 32) : AtomicEvent :=
  ⟨initial.registers .rdi, old, old + (initial.registers .rsi).setWidth 32⟩

def prepared (initial : State) : State := executeMovEaxEsi initial

def exchanged (initial : State) (old : BitVec 32) : State :=
  { initial with
    registers := fun register => if register = .rax then old.setWidth 64 else initial.registers register
    rip := initial.rip + 6
    flags := addFlags32 initial.flags old ((initial.registers .rsi).setWidth 32)
    memory := writeDWordUnchecked initial.memory (initial.registers .rdi) (old + (initial.registers .rsi).setWidth 32) }

def finalState (initial : State) (old : BitVec 32) (returnAddress : Word) : State :=
  { initial with
    registers := fun register => if register = .rsp then initial.registers .rsp + 8
      else if register = .rax then old.setWidth 64 else initial.registers register
    rip := returnAddress
    flags := addFlags32 initial.flags old ((initial.registers .rsi).setWidth 32)
    memory := writeDWordUnchecked initial.memory (initial.registers .rdi) (old + (initial.registers .rsi).setWidth 32) }

/-- Exact compiler bytes with one labeled indivisible fetch-add between MOV and
RET. The modeled platform is ordinary RAM; physical WB/translation/ordering
conformance and code/stack stability remain environmental obligations. -/
theorem atomic_execution (initial : State) (old : BitVec 32) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip bytes)
    (supported : atomicAddressable (initial.registers .rdi) = true)
    (allowed : canStoreDWord initial.memory (initial.registers .rdi) = true)
    (data : loadDWord initial.memory (initial.registers .rdi) = .ok old)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip bytes.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    AtomicExecutes initial (finalState initial old returnAddress) 3 [event initial old] := by
  have b0 := code.2 0 0x89 (by decide)
  have b1 := code.2 1 0xf0 (by decide)
  have b2 := code.2 2 0xf0 (by decide)
  have b3 := code.2 3 0x0f (by decide)
  have b4 := code.2 4 0xc1 (by decide)
  have b5 := code.2 5 0x07 (by decide)
  have first : step initial = .ok (.next (prepared initial)) := by
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1
    simp [step, decodeAt, b0, b1, prepared]
  have exchange := fetchAddDWord_success initial.memory (initial.registers .rdi) old
    ((initial.registers .rsi).setWidth 32) supported allowed data
  have second : step (prepared initial) = .ok (.atomic (event initial old) (exchanged initial old)) := by
    simp only [BitVec.ofNat_eq_ofNat] at b2 b3 b4 b5
    simp [step, decodeAt, prepared, executeMovEaxEsi, State.writeRegister, b2,
      BitVec.add_assoc, b3, b4, b5, executeFetchAdd,
      exchange, event, exchanged]
    funext register
    by_cases same : register = .rax <;> simp [same]
  have codeAfter := writeDWord_preserves_code initial.memory (initial.registers .rdi) initial.rip
    (old + (initial.registers .rsi).setWidth 32) bytes code codeDisjoint
  have retByte := codeAfter.2 6 0xc3 (by decide)
  have stackAfter := (readWord_congr _ _ _ (writeDWord_agrees initial.memory (initial.registers .rdi)
    (initial.registers .rsp) (old + (initial.registers .rsi).setWidth 32) 8 stackDisjoint)).trans stack
  have third : step (exchanged initial old) = .ok (.returned (finalState initial old returnAddress)) := by
    simp only [BitVec.ofNat_eq_ofNat] at retByte
    simp [step, decodeAt, exchanged, retByte, executeRet, stackAfter, returnValid,
      State.writeRegister, finalState]
  exact .next first (.atomic second (.ret third))

theorem correct (initial : State) (old : BitVec 32) (returnAddress : Word)
    (code : CodeAt initial.memory initial.rip bytes)
    (supported : atomicAddressable (initial.registers .rdi) = true)
    (allowed : canStoreDWord initial.memory (initial.registers .rdi) = true)
    (data : loadDWord initial.memory (initial.registers .rdi) = .ok old)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip bytes.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    AtomicExecutes initial (finalState initial old returnAddress) 3 [event initial old] ∧
    Executes initial (finalState initial old returnAddress) 3 ∧ ¬ Diverges initial ∧
    ∀ final count, Executes initial final count → final = finalState initial old returnAddress ∧ count = 3 := by
  have trace := atomic_execution initial old returnAddress code supported allowed data codeDisjoint stackDisjoint stack returnValid
  have execution := trace.executes
  exact ⟨trace, execution, execution.no_divergence, fun _ _ other => other.deterministic execution⟩

theorem value_and_frame (initial : State) (old : BitVec 32) (returnAddress : Word)
    (allowed : canStoreDWord initial.memory (initial.registers .rdi) = true) :
    (finalState initial old returnAddress).registers .rax = old.setWidth 64 ∧
    (finalState initial old returnAddress).flags = addFlags32 initial.flags old ((initial.registers .rsi).setWidth 32) ∧
    loadDWord (finalState initial old returnAddress).memory (initial.registers .rdi) =
      .ok (old + (initial.registers .rsi).setWidth 32) ∧
    ∀ query, 4 ≤ (query - initial.registers .rdi).toNat →
      (finalState initial old returnAddress).memory.read query = initial.memory.read query := by
  exact ⟨by simp [finalState], rfl, (store_sound _ _ _ allowed).2,
    fun query outside => writeDWord_frame _ _ query _ outside⟩

end EDSL.Examples.Compiler.FetchAdd
