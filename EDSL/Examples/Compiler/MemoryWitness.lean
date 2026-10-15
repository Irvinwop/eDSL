/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Compiler.MemoryOps

namespace EDSL.Examples.Compiler.MemoryOps
open X86

/-- Separate executable code, return stack and writable data regions. -/
def baseMemory (opcode modrm : Byte) : Memory where
  read address :=
    match address.toNat with
    | 4096 => some opcode
    | 4097 => some modrm
    | 4098 => some 0xc3
    | 32768 => some 0
    | 32769 => some 0x20
    | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some 0
    | 65536 | 65537 | 65538 | 65539 => some 0
    | _ => none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4099)
  writable address := decide (65536 ≤ address.toNat ∧ address.toNat < 65540)

def dataMemory (opcode modrm : Byte) (oldValue : BitVec 32) : Memory :=
  writeDWordUnchecked (baseMemory opcode modrm) 65536 oldValue

theorem base_code (opcode modrm : Byte) :
    CodeAt (baseMemory opcode modrm) 4096 [opcode, modrm, 0xc3] := by
  refine ⟨by change 4096 + 3 ≤ 2^64; decide, ?_⟩
  intro offset byte atOffset
  match offset with
  | 0 | 1 | 2 =>
    simp at atOffset
    subst byte
    rfl
  | n + 3 => simp at atOffset

theorem data_code_disjoint : DWordDisjoint 65536 4096 3 := by
  intro offset bound
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 := by omega
  rcases cases with rfl | rfl | rfl <;> decide

theorem data_stack_disjoint : DWordDisjoint 65536 32768 8 := by
  intro offset bound
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
    offset = 4 ∨ offset = 5 ∨ offset = 6 ∨ offset = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem data_code (opcode modrm : Byte) (oldValue : BitVec 32) :
    CodeAt (dataMemory opcode modrm oldValue) 4096 [opcode, modrm, 0xc3] :=
  writeDWord_preserves_code _ _ _ _ _ (base_code opcode modrm) data_code_disjoint

theorem data_stack (opcode modrm : Byte) (oldValue : BitVec 32) :
    readWord (dataMemory opcode modrm oldValue) 32768 = .ok 8192 := by
  have unchanged := readWord_congr _ _ _ (writeDWord_agrees
    (baseMemory opcode modrm) 65536 32768 oldValue 8 data_stack_disjoint)
  exact unchanged.trans (by rfl)

theorem data_value (opcode modrm : Byte) (oldValue : BitVec 32) :
    loadDWord (dataMemory opcode modrm oldValue) 65536 = .ok oldValue :=
  load_after_write _ _ _ (by decide)

theorem data_writable (opcode modrm : Byte) (oldValue : BitVec 32) :
    canStoreDWord (dataMemory opcode modrm oldValue) 65536 = true := by rfl

def loadEntry (oldValue : BitVec 32) : State where
  registers register := if register = .rdi then 65536
    else if register = .rsp then 32768 else 0
  rip := 4096
  flags := 0x202
  memory := dataMemory 0x8b 0x07 oldValue

def storeEntry (oldValue : BitVec 32) (value : Word) : State where
  registers register := if register = .rdi then 65536
    else if register = .rsp then 32768
    else if register = .rsi then value else 0
  rip := 4096
  flags := 0x202
  memory := dataMemory 0x89 0x37 oldValue

/-- Every possible word value has a satisfiable load-entry contract. -/
theorem every_load_value_executes (oldValue : BitVec 32) :
    Executes (loadEntry oldValue) (loadFinal (loadEntry oldValue) oldValue 8192) 2 := by
  apply (load_correct (loadEntry oldValue) oldValue 8192 ?_ ?_ ?_ (by decide)).1
  · exact data_code _ _ _
  · exact data_value _ _ _
  · exact data_stack _ _ _

/-- Every old word and new 64-bit argument has a satisfiable store contract. -/
theorem every_store_value_executes (oldValue : BitVec 32) (value : Word) :
    Executes (storeEntry oldValue value) (storeFinal (storeEntry oldValue value) 8192) 2 := by
  apply (store_correct (storeEntry oldValue value) 8192 ?_ ?_ ?_ ?_ ?_ (by decide)).1
  · exact data_code _ _ _
  · exact data_writable _ _ _
  · exact data_code_disjoint
  · exact data_stack_disjoint
  · exact data_stack _ _ _

end EDSL.Examples.Compiler.MemoryOps
