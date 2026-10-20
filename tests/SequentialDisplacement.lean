/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Code
import EDSL.X86.CallReturn.Machine
import EDSL.X86.CallReturn.DecodeTransport

set_option autoImplicit false
set_option warningAsError true

open EDSL.X86 EDSL.X86.Sequential

-- Architectural mod01 base5 is RBP/R13, and SIB index4 changes meaning with X.
example : Sequential.decodeAt (codeState [0x48,0x8d,0x45,0x80] 0) =
    .ok (.lea64 .rax (.baseDisp8 .rbp 0x80)) := by rfl
example : Sequential.decodeAt (codeState [0x4d,0x8d,0x45,0xff] 0) =
    .ok (.lea64 .r8 (.baseDisp8 .r13 0xff)) := by rfl
example : Sequential.decodeAt (codeState [0x49,0x8d,0x44,0xa5,0x80] 0) =
    .ok (.lea64 .rax (.sibDisp8 .r13 none 2 0x80)) := by rfl
example : Sequential.decodeAt (codeState [0x4b,0x8d,0x44,0xa5,0x80] 0) =
    .ok (.lea64 .rax (.sibDisp8 .r13 (some .r12) 2 0x80)) := by rfl
example : ([[0x4b,0x8d,0x44,0x05,0], [0x4b,0x8d,0x44,0x45,0],
      [0x4b,0x8d,0x44,0x85,0], [0x4b,0x8d,0x44,0xc5,0]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (codeState bytes 0)) =
    [.ok (.lea64 .rax (.sibDisp8 .r13 (some .r8) 0 0)),
     .ok (.lea64 .rax (.sibDisp8 .r13 (some .r8) 1 0)),
     .ok (.lea64 .rax (.sibDisp8 .r13 (some .r8) 2 0)),
     .ok (.lea64 .rax (.sibDisp8 .r13 (some .r8) 3 0))] := by rfl

-- Equal computed values retain different instruction lengths and SIB syntax.
example : (Sequential.Instruction.lea64 .rax (.base .rdi)).length = 3 ∧
    (Sequential.Instruction.lea64 .rax (.baseDisp8 .rdi 0)).length = 4 ∧
    (Sequential.Instruction.lea64 .rax (.sibDisp8 .rdi none 0 0)).length = 5 := by decide

-- Generic alias/prestate equation; no data mapping or canonicality is assumed.
example (state : State) (destination base index : Register) (scale : Fin 4)
    (displacement : Byte) (af : Bool) :
    ∃ final, execute state (.lea64 destination (.sibDisp8 base (some index) scale displacement)) af =
        .ok ⟨.next final, []⟩ ∧
      final.registers destination = state.registers base + (state.registers index <<< scale.val) +
        displacement.signExtend 64 ∧ final.memory = state.memory ∧ final.flags = state.flags := by
  obtain ⟨final, actual, written, _, memory, flags, _⟩ :=
    execute_lea64_context state destination (.sibDisp8 base (some index) scale displacement) af
  exact ⟨final, actual, written, memory, flags⟩

-- No DATA canonicality check is introduced for a noncanonical result.
private def noncanonical : State :=
  { codeState [0x48,0x8d,0x47,0xff] 0 with registers := fun _ => 0x800000000001 }
example : step false noncanonical =
    .ok ⟨.next { noncanonical.writeRegister .rax 0x800000000000 with rip := 4 }, []⟩ := by rfl

-- Every required displacement/SIB byte must have execute/read permission.
example : Sequential.decodeAt (codeState [0x48,0x8d,0x47] 0) =
    .error (.inaccessibleInstruction 3) := by rfl
example : Sequential.decodeAt (codeState [0x48,0x8d,0x44] 0) =
    .error (.inaccessibleInstruction 3) := by rfl
example : Sequential.decodeAt (codeState [0x48,0x8d,0x44,0x20] 0) =
    .error (.inaccessibleInstruction 4) := by rfl
private def blockedDisplacement : State :=
  let state := codeState [0x48,0x8d,0x47,0xff] 0
  { state with memory := { state.memory with executable := fun address => address != 3 } }
example : Sequential.decodeAt blockedDisplacement = .error (.inaccessibleInstruction 3) := by rfl

private def crossingHole : State where
  registers := fun _ => 0
  rip := 0x7ffffffffffd
  flags := 0
  memory := {
    read := fun address => ([0x48,0x8d,0x47,0xff] : List Byte)[(address - 0x7ffffffffffd).toNat]?
    executable := fun _ => true }
example : Sequential.decodeAt crossingHole = .error (.inaccessibleInstruction 0x800000000000) := by rfl

private def stackAlias : State :=
  { codeState [0x48,0x8d,0x64,0x24,0xff] 0 with registers := fun _ => 0 }
example : step false stackAlias =
    .ok ⟨.next { stackAlias.writeRegister .rsp 0xffffffffffffffff with rip := 5 }, []⟩ := by rfl

-- No indirect extension of the admitted memory subset, widths or disp32.
example : Sequential.decodeAt (codeState [0x48,0x8b,0x47,0xff] 0) = .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (codeState [0x48,0x8d,0x87,0xff,0xff,0xff,0xff] 0) =
    .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (codeState [0x48,0x8d,0xc7] 0) = .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (codeState [0x48,0x8d,0x05,0,0,0,0] 0) = .error .unsupportedEncoding := by rfl

-- The sibling decoder preserves the old identities used by historical clients.
example : CallReturn.decodeAt (codeState [0x4d,0x8d,0x45,0xff] 0) =
    .ok (.leaDisp8 .r8 (.plain .r13) 0xff) := by rfl
example (state : State) (af : Bool) :
    CallReturn.execute state (.leaDisp8 .rax (.plain .rdi) 0xff) af =
      execute state (.lea64 .rax (.baseDisp8 .rdi 0xff)) af := rfl
