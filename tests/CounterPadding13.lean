/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ByteComparePadding
import EDSL.X86.Sequential.Literals
import EDSL.X86.CallReturn.DecodeTransport
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.CounterPadding13
open X86 X86.Sequential

deriving instance DecidableEq for Except

/-- Independent assembler byte windows, never obtained from the NOP encoder. -/
private def padding13 : List Byte :=
  [0x66,0x66,0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0]

private def padding15 : List Byte :=
  [0x66,0x66,0x66,0x66,0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0]

private def entry (bytes : List Byte) (registers : Register → Word := fun _ => 8192) : State where
  registers := registers
  rip := 4096
  flags := 0xdeadbeef00000ed7
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length
      then bytes[address.toNat - 4096]? else none
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length)
    writable := fun address => address == 0x9000 }

private def denyExecute (before : State) (offset : Nat) : State :=
  { before with
    memory := { before.memory with
      executable := fun address =>
        before.memory.executable address && address != 4096 + BitVec.ofNat 64 offset } }

private def removeByte (before : State) (offset : Nat) : State :=
  { before with
    memory := { before.memory with
      read := fun address =>
        if address = 4096 + BitVec.ofNat 64 offset then none else before.memory.read address } }

private def faultsAt (before : State) (expected : Word) : Bool :=
  match Sequential.decodeAt before with
  | .error (.inaccessibleInstruction address) => address == expected
  | _ => false

private def unsupported (before : State) : Bool :=
  match Sequential.decodeAt before with
  | .error .unsupportedEncoding => true
  | _ => false

private def rejects (bytes : List Byte) : Bool := !(Sequential.decodeAt (entry bytes)).isOk

private theorem entry13_base_decoded :
    Sequential.decodeAt (entry padding13) = .ok (.nop .thirteen) := by
  decide +kernel

private theorem entry13_decoded (registers : Register → Word) :
    Sequential.decodeAt (entry padding13 registers) = .ok (.nop .thirteen) := by
  apply decodeAt_transport (source := entry padding13)
  · intro offset bound byte fetched
    exact fetched
  · exact entry13_base_decoded

private theorem entry15_decoded :
    Sequential.decodeAt (entry padding15) = .ok (.nop .fifteen) := by
  decide +kernel

private theorem tail13_decoded (following : Byte) :
    Sequential.decodeAt (denyExecute (entry (padding13 ++ [following])) 13) =
      .ok (.nop .thirteen) := by
  decide +kernel +revert

/-- The production decoder and literal emitter consume an independent window;
the exact old long form still decodes and advances by fifteen. -/
theorem decode_emit_and_preserve15 (choice : Bool) :
    Sequential.decodeAt (entry padding13) = .ok (.nop .thirteen) ∧
    (Sequential.decodeAt (entry padding13)).map Literals.instruction = .ok "(.nop .thirteen)" ∧
    Sequential.decodeAt (entry padding15) = .ok (.nop .fifteen) ∧
    Sequential.step choice (entry padding15) =
      .ok ⟨.next { entry padding15 with rip := 4111 },[]⟩ := by
  refine ⟨entry13_decoded _, ?_, entry15_decoded, ?_⟩
  · rw [entry13_decoded]
    rfl
  · exact (step_eq_execute choice entry15_decoded).trans
      (execute_nop (entry padding15) .fifteen choice)

/-- Actual decode/step at any authenticated code address, with arbitrary flags,
all registers, RAM and both permission maps, not a projection of the final state.
The expected +13 and the input window are independent of the encoding tag. -/
theorem arbitrary_state_frame (before : State)
    (code : CodeAt before.memory before.rip padding13) (choice : Bool) :
    Sequential.step choice before = .ok ⟨.next { before with rip := before.rip + 13 },[]⟩ := by
  exact step_nop13_context before code choice

/-- Each of the thirteen bytes must be present and executable. Removing a byte
while retaining execute permission separates missing RAM from permission denial. -/
theorem every_required_byte :
    (List.range 13).all (fun offset =>
      faultsAt (entry (padding13.take offset)) (4096 + BitVec.ofNat 64 offset) &&
      faultsAt (denyExecute (entry padding13) offset) (4096 + BitVec.ofNat 64 offset) &&
      faultsAt (removeByte (entry padding13) offset) (4096 + BitVec.ofNat 64 offset)) = true := by
  decide +kernel

/-- A fetched mismatch wins before a later fetch fault at every suffix byte in
both long forms. Conversely a required unreadable byte wins before comparing it
or a later malformed byte. These assertions exercise public decoder ordering. -/
theorem required_fetch_order :
    (List.range 12).all (fun offset =>
      let index := offset + 1
      unsupported (denyExecute (entry (padding13.set index (padding13[index]! ^^^ 1)))
        (index + 1))) = true ∧
    (List.range 14).all (fun offset =>
      let index := offset + 1
      unsupported (denyExecute (entry (padding15.set index (padding15[index]! ^^^ 1)))
        (index + 1))) = true ∧
    (List.range 13).all (fun offset =>
      faultsAt (denyExecute (entry (padding13.set offset (padding13[offset]! ^^^ 1))) offset)
        (4096 + BitVec.ofNat 64 offset) &&
      faultsAt (denyExecute (entry (padding13.set (offset + 1) 1)) offset)
        (4096 + BitVec.ofNat 64 offset)) = true := by
  decide +kernel

/-- A low-bit flip at each byte and extra, missing or reordered prefixes reject;
the adjacent fourteen-byte assembler form is deliberately not on the list. -/
theorem malformed_and_unlisted :
    (List.range 13).all (fun index => rejects (padding13.set index (padding13[index]! ^^^ 1))) = true ∧
    ([0x66 :: padding13, 0x66 :: padding15, 0x2e :: padding13, 0x67 :: padding13,
      0xf0 :: padding13, 0xf2 :: padding13, 0xf3 :: padding13, 0x40 :: padding13,
      0x48 :: padding13,
      [0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0],
      [0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0],
      [0x66,0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0],
      [0x66,0x66,0x66,0x66,0x0f,0x1f,0x84,0,0,0,0,0],
      [0x66,0x66,0x66,0x2e,0x66,0x0f,0x1f,0x84,0,0,0,0,0],
      padding13.set 4 0x66, padding13.set 7 0x8c] : List (List Byte)).all rejects = true := by
  decide +kernel

/-- Byte14 is present but nonexecutable, with arbitrary contents. Neither
Sequential nor CallReturn may demand it to retire the complete thirteen bytes. -/
theorem no_following_byte_fetch (following : Byte) (choice : Bool) :
    let before := denyExecute (entry (padding13 ++ [following])) 13
    fetchByte before.memory 4109 = .error (.inaccessibleInstruction 4109) ∧
    Sequential.step choice before = .ok ⟨.next { before with rip := 4109 },[]⟩ ∧
    CallReturn.rawStep choice before = .ok ⟨.next { before with rip := 4109 },[]⟩ := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · exact (step_eq_execute choice (tail13_decoded following)).trans
      (execute_nop _ .thirteen choice)
  · exact (CallReturn.rawStep_eq_execute choice
      (CallReturn.decodeAt_sequential_lift (tail13_decoded following))).trans
      ((CallReturn.execute_liftSequential _ (.nop .thirteen) choice).trans
        (execute_nop _ .thirteen choice))

/-- The apparent RAX+RAX operand points first to absent canonical RAM, then to
a noncanonical address. The real DATA primitive fails, while NOP13 still retires
without an operand read or any register/flag/memory change. -/
theorem no_operand_memory_access (choice : Bool) :
    (let before := entry padding13
     readDataByte before.memory 16384 = .error (.inaccessibleData 16384) ∧
     Sequential.step choice before = .ok ⟨.next { before with rip := 4109 },[]⟩) ∧
    (let before := entry padding13 (fun _ => 0x400000000000)
     readDataByte before.memory 0x800000000000 = .error (.inaccessibleData 0x800000000000) ∧
     Sequential.step choice before = .ok ⟨.next { before with rip := 4109 },[]⟩) := by
  refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩
  · exact (step_eq_execute choice (entry13_decoded _)).trans
      (execute_nop _ .thirteen choice)
  · exact (step_eq_execute choice (entry13_decoded _)).trans
      (execute_nop _ .thirteen choice)

/-- Nine preserved bytes do not authenticate the final displacement of NOP13.
The shared transport must retain its existing fifteen-byte success extent. -/
theorem nine_byte_transport_insufficient :
    SuccessfulFetchTransportWithin 9 (codeState padding13 0) (codeState (padding13.set 12 1) 0) ∧
    Sequential.decodeAt (codeState padding13 0) = .ok (.nop .thirteen) ∧
    Sequential.decodeAt (codeState (padding13.set 12 1) 0) = .error .unsupportedEncoding := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  have same : ∀ offset : Fin 9,
      fetchByte (codeState padding13 0).memory (BitVec.ofNat 64 offset.val) =
        fetchByte (codeState (padding13.set 12 1) 0).memory (BitVec.ofNat 64 offset.val) := by
    decide +kernel
  intro offset bound byte fetched
  simp only [codeState, BitVec.zero_add] at fetched ⊢
  have equal := same ⟨offset,bound⟩
  change fetchByte (codeMemory padding13) (BitVec.ofNat 64 offset) =
    fetchByte (codeMemory (padding13.set 12 1)) (BitVec.ofNat 64 offset) at equal
  exact equal.symm.trans fetched

/-- Whole-window discovery treats NOP13 as one instruction and forbids an edge
into its final displacement byte, using the existing default profile. -/
theorem cfg_instruction_boundaries :
    (CFG.discover (padding13 ++ [0xc3])).isSome = true ∧
    (CFG.discover ([0xeb,12] ++ padding13 ++ [0xc3])).isSome = false := by
  decide +kernel

end EDSL.Tests.CounterPadding13

#print axioms EDSL.X86.Sequential.step_nop13_context
#print axioms EDSL.X86.Sequential.NopEncoding.decode_bytes
#print axioms EDSL.X86.Sequential.decodeAt_transport
#print axioms EDSL.Tests.CounterPadding13.arbitrary_state_frame
#audit_edsl
