/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.CFGTransport
import EDSL.X86.Sequential.Literals
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.SequentialByteComparison
open X86 X86.Sequential

private def entry (bytes : List Byte) (registers : Register → Word := fun _ => 8192)
    (data : Word → Option Byte := fun _ => none) : State where
  registers := registers
  rip := 4096
  flags := 0x602
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length
      then bytes[address.toNat - 4096]? else data address
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length)
    writable := fun _ => false }

private def observe (state : State) (af : Bool := false) :
    Except Error (Word × Word × List Read) := do
  let observation ← Sequential.step af state
  match observation.result with
  | .next final => return (final.flags, final.rip, observation.reads)
  | _ => throw .unexpectedReturn

private def byteInput (value : Byte) (address : Word) : Option Byte :=
  if address = 8192 then some value else none

/-- Independent boundary vectors: unsigned borrow, byte signed overflow,
nibble borrow, zero, sign, and low-byte parity. Using wider subtraction,
reversing operands, sign-extending the immediate, or retaining stale flags fails. -/
theorem subtraction_boundaries :
    ([(0,1), (0x80,1), (0x7f,0xff), (0xff,0xff), (0,0x80), (0x10,1)] :
      List (Byte × Byte)).map (fun (left,right) =>
        observe (entry [0x80,0x3f,right] (data := byteInput left))) =
    [.ok (0x697,4099,[⟨.data,8192,1⟩]), .ok (0xe12,4099,[⟨.data,8192,1⟩]),
     .ok (0xe83,4099,[⟨.data,8192,1⟩]), .ok (0x646,4099,[⟨.data,8192,1⟩]),
     .ok (0xe83,4099,[⟨.data,8192,1⟩]), .ok (0x616,4099,[⟨.data,8192,1⟩])] := by rfl

/-- Only one byte is mapped, at the final canonical address. A wider load
would cross the canonical boundary and fault. Neither write nor execute access
is needed for this DATA1 operand. -/
theorem final_canonical_byte (af : Bool) :
    observe (entry [0x80,0x3f,1] (fun _ => 0x7fffffffffff)
      (fun address => if address = 0x7fffffffffff then some 0x80 else none)) af =
    .ok (0xe12,4099,[⟨.data,0x7fffffffffff,1⟩]) := by rfl

/-- Full-width address inputs and scale eight matter; only the high computed
address is mapped. Both the SIB byte and following immediate must be consumed. -/
theorem high_scaled_address :
    observe (entry [0x80,0x3c,0xcf,0xff] (fun register =>
      if register = .rdi then 0x200000000 else 0x100000001)
      (fun address => if address = 0xa00000008 then some 0x7f else none)) =
    .ok (0xe83,4100,[⟨.data,0xa00000008,1⟩]) := by rfl

theorem base_index_alias :
    observe (entry [0x80,0x3c,0x7f,0] (fun _ => 4096)
      (fun address => if address = 12288 then some 0xff else none)) =
    .ok (0x686,4100,[⟨.data,12288,1⟩]) := by rfl

/-- Fetch faults identify the first missing encoded byte. A readable immediate
without execute permission cannot be silently taken from RAM. -/
theorem missing_encoded_bytes :
    ([[0x80], [0x80,0x3f], [0x80,0x3c], [0x80,0x3c,0x17]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error (.inaccessibleInstruction 4097), .error (.inaccessibleInstruction 4098),
     .error (.inaccessibleInstruction 4098), .error (.inaccessibleInstruction 4099)] := by rfl

theorem immediate_execute_permission :
    let initial := entry [0x80,0x3c,0x17,0]
    Sequential.decodeAt { initial with memory := { initial.memory with
      executable := fun address => address != 4099 } } =
      .error (.inaccessibleInstruction 4099) := by rfl

theorem actual_data_faults :
    (observe (entry [0x80,0x3f,0]),
      observe (entry [0x80,0x3f,0] (fun _ => 0x800000000000) (fun _ => some 0))) =
    (.error (.inaccessibleData 8192), .error (.inaccessibleData 0x800000000000)) := by rfl

/-- Unsupported families never become a weaker addressing or width contract.
The old decoder continues to reject CMP8; the sequential profile rejects
unprefixed AH sources rather than treating them as low SPL. -/
theorem unsupported_forms :
    ([[0x80,0x07,0], [0x80,0xff,0], [0x80,0x7f,0,0], [0x80,0x3d,0,0,0,0,0],
      [0x80,0x3c,0x27,0], [0x80,0x3c,0x05,0], [0x66,0x80,0x3f,0],
      [0x40,0x80,0x3f,0], [0x48,0x80,0x3f,0]] : List (List Byte)).all
      (fun bytes => match Sequential.decodeAt (entry bytes) with
        | .error .unsupportedEncoding => true | _ => false) = true ∧
    Sequential.decodeAt (entry [0x38,0x27]) = .error .unsupportedEncoding ∧
    X86.decodeAt (entry [0x80,0x3f,0]) = .error (.unsupportedOpcode 0x80) := by
  exact ⟨rfl, rfl, rfl⟩

def nop9 : List Byte := [0x66,0x0f,0x1f,0x84,0,0,0,0,0]

theorem nine_byte_nop (af : Bool) :
    observe (entry nop9 (fun _ => 0x800000000000)) af = .ok (0x602,4105,[]) := by rfl

/-- Every truncation and every execute-permission hole, including offsets5..8,
is rejected at that byte. This catches accidental five-byte transport/fetch. -/
theorem nop9_full_fetch :
    (List.range 9).map (fun count => Sequential.decodeAt (entry (nop9.take count))) =
      (List.range 9).map (fun count => .error (.inaccessibleInstruction (4096 + BitVec.ofNat 64 count))) ∧
    (List.range 9).map (fun offset =>
      let initial := entry nop9
      Sequential.decodeAt { initial with memory := { initial.memory with
        executable := fun address => address != 4096 + BitVec.ofNat 64 offset } }) =
      (List.range 9).map (fun offset => .error (.inaccessibleInstruction (4096 + BitVec.ofNat 64 offset))) := by
  exact ⟨rfl, rfl⟩

theorem nop9_exact_suffix :
    ([2,3,4,5,6,7,8] : List Nat).all (fun offset =>
      match Sequential.decodeAt (entry (nop9.set offset 1)) with
      | .error .unsupportedEncoding => true | _ => false) = true ∧
    (Sequential.decodeAt (entry [0x66,0x66,0x0f,0x1f,0x84,0,0,0,0,0])).isOk = false ∧
    (Sequential.decodeAt (entry [0x0f,0x1f,0x84,0,0,0,0,0])).isOk = false := by
  exact ⟨rfl, rfl, rfl⟩

theorem nop9_current_code (state : State) (code : CodeAt state.memory state.rip nop9) :
    Sequential.decodeAt state = .ok (.nop .nine) := by
  apply decodeAt_transport
    (code_fetch_transport code (by decide) 0 (by decide) state rfl (by simp))
  rfl

/-- CFG edges must target instruction starts, including after all nine bytes.
The finite padding instruction does not grant an edge into its suffix. -/
theorem nop9_cfg_edges :
    ((CFG.discover (nop9 ++ [0xc3])).isSome,
      (CFG.discover ([0xeb,7] ++ nop9 ++ [0xc3])).isSome) = (true,false) := by decide

/-- Exact frozen file slices (GCC VA402f60/35, Clang VA4014a0/34).
These are discovery regressions only, with no functional scan certificate. -/
def gcc35 : List Byte :=
  [0xf3,0x0f,0x1e,0xfa,0x48,0x89,0xf0,0x31,0xd2,0x48,0x85,0xf6,0x75,0x0b,0xc3,0x90,
   0x48,0x83,0xc2,1,0x48,0x39,0xd0,0x74,9,0x80,0x3c,0x17,0,0x75,0xf1,0x48,0x89,0xd0,0xc3]

def clang34 : List Byte :=
  [0x31,0xc0,0x48,0x85,0xf6,0x74,0x1a,0x66,0x0f,0x1f,0x84,0,0,0,0,0,
   0x80,0x3c,7,0,0x74,0x0b,0x48,0xff,0xc0,0x48,0x39,0xc6,0x75,0xf2,0x48,0x89,0xf0,0xc3]

theorem unchanged_windows_discover :
    ((CFG.analyze gcc35).map (fun graph => graph.nodes.map (·.offset)),
      (CFG.analyze clang34).map (fun graph => graph.nodes.map (·.offset))) =
    (.ok [0,4,7,9,12,14,15,16,20,23,25,29,31,34],
     .ok [0,2,5,7,16,20,22,25,28,30,33]) := by rfl

end EDSL.Tests.SequentialByteComparison

#audit_edsl
