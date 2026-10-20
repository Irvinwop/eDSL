/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ByteComparePadding
import EDSL.X86.Sequential.Return
import EDSL.X86.Sequential.Literals
import EDSL.X86.CallReturn.DecodeTransport
import EDSL.X86.VCGen.Frame

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.SequentialByteComparePadding

deriving instance DecidableEq for Except

open X86 X86.Sequential

/-- Independent literal window, not obtained from the NOP encoder. -/
def padding : List Byte := [0x66,0x66,0x66,0x66,0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0]

private def entry (bytes : List Byte) (registers : Register → Word := fun _ => 0x8000000000000001)
    (data : Word → Option Byte := fun _ => none) (flags : Word := 0xdeadbeef00000ed7) : State where
  registers := registers
  rip := 4096
  flags := flags
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length
      then bytes[address.toNat - 4096]? else data address
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + bytes.length)
    writable := fun address => address == 0x9000 }

private def single (address : Word) (value : Byte) : Word → Option Byte :=
  fun query => if query = address then some value else none

private def observe (before : State) (choice : Bool) : Except Error (Word × Word × List Read) := do
  let observation ← Sequential.step choice before
  match observation.result with
  | .next after => return (after.flags,after.rip,observation.reads)
  | _ => throw .unexpectedReturn

/-- Literal architectural flag vectors separate operand order, signed overflow,
byte/nibble borrow, equality, parity and contamination by high register bits.
Incoming flags set arithmetic and nonarithmetic bits, including high reserved bits. -/
theorem flag_vectors (choice : Bool) :
    ([(0x1122334455667700,1), (0xfedcba9876543280,1),
      (0x123456789abcde7f,0xff), (0x80000000000000ff,0xff),
      (0x8888888888888800,0x80), (0x1122334455667710,1),
      (0x1122334455667702,1)] : List (Word × Byte)).map (fun (left,right) =>
        observe (entry [0x3a,0x06] (fun (r : Register) => if r = Register.rax then left else
          if r = Register.rsi then 8192 else 0xaaaa5555ffffabcd) (single 8192 right)) choice) =
    [.ok (0xdeadbeef00000697,4098,[⟨.data,8192,1⟩]),
     .ok (0xdeadbeef00000e12,4098,[⟨.data,8192,1⟩]),
     .ok (0xdeadbeef00000e83,4098,[⟨.data,8192,1⟩]),
     .ok (0xdeadbeef00000646,4098,[⟨.data,8192,1⟩]),
     .ok (0xdeadbeef00000e83,4098,[⟨.data,8192,1⟩]),
     .ok (0xdeadbeef00000616,4098,[⟨.data,8192,1⟩]),
     .ok (0xdeadbeef00000602,4098,[⟨.data,8192,1⟩])] := by rfl

/-- The other frozen form must use R8B minus the memory byte, never reverse
38 /r flags or turn the SIB into a register. Only a single data byte exists. -/
theorem frozen_rex_flags (choice : Bool) :
    observe (entry [0x44,0x3a,4,6] (fun r => match r with
      | .r8 => 0x123456789abcde7f | .rsi => 0x100000001 | .rax => 0x200000002
      | _ => 0xfedcba9876543280) (single 0x300000003 0xff)) choice =
      .ok (0xdeadbeef00000e83,4100,[⟨.data,0x300000003,1⟩]) := by rfl

/-- Every left bank, all REX bit combinations, scales, real RSP bases and R12
indices are independently named. Unprefixed 4..7 are tested as rejections below. -/
theorem decoded_banks_and_addresses :
    ([[0x3a,6],[0x3a,0x0e],[0x3a,0x16],[0x3a,0x1e],
      [0x40,0x3a,6],[0x40,0x3a,0x0e],[0x40,0x3a,0x16],[0x40,0x3a,0x1e],
      [0x40,0x3a,0x26],[0x40,0x3a,0x2e],[0x40,0x3a,0x36],[0x40,0x3a,0x3e],
      [0x44,0x3a,6],[0x44,0x3a,0x0e],[0x44,0x3a,0x16],[0x44,0x3a,0x1e],
      [0x44,0x3a,0x26],[0x44,0x3a,0x2e],[0x44,0x3a,0x36],[0x44,0x3a,0x3e],
      [0x41,0x3a,6],[0x42,0x3a,4,0xa6],[0x43,0x3a,4,0xa6],
      [0x45,0x3a,4,6],[0x46,0x3a,4,0xe4],[0x47,0x3a,4,0xe4],
      [0x3a,4,4],[0x3a,4,0x40],[0x3a,4,0x80],[0x3a,4,0xc0]] : List (List Byte)).map
        (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.ok (.cmpRegMem8 .rax (.base .rsi) false),
     .ok (.cmpRegMem8 .rcx (.base .rsi) false),
     .ok (.cmpRegMem8 .rdx (.base .rsi) false),
     .ok (.cmpRegMem8 .rbx (.base .rsi) false),
     .ok (.cmpRegMem8 .rax (.base .rsi) true),
     .ok (.cmpRegMem8 .rcx (.base .rsi) true),
     .ok (.cmpRegMem8 .rdx (.base .rsi) true),
     .ok (.cmpRegMem8 .rbx (.base .rsi) true),
     .ok (.cmpRegMem8 .rsp (.base .rsi) true),
     .ok (.cmpRegMem8 .rbp (.base .rsi) true),
     .ok (.cmpRegMem8 .rsi (.base .rsi) true),
     .ok (.cmpRegMem8 .rdi (.base .rsi) true),
     .ok (.cmpRegMem8 .r8 (.base .rsi) true),
     .ok (.cmpRegMem8 .r9 (.base .rsi) true),
     .ok (.cmpRegMem8 .r10 (.base .rsi) true),
     .ok (.cmpRegMem8 .r11 (.base .rsi) true),
     .ok (.cmpRegMem8 .r12 (.base .rsi) true),
     .ok (.cmpRegMem8 .r13 (.base .rsi) true),
     .ok (.cmpRegMem8 .r14 (.base .rsi) true),
     .ok (.cmpRegMem8 .r15 (.base .rsi) true),
     .ok (.cmpRegMem8 .rax (.base .r14) true),
     .ok (.cmpRegMem8 .rax (.indexed .rsi .r12 2) true),
     .ok (.cmpRegMem8 .rax (.indexed .r14 .r12 2) true),
     .ok (.cmpRegMem8 .r8 (.indexed .r14 .rax 0) true),
     .ok (.cmpRegMem8 .r8 (.indexed .rsp .r12 3) true),
     .ok (.cmpRegMem8 .r8 (.indexed .r12 .r12 3) true),
     .ok (.cmpRegMem8 .rax (.indexed .rsp .rax 0) false),
     .ok (.cmpRegMem8 .rax (.indexed .rax .rax 1) false),
     .ok (.cmpRegMem8 .rax (.indexed .rax .rax 2) false),
     .ok (.cmpRegMem8 .rax (.indexed .rax .rax 3) false)] := by rfl

/-- Actual execution uses the old full64 address when all operands alias, RSP
is the left byte, and REX.B/X choose the same high register as base and index. -/
theorem aliases_and_final_data_byte (choice : Bool) :
    observe (entry [0x3a,4,0] (fun _ => 0x100000001) (single 0x200000002 2)) choice =
      .ok (0xdeadbeef00000697,4099,[⟨.data,0x200000002,1⟩]) ∧
    observe (entry [0x40,0x3a,0x24,0] (fun _ => 0x100000001) (single 0x200000002 0)) choice =
      .ok (0xdeadbeef00000602,4100,[⟨.data,0x200000002,1⟩]) ∧
    observe (entry [0x47,0x3a,0x24,0xe4] (fun _ => 0x100000001)
      (single 0x900000009 2)) choice =
      .ok (0xdeadbeef00000697,4100,[⟨.data,0x900000009,1⟩]) ∧
    observe (entry [0x3a,0x06] (fun _ => 0x7fffffffffff)
      (single 0x7fffffffffff 0xff)) choice =
      .ok (0xdeadbeef00000646,4098,[⟨.data,0x7fffffffffff,1⟩]) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Plain bases and SIB indices cover every accepted bank code. RBP/R13
plain and RSP index are absent from this mod00 subset, rather than remapped. -/
theorem decoded_base_index_banks :
    ([[0x3a,0],[0x3a,1],[0x3a,2],[0x3a,3],[0x3a,6],[0x3a,7],
      [0x41,0x3a,0],[0x41,0x3a,1],[0x41,0x3a,2],[0x41,0x3a,3],
      [0x41,0x3a,6],[0x41,0x3a,7]] : List (List Byte)).map
        (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.ok (.cmpRegMem8 .rax (.base .rax) false),.ok (.cmpRegMem8 .rax (.base .rcx) false),
     .ok (.cmpRegMem8 .rax (.base .rdx) false),.ok (.cmpRegMem8 .rax (.base .rbx) false),
     .ok (.cmpRegMem8 .rax (.base .rsi) false),.ok (.cmpRegMem8 .rax (.base .rdi) false),
     .ok (.cmpRegMem8 .rax (.base .r8) true),.ok (.cmpRegMem8 .rax (.base .r9) true),
     .ok (.cmpRegMem8 .rax (.base .r10) true),.ok (.cmpRegMem8 .rax (.base .r11) true),
     .ok (.cmpRegMem8 .rax (.base .r14) true),.ok (.cmpRegMem8 .rax (.base .r15) true)] ∧
    ([[0x3a,4,0],[0x3a,4,8],[0x3a,4,0x10],[0x3a,4,0x18],
      [0x3a,4,0x28],[0x3a,4,0x30],[0x3a,4,0x38],
      [0x42,0x3a,4,0],[0x42,0x3a,4,8],[0x42,0x3a,4,0x10],[0x42,0x3a,4,0x18],
      [0x42,0x3a,4,0x20],[0x42,0x3a,4,0x28],[0x42,0x3a,4,0x30],[0x42,0x3a,4,0x38]] :
        List (List Byte)).map (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.ok (.cmpRegMem8 .rax (.indexed .rax .rax 0) false),
     .ok (.cmpRegMem8 .rax (.indexed .rax .rcx 0) false),
     .ok (.cmpRegMem8 .rax (.indexed .rax .rdx 0) false),
     .ok (.cmpRegMem8 .rax (.indexed .rax .rbx 0) false),
     .ok (.cmpRegMem8 .rax (.indexed .rax .rbp 0) false),
     .ok (.cmpRegMem8 .rax (.indexed .rax .rsi 0) false),
     .ok (.cmpRegMem8 .rax (.indexed .rax .rdi 0) false),
     .ok (.cmpRegMem8 .rax (.indexed .rax .r8 0) true),
     .ok (.cmpRegMem8 .rax (.indexed .rax .r9 0) true),
     .ok (.cmpRegMem8 .rax (.indexed .rax .r10 0) true),
     .ok (.cmpRegMem8 .rax (.indexed .rax .r11 0) true),
     .ok (.cmpRegMem8 .rax (.indexed .rax .r12 0) true),
     .ok (.cmpRegMem8 .rax (.indexed .rax .r13 0) true),
     .ok (.cmpRegMem8 .rax (.indexed .rax .r14 0) true),
     .ok (.cmpRegMem8 .rax (.indexed .rax .r15 0) true)] := by exact ⟨rfl,rfl⟩

/-- Every general register and every Memory field are framed by the real step,
without a finite projection which could hide an unwanted GPR/permission write. -/
theorem full_context (choice : Bool) :
    let before := entry [0x44,0x3a,4,6]
      (fun r => if r = .rsi then 8192 else if r = .rax then 1 else 0x123456789abcde80)
      (single 8193 1)
    Sequential.step choice before = .ok ⟨.next { before with
      rip := 4100, flags := 0xdeadbeef00000e12 },[⟨.data,8193,1⟩]⟩ := by rfl

private theorem padding_code : CodeAt (entry padding).memory 4096 padding :=
  ELF.checkCode_sound _ _ _ (by decide +kernel)

theorem nop15_full_context (registers : Register → Word) (flags : Word) (choice : Bool) :
    let before := entry padding registers (fun _ => none) flags
    Sequential.step choice before = .ok ⟨.next { before with rip := 4111 },[]⟩ := by
  dsimp only
  have code : CodeAt (entry padding registers (fun _ => none) flags).memory 4096 padding :=
    padding_code
  have fetched := code_fetch_transport_of_bound code (by decide) 0 (by decide)
    (entry padding registers (fun _ => none) flags) rfl (by rfl)
  have decoded := decodeAt_transport fetched (NopEncoding.decode_bytes .fifteen)
  rw [step_eq_execute choice decoded]
  rfl

theorem old_nop_family (choice : Bool) :
    ([[0x90],[0x66,0x90],[0x0f,0x1f,0],[0x0f,0x1f,0x40,0],
      [0x0f,0x1f,0x44,0,0],[0x66,0x0f,0x1f,0x44,0,0],
      [0x66,0x0f,0x1f,0x84,0,0,0,0,0]] : List (List Byte)).map
        (fun bytes => observe (entry bytes) choice) =
    [.ok (0xdeadbeef00000ed7,4097,[]),.ok (0xdeadbeef00000ed7,4098,[]),
     .ok (0xdeadbeef00000ed7,4099,[]),.ok (0xdeadbeef00000ed7,4100,[]),
     .ok (0xdeadbeef00000ed7,4101,[]),.ok (0xdeadbeef00000ed7,4102,[]),
     .ok (0xdeadbeef00000ed7,4105,[])] := by rfl

/-- Complete original unprefixed low-bank MOV32 immediates through the shared
legacy semantics. Literal high-bit and mixed-endian values distinguish zero
extension, byte order, exact destination, full flags/memory frame and length. -/
theorem mov32_completion_context (choice : Bool) :
    (let before := entry [0xb9,0x78,0x56,0x34,0x12]
     Sequential.step choice before =
       .ok ⟨.next { before.writeRegister .rcx 0x12345678 with rip := 4101 },[]⟩) ∧
    (let before := entry [0xbb,0x80,0xff,0xff,0xff]
     Sequential.step choice before =
       .ok ⟨.next { before.writeRegister .rbx 0xffffff80 with rip := 4101 },[]⟩) ∧
    (let before := entry [0xbc,0xff,0xff,0xff,0xff]
     Sequential.step choice before =
       .ok ⟨.next { before.writeRegister .rsp 0xffffffff with rip := 4101 },[]⟩) ∧
    (let before := entry [0xbd,0,0,0,0x80]
     Sequential.step choice before =
       .ok ⟨.next { before.writeRegister .rbp 0x80000000 with rip := 4101 },[]⟩) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

private def faultAt (bytes : List Byte) (boundary : Nat) (executeDenied : Bool) : Bool :=
  let before := entry (if executeDenied then bytes else bytes.take boundary)
  let denied := if executeDenied then { before with memory := { before.memory with
    executable := fun address => before.memory.executable address &&
      address != 4096 + BitVec.ofNat 64 boundary } } else before
  match Sequential.decodeAt denied with
  | .error (.inaccessibleInstruction address) => address == 4096 + BitVec.ofNat 64 boundary
  | _ => false

/-- Every required byte, including offset14, must be present and executable;
these complete windows have no accessible byte after their last byte. -/
theorem every_fetch_boundary :
    ([padding,[0x3a,6],[0x3a,4,6],[0x44,0x3a,6],[0x44,0x3a,4,6],
      [0x47,0x3a,4,0xe4],[0xb9,1,0,0,0],[0xbb,1,0,0,0],
      [0xbc,1,0,0,0],[0xbd,1,0,0,0]] : List (List Byte)).all (fun bytes =>
        (List.range bytes.length).all (fun boundary =>
          faultAt bytes boundary false && faultAt bytes boundary true)) = true := by decide +kernel

private def rejects (bytes : List Byte) : Bool := !(Sequential.decodeAt (entry bytes)).isOk

theorem mov32_completion_prefix_rejections :
    ([[0x40,0xb9,1,0,0,0],[0x48,0xb9,1,0,0,0,0,0,0,0],
      [0x66,0xb9,1,0],[0x67,0xb9,1,0,0,0],[0xf0,0xb9,1,0,0,0]] :
      List (List Byte)).all rejects = true := by decide +kernel

theorem padding_mutations :
    (List.range 15).all (fun index => rejects (padding.set index (padding[index]! ^^^ 1))) = true ∧
    ([0x66 :: padding,0x2e :: padding,0xf0 :: padding,0x40 :: padding,
      [0x66,0x66,0x90],[0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0],
      [0x0f,0x1f,0x80,0,0,0,0],[0x66,0x0f,0x1f,0x84,0,0,0,0,1]] :
        List (List Byte)).all rejects = true := by decide +kernel

theorem cmp_rejections :
    ([[0x3a,0x26],[0x3a,0x2e],[0x3a,0x36],[0x3a,0x3e],
      [0x3a,0x46,0],[0x44,0x3a,0x46,0],[0x3a,0x86,0,0,0,0],
      [0x3a,5,0,0,0,0],[0x41,0x3a,5,0,0,0,0],
      [0x3a,4,0x24],[0x40,0x3a,4,0x24],[0x41,0x3a,4,0x24],
      [0x3a,4,5,0,0,0,0],[0x43,0x3a,4,5,0,0,0,0],
      [0x48,0x3a,6],[0x4f,0x3a,6],[0x66,0x3a,6],[0x67,0x3a,6],
      [0xf0,0x3a,6],[0xf2,0x3a,6],[0xf3,0x3a,6],[0x2e,0x3a,6],
      [0x40,0x44,0x3a,6],[0x44,0x40,0x3a,6],
      [0x40,0x38,6],[0x44,0x38,4,6]] : List (List Byte)).all rejects = true := by decide +kernel

/-- Changing direction changes the flags; mod3 stays the existing register
family, and changing the left field changes the actual prestate source. -/
theorem mutations_are_real (choice : Bool) :
    observe (entry [0x38,6] (fun _ => 8192) (single 8192 1)) choice =
      .ok (0xdeadbeef00000602,4098,[⟨.data,8192,1⟩]) ∧
    Sequential.decodeAt (entry [0x3a,0xc6]) = .error .unsupportedEncoding ∧
    Sequential.decodeAt (entry [0x40,0x3a,0xc6]) = .ok (.cmpReg8 .rax .rsi true) ∧
    Sequential.decodeAt (entry [0x44,0x3a,0x0e]) = .ok (.cmpRegMem8 .r9 (.base .rsi) true) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Read permission is independent of execute/write permission. Missing and
noncanonical DATA fail through the same production primitive at the real EA. -/
theorem current_data_access (choice : Bool) :
    observe (entry [0x3a,6] (fun _ => 8192)) choice = .error (.inaccessibleData 8192) ∧
    observe (entry [0x3a,6] (fun _ => 0x800000000000) (single 0x800000000000 1)) choice =
      .error (.inaccessibleData 0x800000000000) ∧
    observe (entry [0x3a,6] (fun _ => 8192) (single 8193 1)) choice =
      .error (.inaccessibleData 8192) := by exact ⟨rfl,rfl,rfl⟩

/-- The first nine bytes cannot authenticate the last six of a NOP15. -/
theorem short_transport_insufficient :
    SuccessfulFetchTransportWithin 9 (codeState padding 0) (codeState (padding.set 14 1) 0) ∧
      Sequential.decodeAt (codeState padding 0) = .ok (.nop .fifteen) ∧
      Sequential.decodeAt (codeState (padding.set 14 1) 0) = .error .unsupportedEncoding := by
  refine ⟨?_,NopEncoding.decode_bytes .fifteen,?_⟩
  · have same : ∀ offset : Fin 9,
        fetchByte (codeState padding 0).memory (BitVec.ofNat 64 offset.val) =
          fetchByte (codeState (padding.set 14 1) 0).memory (BitVec.ofNat 64 offset.val) := by
      decide +kernel
    intro offset bound byte fetched
    simp only [codeState, BitVec.zero_add] at fetched ⊢
    have equal := same ⟨offset,bound⟩
    change fetchByte (codeMemory padding) (BitVec.ofNat 64 offset) =
      fetchByte (codeMemory (padding.set 14 1)) (BitVec.ofNat 64 offset) at equal
    exact equal.symm.trans fetched
  · decide +kernel

private def relocated (base : Word) : Memory where
  read address := padding[(address - base).toNat]?
  executable address := decide ((address - base).toNat < 15)

/-- Exact complete code can end at the last low canonical byte, but a window
crossing the canonical hole or wrapping the word cannot authenticate. -/
theorem nop_code_boundaries :
    ELF.checkCode (relocated 0x7ffffffffff1) 0x7ffffffffff1 padding = true ∧
    ELF.checkCode (relocated 0x7ffffffffff2) 0x7ffffffffff2 padding = false ∧
    ELF.checkCode (relocated 0xfffffffffffffff2) 0xfffffffffffffff2 padding = false := by decide +kernel

/-- Complete exact encodings succeed without demanding byte16; the sibling
uses the shared decoder/executor, retaining the entire observation. -/
theorem sibling_and_literals (choice : Bool) :
    CallReturn.decodeAt (entry padding) = .ok (.sequential (.nop .fifteen)) ∧
    CallReturn.rawStep choice (entry padding) =
      .ok ⟨.next { entry padding with rip := 4111 },[]⟩ ∧
    CallReturn.decodeAt (entry [0x44,0x3a,4,6]) =
      .ok (.sequential (.cmpRegMem8 .r8 (.indexed .rsi .rax 0) true)) ∧
    Literals.instruction (.cmpRegMem8 .r8 (.indexed .rsi .rax 0) true) =
      "(.cmpRegMem8 .r8 (.indexed .rsi .rax 0) true)" ∧
    Literals.instruction (.nop .fifteen) = "(.nop .fifteen)" := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

-- Original full symbol bytes read from the frozen manifests and objdump.
-- These are only whole-window decoding/checking tests, without function claims.
def gcc : List Byte :=
  [0xf3,0x0f,0x1e,0xfa,0x48,0x85,0xd2,0x74,0x1f,0x31,0xc0,0xeb,0x0c,
   0x0f,0x1f,0,0x48,0x83,0xc0,1,0x48,0x39,0xc2,0x74,0x0f,0x0f,0xb6,
   0x0c,6,0x38,0x0c,7,0x74,0xee,0x31,0xc0,0xc3,0x0f,0x1f,0,0xb8,1,0,0,0,0xc3]
def clang : List Byte :=
  [0x48,0x85,0xd2,0x74,0x39,0x0f,0xb6,7,0x3a,6,0x75,0x35,0xb9,1,0,0,0,
   0x66,0x66,0x66,0x66,0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0,
   0x48,0x89,0xc8,0x48,0x39,0xca,0x74,0x0f,0x44,0x0f,0xb6,4,7,
   0x48,0x8d,0x48,1,0x44,0x3a,4,6,0x74,0xe9,0x48,0x39,0xd0,
   0x0f,0x93,0xc0,0xc3,0xb0,1,0xc3,0x31,0xc0,0xc3]

def roomy : CFG.Profile := ⟨128,32,by decide⟩

private def admitted (profile : CFG.Profile) (bytes : List Byte) : Bool :=
  match CFG.analyzeWith profile bytes with
  | .ok graph => CFG.checkWith profile bytes graph
  | .error _ => false

theorem original_whole_windows : admitted CFG.defaultProfile gcc = true ∧ admitted roomy clang = true :=
  by decide +kernel

theorem default_still_rejects_clang : CFG.analyze clang = .error .byteLimit ∧
    (match CFG.analyzeWith roomy clang with
      | .ok graph => CFG.check clang graph
      | .error _ => true) = false := by
  constructor
  · rfl
  · decide +kernel

/-- Explicit independent partition. The padding must be ONE instruction at17,
and bytes beyond the old64 cap must remain checked, including the last RET. -/
def clangGraph : CFG.Graph := CFG.annotate [
  ⟨0,.test64 .rdx .rdx,false,0⟩,⟨3,.je 0x39,false,0⟩,
  ⟨5,.movzxMem8 .rax (.base .rdi) false,false,0⟩,
  ⟨8,.cmpRegMem8 .rax (.base .rsi) false,false,0⟩,
  ⟨10,.legacy (.jnz 0x35),false,0⟩,⟨12,.legacy (.mov32 .rcx 1),false,0⟩,
  ⟨17,.nop .fifteen,false,0⟩,⟨32,.movReg64 .rax .rcx,false,0⟩,
  ⟨35,.cmp64 .rdx .rcx,false,0⟩,⟨38,.je 0x0f,false,0⟩,
  ⟨40,.movzxMem8 .r8 (.indexed .rdi .rax 0) true,false,0⟩,
  ⟨45,.lea64 .rcx (.baseDisp8 .rax 1),false,0⟩,
  ⟨49,.cmpRegMem8 .r8 (.indexed .rsi .rax 0) true,false,0⟩,
  ⟨53,.je 0xe9,false,0⟩,⟨55,.cmp64 .rax .rdx,false,0⟩,
  ⟨58,.setcc .aboveEqual .rax false,false,0⟩,⟨61,.legacy .ret,false,0⟩,
  ⟨62,.movImm8 .rax 1 false,false,0⟩,⟨64,.legacy .ret,false,0⟩,
  ⟨65,.xorSelf32 .rax,false,0⟩,⟨67,.legacy .ret,false,0⟩]

theorem clang_partition : CFG.analyzeWith roomy clang = .ok clangGraph := by rfl

theorem clang_checked : CFG.Valid clang clangGraph roomy := CFG.analyzeWith_sound clang_partition

theorem full_window_mutations :
    ([17,23,24,25,26,30,31,49,50,51,52,58,59,60,62,63,64,65,66,67] : List Nat).all
      (fun i => !(CFG.checkWith roomy (clang.set i (clang[i]! ^^^ 1)) clangGraph)) = true := by decide +kernel

-- A bounded production VC combines actual CMP DATA1, NOP15, SETae and RET.
def program : List Byte := [0x3a,6] ++ padding ++ [0x0f,0x93,0xc0,0xc3]
def graph : CFG.Graph :=
  ⟨[⟨0,.cmpRegMem8 .rax (.base .rsi) false,true,4⟩,
    ⟨2,.nop .fifteen,false,3⟩,⟨17,.setcc .aboveEqual .rax false,false,2⟩,
    ⟨20,.legacy .ret,false,1⟩],4⟩
private def initial : State := entry program (fun r => match r with
  | .rax => 0x1122334455667780 | .rsi => 0x9000 | .rsp => 0x2000
  | _ => 0x99aabbccddeeff01) (fun address => if address = 0x9000 then some 1
    else if 0x2000 ≤ address.toNat ∧ address.toNat < 0x2008 then
      some ((0x3000 : Word).extractLsb' ((address.toNat - 0x2000) * 8) 8) else none)
private def allowed (_ : State) (read : Read) : Prop :=
  read = ⟨.data,0x9000,1⟩ ∨ read = ⟨.stack,0x2000,8⟩
private def post (result : Result) : Prop :=
  result.state.registers .rax = 0x1122334455667701 ∧
  result.state.registers .rsp = 0x2008 ∧ result.state.rip = 0x3000 ∧
  result.state.flags = 0xdeadbeef00000e12 ∧ result.instructions = 4 ∧
  result.reads = [⟨.data,0x9000,1⟩,⟨.stack,0x2000,8⟩]

private def start : graph.Index := ⟨0,by decide⟩

private instance (before : State) (read : Read) : Decidable (allowed before read) :=
  inferInstanceAs (Decidable (read = ⟨.data,0x9000,1⟩ ∨ read = ⟨.stack,0x2000,8⟩))

private instance (result : Result) : Decidable (post result) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private instance (before : State) : Decidable (VCGen.wp graph 4096 allowed 4 start before post) :=
  VCGen.decidableWP graph 4096 allowed (fun _ _ => inferInstance)
    4 start before post (fun _ => inferInstance)

theorem checked : CFG.Valid program graph := CFG.check_sound (by decide +kernel)

theorem generated_vc : VCGen.wp graph 4096 allowed 4 start initial post := by decide +kernel

theorem generated_vc_runs (choices : Choices) :
    ∃ result, Sequential.run choices 4 initial = .ok result ∧ post result ∧
      result.state.memory = initial.memory ∧ result.instructions ≤ 4 ∧
      VCGen.CheckedTrace allowed choices initial result := by
  apply VCGen.run_sound_frame checked (node := start)
    (base := 4096) (code := ?_) (pc := rfl) generated_vc choices
  exact ELF.checkCode_sound _ _ _ (by decide +kernel)

/-- Caller-only policy must reject the real DATA1 observation, even if its
address could overlap a stack loan. A NOP cannot hide or remove that read. -/
theorem pure_call_denies_cmp :
    ¬ VCGen.wp graph 4096 (fun _ read => EDSL.PureCall.RawRead initial read)
      4 start initial post := by
  rw [VCGen.wp_cmpRegMem8_iff graph 4096 _ 3 start initial post
    .rax (.base .rsi) false rfl]
  rintro ⟨_,_,permitted,_⟩
  exact EDSL.PureCall.cmpRegMem8_not_rawRead _ _ _ permitted

/-- Code authentication alone does not authorize an absent CURRENT data byte. -/
theorem missing_data_vc_rejected :
    let missing := { initial with memory := { initial.memory with
      read := fun address => if address = 0x9000 then none else initial.memory.read address } }
    ¬ VCGen.wp graph 4096 allowed 4 start missing post := by
  decide +kernel

end EDSL.Tests.SequentialByteComparePadding
