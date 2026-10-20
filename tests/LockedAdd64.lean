/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedAdd64
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.LockedAdd64
open X86
open X86.LockedAdd64

/-- Actual RAM populated from literal input bytes. Protected code and adjacent
sentinels have independent locations; no qword writer creates the inputs. -/
def ram (code operand : List Byte) : Memory where
  read address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length
      then code[address.toNat - 4096]?
    else if address = 65535 then some 0x5a
    else if address = 65544 then some 0xa5
    else if 65536 ≤ address.toNat ∧ address.toNat < 65544
      then operand[address.toNat - 65536]?
    else none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length)
  writable address := decide (65536 ≤ address.toNat ∧ address.toNat < 65544)

def initial (code operand : List Byte) (registers : List (Register × Word)) : State where
  registers register := (registers.lookup register).getD 0xdeadbeef12345678
  rip := 4096
  flags := 0x200202
  memory := ram code operand

def frozenCode : List Byte := [0xf0,0x48,0x0f,0xc1,0x07]

structure View where
  event : FetchAddEvent64
  registers : List Word
  rip : Word
  flags : Word
  readback : Except Error Word
  bytes : List (Option Byte)
  code : List (Option Byte)
  executable : List Bool
  writable : List Bool
  accesses : List Access
  deriving Repr

def observe (state : State) (registers : List Register) : Except Error View := do
  let result ← X86.LockedAdd64.step state
  return ⟨result.event, registers.map result.state.registers, result.state.rip, result.state.flags,
    loadQWord result.state.memory 65536,
    [65535,65536,65537,65538,65539,65540,65541,65542,65543,65544].map result.state.memory.read,
    [4096,4097,4098,4099,4100].map result.state.memory.read,
    [4096,4100,4101,65536,65543].map result.state.memory.executable,
    [4096,65535,65536,65543,65544].map result.state.memory.writable, result.accesses⟩

/-- Frozen bytes exercise actual fetch/decode/execution, a low32 carry into an
existing high half, full64 RAX response, untouched GPRs/flags/permissions/code,
and both neighboring bytes. The expectations are literal arithmetic results. -/
example : observe (initial frozenCode [0xff,0xff,0xff,0xff,0x12,0x34,0x56,0x78]
    [(.rdi,65536),(.rax,1),(.rsp,0x123456789abcdef0)]) [.rax,.rdi,.rsp,.r8] = .ok {
    event := ⟨1,⟨65536,0x78563412ffffffff,0x7856341300000000⟩⟩
    registers := [0x78563412ffffffff,65536,0x123456789abcdef0,0xdeadbeef12345678]
    rip := 4101
    flags := 0x200216
    readback := .ok 0x7856341300000000
    bytes := [some 0x5a,some 0,some 0,some 0,some 0,some 0x13,some 0x34,some 0x56,
      some 0x78,some 0xa5]
    code := [some 0xf0,some 0x48,some 0x0f,some 0xc1,some 0x07]
    executable := [true,true,false,false,false]
    writable := [false,false,true,true,false]
    accesses := [.rmw8 65536] } := by rfl

def arithmetic (code operand : List Byte) (registers : List (Register × Word))
    (selected : List Register) :=
  (observe (initial code operand registers) selected).map
    (fun view => (view.event,view.registers,view.readback,view.flags,view.accesses))

-- Unsigned full64 wrap must set carry/zero/parity/AF and clear sign/overflow.
example : arithmetic frozenCode [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff]
    [(.rdi,65536),(.rax,1)] [.rax] =
    .ok (⟨1,⟨65536,0xffffffffffffffff,0⟩⟩,[0xffffffffffffffff],.ok 0,0x200257,[.rmw8 65536]) := by rfl

-- A high-bit delta cannot be truncated; negative+negative overflows to positive.
example : arithmetic frozenCode [0,0,0,0,0,0,0,0x80]
    [(.rdi,65536),(.rax,0x8000000000000001)] [.rax] =
    .ok (⟨0x8000000000000001,⟨65536,0x8000000000000000,1⟩⟩,
      [0x8000000000000000],.ok 1,0x200a03,[.rmw8 65536]) := by rfl

-- Positive signed overflow is independent of unsigned carry. Nonstatus bits stay set.
example : arithmetic frozenCode [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0x7f]
    [(.rdi,65536),(.rax,1)] [.rax] =
    .ok (⟨1,⟨65536,0x7fffffffffffffff,0x8000000000000000⟩⟩,
      [0x7fffffffffffffff],.ok 0x8000000000000000,0x200a96,[.rmw8 65536]) := by rfl

-- Clear stale arithmetic bits while preserving EVERY other bit, including high bits.
example : (X86.LockedAdd64.step { initial frozenCode [7,0,0,0,0,0,0,0] [(.rdi,65536),(.rax,2)] with
    flags := 0xffffffffffffffff }).map (fun result => (result.state.flags,result.event.event.after)) =
    .ok (0xfffffffffffff72e,9) := by rfl

-- Zero still emits an event and replaces the source with the full current old value.
example : arithmetic frozenCode [1,0x23,0x45,0x67,0x89,0xab,0xcd,0xef]
    [(.rdi,65536),(.rax,0)] [.rax] =
    .ok (⟨0,⟨65536,0xefcdab8967452301,0xefcdab8967452301⟩⟩,
      [0xefcdab8967452301],.ok 0xefcdab8967452301,0x200282,[.rmw8 65536]) := by rfl

-- Base and source alias: both address and delta must be captured before RDI is overwritten.
example : arithmetic [0xf0,0x48,0x0f,0xc1,0x3f] [0,0,0xff,0xff,0x44,0x33,0x22,0x11]
    [(.rdi,65536),(.rax,77)] [.rdi,.rax] =
    .ok (⟨65536,⟨65536,0x11223344ffff0000,0x1122334500000000⟩⟩,
      [0x11223344ffff0000,77],.ok 0x1122334500000000,0x200206,[.rmw8 65536]) := by rfl

-- RSP is a valid SOURCE without a SIB; its old full64 return is not a stack adjustment.
example : arithmetic [0xf0,0x48,0x0f,0xc1,0x27] [0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88]
    [(.rdi,65536),(.rsp,0x100000001)] [.rsp,.rdi] =
    .ok (⟨0x100000001,⟨65536,0x8877665544332211,0x8877665644332212⟩⟩,
      [0x8877665544332211,65536],.ok 0x8877665644332212,0x200286,[.rmw8 65536]) := by rfl

-- Both REX banks and X=1: [R15],R8 must use current R15, not the invalid low-bank RDI.
example : arithmetic [0xf0,0x4f,0x0f,0xc1,0x07] [0xff,0xff,0xff,0xff,0,0,0,0]
    [(.r15,65536),(.rdi,65537),(.r8,0x100000001),(.rax,9)] [.r8,.rax,.r15,.rdi] =
    .ok (⟨0x100000001,⟨65536,0xffffffff,0x200000000⟩⟩,
      [0xffffffff,9,65536,65537],.ok 0x200000000,0x200216,[.rmw8 65536]) := by rfl

-- High-bank alias also captures prestate operands before writing R15.
example : arithmetic [0xf0,0x4d,0x0f,0xc1,0x3f] [0,0,0,0,0,0,0,0x80]
    [(.r15,65536)] [.r15] =
    .ok (⟨65536,⟨65536,0x8000000000000000,0x8000000000010000⟩⟩,
      [0x8000000000000000],.ok 0x8000000000010000,0x200286,[.rmw8 65536]) := by rfl

/-- Decode observations retain exact bytes as well as semantic operands. -/
def decoded (state : State) := (X86.LockedAdd64.decodeAt state).map
  (fun instruction => (instruction.bytes,instruction.base,instruction.source,instruction.length))

-- All R/B banks work. X does not change a no-SIB operand, but remains in the byte binding.
example : ([0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f] : List Byte).map
    (fun rex => decoded (initial [0xf0,rex,0x0f,0xc1,0x07] [] [])) =
    [.ok ([0xf0,0x48,0x0f,0xc1,0x07],.rdi,.rax,5),
     .ok ([0xf0,0x49,0x0f,0xc1,0x07],.r15,.rax,5),
     .ok ([0xf0,0x4a,0x0f,0xc1,0x07],.rdi,.rax,5),
     .ok ([0xf0,0x4b,0x0f,0xc1,0x07],.r15,.rax,5),
     .ok ([0xf0,0x4c,0x0f,0xc1,0x07],.rdi,.r8,5),
     .ok ([0xf0,0x4d,0x0f,0xc1,0x07],.r15,.r8,5),
     .ok ([0xf0,0x4e,0x0f,0xc1,0x07],.rdi,.r8,5),
     .ok ([0xf0,0x4f,0x0f,0xc1,0x07],.r15,.r8,5)] := by rfl

-- All admitted low base encodings (and B=1 counterparts) are real register bases.
example : ([0x00,0x01,0x02,0x03,0x06,0x07] : List Byte).map
    (fun modrm => (X86.LockedAdd64.decodeAt (initial [0xf0,0x48,0x0f,0xc1,modrm] [] [])).map
      (fun instruction => instruction.base)) =
    [.ok .rax,.ok .rcx,.ok .rdx,.ok .rbx,.ok .rsi,.ok .rdi] := by rfl
example : ([0x00,0x01,0x02,0x03,0x06,0x07] : List Byte).map
    (fun modrm => (X86.LockedAdd64.decodeAt (initial [0xf0,0x49,0x0f,0xc1,modrm] [] [])).map
      (fun instruction => instruction.base)) =
    [.ok .r8,.ok .r9,.ok .r10,.ok .r11,.ok .r14,.ok .r15] := by rfl

-- All sixteen sources are admitted, including the RSP/RBP and R12/R13 encodings
-- that are excluded as no-displacement/no-SIB BASES.
example : ([0x48,0x4c] : List Byte).map (fun rex =>
    ([0x07,0x0f,0x17,0x1f,0x27,0x2f,0x37,0x3f] : List Byte).map
      (fun modrm => (X86.LockedAdd64.decodeAt (initial [0xf0,rex,0x0f,0xc1,modrm] [] [])).map
        (fun instruction => instruction.source))) =
    [[.ok .rax,.ok .rcx,.ok .rdx,.ok .rbx,.ok .rsp,.ok .rbp,.ok .rsi,.ok .rdi],
     [.ok .r8,.ok .r9,.ok .r10,.ok .r11,.ok .r12,.ok .r13,.ok .r14,.ok .r15]] := by rfl

-- Changed actual ModRM selects RCX's delta; frozen expected bytes are never trusted.
example : arithmetic [0xf0,0x48,0x0f,0xc1,0x0f] [0,0,0,0,1,0,0,0]
    [(.rdi,65536),(.rax,99),(.rcx,7)] [.rcx,.rax] =
    .ok (⟨7,⟨65536,0x100000000,0x100000007⟩⟩,
      [0x100000000,99],.ok 0x100000007,0x200202,[.rmw8 65536]) := by rfl

def consecutive : Except Error
    (FetchAddEvent64 × FetchAddEvent64 × Word × Word × Except Error Word) := do
  let first ← X86.LockedAdd64.step (initial (frozenCode ++ [0xf0,0x48,0x0f,0xc1,0x0f])
    [0xff,0xff,0xff,0xff,0,0,0,0] [(.rdi,65536),(.rax,1),(.rcx,0xffffffff00000000)])
  let second ← X86.LockedAdd64.step first.state
  return (first.event,second.event,second.state.registers .rcx,second.state.rip,
    loadQWord second.state.memory 65536)

-- The second instruction fetches the next actual code and reads the updated RAM.
example : consecutive = .ok
    (⟨1,⟨65536,0xffffffff,0x100000000⟩⟩,
      ⟨0xffffffff00000000,⟨65536,0x100000000,0⟩⟩,0x100000000,4106,.ok 0) := by rfl

-- No following byte is needed; the five-byte fixture has no padding at 4101.
example : decoded (initial frozenCode [] []) =
    .ok ([0xf0,0x48,0x0f,0xc1,0x07],.rdi,.rax,5) := by rfl

-- Denial or absence of ANY fetch byte, including the final ModRM, fails the decoder/step.
example : ([4096,4097,4098,4099,4100] : List Word).map
    (fun denied => (X86.LockedAdd64.step { initial frozenCode [1,2,3,4,5,6,7,8] [(.rdi,65536),(.rax,1)] with
      memory := { ram frozenCode [1,2,3,4,5,6,7,8] with
        executable := fun address => address != denied } }).map (fun _ => true)) =
    [.error (.inaccessibleInstruction 4096),.error (.inaccessibleInstruction 4097),
      .error (.inaccessibleInstruction 4098),.error (.inaccessibleInstruction 4099),
      .error (.inaccessibleInstruction 4100)] := by rfl
example : (X86.LockedAdd64.decodeAt { initial frozenCode [] [] with
    memory := { ram frozenCode [] with
      read := fun address => if address = 4100 then none else (ram frozenCode []).read address } }).map
    (fun _ => true) = .error (.inaccessibleInstruction 4100) := by rfl

/-- This RAM deliberately provides wrapped bytes. The separate no-wrap gate
must reject a five-byte window starting only four bytes from the end. -/
def edge (base : Word) : State where
  registers := fun _ => 0
  rip := base
  flags := 0
  memory := { read := fun address => frozenCode[(address - base).toNat]?
              executable := fun _ => true }

example : (X86.LockedAdd64.decodeAt (edge 0xfffffffffffffffc)).map (fun _ => true) =
    .error (.inaccessibleInstruction 0xfffffffffffffffc) := by rfl
example : decoded (edge 0xfffffffffffffffb) =
    .ok ([0xf0,0x48,0x0f,0xc1,0x07],.rdi,.rax,5) := by rfl
example : (X86.LockedAdd64.decodeAt (edge 0x7ffffffffffd)).map (fun _ => true) =
    .error (.inaccessibleInstruction 0x800000000000) := by rfl

-- W=0, byte XADD, absent/reordered/repeated/legacy prefixes, wrong opcode,
-- register mode, SIB, RIP-relative, disp8/disp32, and R12/R13 exclusions.
example : ([
    [0xf0,0x40,0x0f,0xc1,0x07], [0xf0,0x48,0x0f,0xc0,0x07],
    [0x48,0x0f,0xc1,0x07,0], [0x48,0xf0,0x0f,0xc1,0x07],
    [0xf0,0x66,0x48,0x0f,0xc1,0x07], [0x66,0xf0,0x48,0x0f,0xc1,0x07],
    [0xf0,0xf0,0x48,0x0f,0xc1,0x07], [0xf0,0x48,0x48,0x0f,0xc1,0x07],
    [0xf2,0x48,0x0f,0xc1,0x07], [0xf3,0x48,0x0f,0xc1,0x07],
    [0xf0,0x48,0x0f,0xc7,0x07], [0xf0,0x48,0x0f,0xc1,0xc7],
    [0xf0,0x48,0x0f,0xc1,0x04], [0xf0,0x48,0x0f,0xc1,0x05],
    [0xf0,0x48,0x0f,0xc1,0x47,0], [0xf0,0x48,0x0f,0xc1,0x87,0,0,0,0],
    [0xf0,0x49,0x0f,0xc1,0x04], [0xf0,0x49,0x0f,0xc1,0x05]
    , [0xf0,0x58,0x0f,0xc1,0x07], [0xf0,0x67,0x48,0x0f,0xc1,0x07]
    ] : List (List Byte)).map
    (fun code => (X86.LockedAdd64.decodeAt (initial code [] [])).map (fun _ => true)) =
    List.replicate 20 (.error .unsupportedEncoding) := by rfl

-- Every upper-byte current write/read permission remains required even at delta zero.
example : ([65540,65541,65542,65543] : List Word).map
    (fun denied => (X86.LockedAdd64.step { initial frozenCode [1,2,3,4,5,6,7,8] [(.rdi,65536),(.rax,0)] with
      memory := { ram frozenCode [1,2,3,4,5,6,7,8] with
        writable := fun address => address != denied } }).map (fun _ => true)) =
    List.replicate 4 (.error (.writeDenied 65536)) := by rfl
example : ([65540,65541,65542,65543] : List Word).map
    (fun missing => (X86.LockedAdd64.step { initial frozenCode [1,2,3,4,5,6,7,8] [(.rdi,65536),(.rax,0)] with
      memory := { ram frozenCode [1,2,3,4,5,6,7,8] with
        read := fun address => if address = missing then none
          else (ram frozenCode [1,2,3,4,5,6,7,8]).read address } }).map (fun _ => true)) =
    List.replicate 4 (.error (.writeDenied 65536)) := by rfl

-- Every executable operand byte blocks fixed-code execution, including at delta zero.
example : ([65536,65537,65538,65539,65540,65541,65542,65543] : List Word).map
    (fun executable => (X86.LockedAdd64.step { initial frozenCode [1,2,3,4,5,6,7,8] [(.rdi,65536),(.rax,0)] with
      memory := { ram frozenCode [1,2,3,4,5,6,7,8] with
        executable := fun address => (ram frozenCode []).executable address || address == executable }
      }).map (fun _ => true)) =
    List.replicate 8 (.error (.writeDenied 65536)) := by rfl

-- Current address support is checked by step, not just by the memory primitive tests.
example : ([65537,0x800000000000,0xffffffffffffffff] : List Word).map
    (fun address => (X86.LockedAdd64.step (initial frozenCode [1,2,3,4,5,6,7,8]
      [(.rdi,address),(.rax,0)])).map (fun _ => true)) =
    [.error (.unsupportedAtomicAddress 65537),.error (.unsupportedAtomicAddress 0x800000000000),
      .error (.unsupportedAtomicAddress 0xffffffffffffffff)] := by rfl

end EDSL.Tests.LockedAdd64

#audit_edsl
