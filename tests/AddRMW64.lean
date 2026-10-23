/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.AddRMW64
import EDSL.Audit

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.AddRMW64
open X86

deriving instance DecidableEq for Except

/-- Literal byte RAM, with no qword writer constructing the old operand.
Code ends at its actual last byte; no executable padding is supplied. -/
def ram (code operand : List Byte) : Memory where
  read address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length then
      code[address.toNat - 4096]?
    else if 65536 ≤ address.toNat ∧ address.toNat < 65544 then
      operand[address.toNat - 65536]?
    else none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length)
  writable address := decide (65536 ≤ address.toNat ∧ address.toNat < 65544)

def initial (code operand : List Byte) (registers : List (Register × Word))
    (flags : Word := 0x200202) : State where
  registers register := (registers.lookup register).getD 0xdeadbeef12345678
  rip := 4096
  flags := flags
  memory := ram code operand

def addOne : List Byte := [0xf0,0x48,0x83,0x07,1]
def incOne : List Byte := [0xf0,0x48,0xff,0x07]

structure View where
  event : FetchAddEvent64
  registers : List Word
  rip : Word
  flags : Word
  readback : Except Error Word
  accesses : List X86.AddRMW64.Access
  deriving DecidableEq, Repr

/-- Production fetch, recognition, fixed-code preflight and RAM transition. -/
def observe (state : State) (selected : List Register := []) : Except Error View := do
  let result ← X86.AddRMW64.step state
  return ⟨result.event, selected.map result.state.registers, result.state.rip,
    result.state.flags, loadQWord result.state.memory 65536, result.accesses⟩

-- FF means -1, not +255. The event must retain the entire sign-extended delta.
example : observe (initial [0xf0,0x48,0x83,0x07,0xff] [0,0,0,0,0,0,0,0] [(.rdi,65536)]) =
    .ok ⟨⟨0xffffffffffffffff,⟨65536,0,0xffffffffffffffff⟩⟩,[],4101,0x200286,
      .ok 0xffffffffffffffff,[.rmw8 65536]⟩ := by decide +kernel

-- The negative endpoint -128 crosses zero without signed overflow or carry.
example : observe (initial [0xf0,0x48,0x83,0x07,0x80] [0x7f,0,0,0,0,0,0,0] [(.rdi,65536)]) =
    .ok ⟨⟨0xffffffffffffff80,⟨65536,127,0xffffffffffffffff⟩⟩,[],4101,0x200286,
      .ok 0xffffffffffffffff,[.rmw8 65536]⟩ := by decide +kernel

-- Full64 wrap, not low32 arithmetic: CF/ZF/PF/AF set, OF/SF clear.
example : observe (initial addOne [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] [(.rdi,65536)]) =
    .ok ⟨⟨1,⟨65536,0xffffffffffffffff,0⟩⟩,[],4101,0x200257,.ok 0,[.rmw8 65536]⟩ := by decide +kernel

-- Signed overflow without unsigned carry, with even parity and nibble carry.
example : observe (initial addOne [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0x7f] [(.rdi,65536)]) =
    .ok ⟨⟨1,⟨65536,0x7fffffffffffffff,0x8000000000000000⟩⟩,[],4101,0x200a96,
      .ok 0x8000000000000000,[.rmw8 65536]⟩ := by decide +kernel

-- Positive imm8 endpoint: 1+127=128 has odd low-byte parity, AF but no SF.
example : observe (initial [0xf0,0x48,0x83,0x07,0x7f] [1,0,0,0,0,0,0,0] [(.rdi,65536)]) =
    .ok ⟨⟨127,⟨65536,1,128⟩⟩,[],4101,0x200212,.ok 128,[.rmw8 65536]⟩ := by decide +kernel

-- Zero still reads the complete current old value and emits one full RMW event.
example : observe (initial [0xf0,0x48,0x83,0x07,0] [1,0x23,0x45,0x67,0x89,0xab,0xcd,0xef]
    [(.rdi,65536)]) =
    .ok ⟨⟨0,⟨65536,0xefcdab8967452301,0xefcdab8967452301⟩⟩,[],4101,0x200282,
      .ok 0xefcdab8967452301,[.rmw8 65536]⟩ := by decide +kernel

-- The same wrap must leave CF clear/set according to BOTH incoming CF values.
example : ([0x200202,0x200203] : List Word).map (fun flags =>
    observe (initial incOne [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] [(.rdi,65536)] flags)) =
    [.ok ⟨⟨1,⟨65536,0xffffffffffffffff,0⟩⟩,[],4100,0x200256,.ok 0,[.rmw8 65536]⟩,
     .ok ⟨⟨1,⟨65536,0xffffffffffffffff,0⟩⟩,[],4100,0x200257,.ok 0,[.rmw8 65536]⟩] := by decide +kernel

-- INC must also retain CF when there is NO sum carry; signed overflow still sets OF.
example : observe (initial incOne [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0x7f]
    [(.rdi,65536)] 0x200203) =
    .ok ⟨⟨1,⟨65536,0x7fffffffffffffff,0x8000000000000000⟩⟩,[],4100,0x200a97,
      .ok 0x8000000000000000,[.rmw8 65536]⟩ := by decide +kernel

-- Clear stale arithmetic flags but retain every other bit, including high bits and CF.
example : observe (initial incOne [7,0,0,0,0,0,0,0] [(.rdi,65536)] 0xffffffffffffffff) =
    .ok ⟨⟨1,⟨65536,7,8⟩⟩,[],4100,0xfffffffffffff72b,.ok 8,[.rmw8 65536]⟩ := by decide +kernel

def allRegisters : List Register :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

def registerInputs : List (Register × Word) :=
  [(.rax,0x1111),(.rcx,0x2222),(.rdx,0x3333),(.rbx,0x4444),(.rsp,0x123456789abcdef0),
   (.rbp,0x5555),(.rsi,0x6666),(.rdi,65536),(.r8,0x8888),(.r9,0x9999),(.r10,0xaaaa),
   (.r11,0xbbbb),(.r12,0xcccc),(.r13,0xdddd),(.r14,0xeeee),(.r15,0xffff)]

-- After a real nontrivial RMW, every GPR must survive BOTH non-writeback forms.
-- Distinct register values catch swaps as well as an accidental old-value destination.
example : ([addOne,incOne] : List (List Byte)).map (fun code =>
    (observe (initial code [0xf,0,0,0,0,0,0,0] registerInputs) allRegisters).map
      (fun view => (view.event,view.registers,view.flags,view.readback))) =
    List.replicate 2 (.ok (⟨1,⟨65536,15,16⟩⟩,
      [0x1111,0x2222,0x3333,0x4444,0x123456789abcdef0,0x5555,0x6666,65536,
       0x8888,0x9999,0xaaaa,0xbbbb,0xcccc,0xdddd,0xeeee,0xffff],0x200212,.ok 16)) := by decide +kernel

-- B=1 selects R15 even when low-bank RDI points to an unsupported address.
example : observe (initial [0xf0,0x49,0xff,0x07] [0xff,0xff,0xff,0xff,0,0,0,0]
    [(.r15,65536),(.rdi,65537)]) [.r15,.rdi] =
    .ok ⟨⟨1,⟨65536,0xffffffff,0x100000000⟩⟩,[65536,65537],4100,0x200216,
      .ok 0x100000000,[.rmw8 65536]⟩ := by decide +kernel

-- XADD source/base alias: address and delta must precede full64 old-value writeback.
example : observe (initial [0xf0,0x48,0x0f,0xc1,0x3f] [0,0,0xff,0xff,0x44,0x33,0x22,0x11]
    [(.rdi,65536),(.rax,77)]) [.rdi,.rax] =
    .ok ⟨⟨65536,⟨65536,0x11223344ffff0000,0x1122334500000000⟩⟩,
      [0x11223344ffff0000,77],4101,0x200206,.ok 0x1122334500000000,[.rmw8 65536]⟩ := by decide +kernel

-- Legacy source RSP and the ignored-X/high-source REX cases remain executable.
example : observe (initial [0xf0,0x48,0x0f,0xc1,0x27] [0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88]
    [(.rdi,65536),(.rsp,0x100000001)]) [.rsp,.rdi] =
    .ok ⟨⟨0x100000001,⟨65536,0x8877665544332211,0x8877665644332212⟩⟩,
      [0x8877665544332211,65536],4101,0x200286,.ok 0x8877665644332212,[.rmw8 65536]⟩ := by decide +kernel
example : observe (initial [0xf0,0x4f,0x0f,0xc1,0x07] [0xff,0xff,0xff,0xff,0,0,0,0]
    [(.r15,65536),(.rdi,65537),(.r8,0x100000001)]) [.r8,.r15] =
    .ok ⟨⟨0x100000001,⟨65536,0xffffffff,0x200000000⟩⟩,
      [0xffffffff,65536],4101,0x200216,.ok 0x200000000,[.rmw8 65536]⟩ := by decide +kernel

/-- Wrapped backing bytes are deliberate: no-wrap must be enforced by fetch,
not inferred from a fixture's absence of bytes at low addresses. -/
def edge (code : List Byte) (base : Word) : State where
  registers := fun _ => 0
  rip := base
  flags := 0
  memory := { read := fun address => code[(address - base).toNat]?
              executable := fun _ => true }

-- Four-byte INC succeeds at both a no-wrap boundary and a canonical boundary.
-- The missing/noncanonical fifth byte is not a fetch prerequisite.
example : (X86.AddRMW64.decodeAt (edge incOne 0xfffffffffffffffc)).map
    (fun instruction => (instruction.bytes,instruction.length)) = .ok (incOne,4) := by decide +kernel
example : (X86.AddRMW64.decodeAt (edge incOne 0x7ffffffffffc)).map
    (fun instruction => instruction.length) = .ok 4 := by decide +kernel
example : (X86.AddRMW64.decodeAt (edge addOne 0xfffffffffffffffc)).map
    (fun _ => true) = .error (.inaccessibleInstruction 0xfffffffffffffffc) := by decide +kernel

-- Selected new forms still require EVERY byte of their own actual code.
example : (X86.AddRMW64.decodeAt { initial incOne [] [] with
    memory := { ram incOne [] with executable := fun address => address != 4099 } }).map
      (fun _ => true) = .error (.inaccessibleInstruction 4099) := by decide +kernel
example : (X86.AddRMW64.decodeAt (initial [0xf0,0x48,0x83,0x07] [] [])).map
    (fun _ => true) = .error (.inaccessibleInstruction 4100) := by decide +kernel

-- Denial of any operand byte prevents a result even for ADD delta zero.
example : ([65536,65537,65538,65539,65540,65541,65542,65543] : List Word).map
    (fun denied => (X86.AddRMW64.step { initial [0xf0,0x48,0x83,0x07,0]
      [1,2,3,4,5,6,7,8] [(.rdi,65536)] with
        memory := { ram [0xf0,0x48,0x83,0x07,0] [1,2,3,4,5,6,7,8] with
          writable := fun address => address != denied } }).map (fun _ => true)) =
    List.replicate 8 (.error (.writeDenied 65536)) := by decide +kernel

-- A missing current read byte is denied by the same full-eight-byte preflight.
example : ([65536,65537,65538,65539,65540,65541,65542,65543] : List Word).map
    (fun missing => (X86.AddRMW64.step { initial incOne [1,2,3,4,5,6,7,8] [(.rdi,65536)] with
      memory := { ram incOne [1,2,3,4,5,6,7,8] with
        read := fun address => if address = missing then none
          else (ram incOne [1,2,3,4,5,6,7,8]).read address } }).map (fun _ => true)) =
    List.replicate 8 (.error (.writeDenied 65536)) := by decide +kernel

-- Any executable operand byte fails the additional fixed-code gate.
example : ([65536,65537,65538,65539,65540,65541,65542,65543] : List Word).map
    (fun executable => (X86.AddRMW64.step { initial incOne [1,2,3,4,5,6,7,8] [(.rdi,65536)] with
      memory := { ram incOne [1,2,3,4,5,6,7,8] with
        executable := fun address => (ram incOne []).executable address || address == executable }
      }).map (fun _ => true)) = List.replicate 8 (.error (.writeDenied 65536)) := by decide +kernel

-- Group /1, register mode, SIB, RIP-relative, displacements, W=0, R/X bits,
-- missing/reordered/repeated/legacy prefixes, and R12/R13 bases are unsupported.
example : ([
    [0xf0,0x48,0x83,0x0f,1], [0xf0,0x48,0xff,0x0f,0],
    [0xf0,0x48,0x83,0xc7,1], [0xf0,0x48,0xff,0xc7,0],
    [0xf0,0x48,0x83,0x04,1], [0xf0,0x48,0xff,0x05,0],
    [0xf0,0x48,0x83,0x47,1,0], [0xf0,0x48,0xff,0x87,0,0,0,0],
    [0xf0,0x49,0x83,0x04,1], [0xf0,0x49,0xff,0x05,0],
    [0xf0,0x40,0x83,0x07,1], [0xf0,0x40,0xff,0x07,0],
    [0xf0,0x4a,0x83,0x07,1], [0xf0,0x4c,0xff,0x07,0],
    [0x48,0xff,0x07,0,0], [0x48,0xf0,0xff,0x07,0],
    [0xf0,0xf0,0x48,0xff,0x07], [0xf0,0x66,0x48,0x83,0x07,1],
    [0x66,0xf0,0x48,0xff,0x07], [0xf0,0x67,0x48,0xff,0x07]
    ] : List (List Byte)).map (fun code =>
      (X86.AddRMW64.decodeAt (initial code [] [])).map (fun _ => true)) =
    List.replicate 20 (.error .unsupportedEncoding) := by decide +kernel

end EDSL.Tests.AddRMW64

#audit_edsl
