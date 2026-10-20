/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.X86.Sequential.Return
import EDSL.X86.Sequential.Literals
import EDSL.OS.TSO.Model
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialMemory64
open X86

/-- Finite executable bytes and independently supplied ordinary DATA RAM. -/
def entry (code : List Byte) (registers : Register → Word := fun _ => 0)
    (data : Word → Option Byte := fun _ => none)
    (writable : Word → Bool := fun _ => false) : State where
  registers := registers
  flags := 0xfedcba9876543210
  rip := 4096
  memory := {
    read := fun address => if 4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length
      then code[address.toNat - 4096]? else data address
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4096 + code.length)
    writable := writable }

def nextView (af : Bool) (state : State)
    (view : State → List Sequential.Read → α) : Except Error α := do
  let observation ← Sequential.step af state
  match observation.result with
  | .next final => return view final observation.reads
  | _ => throw .unexpectedReturn

/-- Independent literal MOV vectors exercise R, B, ignored non-SIB X, and
both operand directions for every admitted REX.W prefix. -/
example : ([[0x48, 0x8b, 0x0f], [0x49, 0x8b, 0x0f],
      [0x4a, 0x8b, 0x0f], [0x4b, 0x8b, 0x0f],
      [0x4c, 0x8b, 0x0f], [0x4d, 0x8b, 0x0f],
      [0x4e, 0x8b, 0x0f], [0x4f, 0x8b, 0x0f]] : List (List Byte)).map
    (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.ok (.loadMem64 .rcx (.base .rdi)), .ok (.loadMem64 .rcx (.base .r15)),
      .ok (.loadMem64 .rcx (.base .rdi)), .ok (.loadMem64 .rcx (.base .r15)),
      .ok (.loadMem64 .r9 (.base .rdi)), .ok (.loadMem64 .r9 (.base .r15)),
      .ok (.loadMem64 .r9 (.base .rdi)), .ok (.loadMem64 .r9 (.base .r15))] := by rfl

example : ([[0x48, 0x89, 0x0f], [0x49, 0x89, 0x0f],
      [0x4a, 0x89, 0x0f], [0x4b, 0x89, 0x0f],
      [0x4c, 0x89, 0x0f], [0x4d, 0x89, 0x0f],
      [0x4e, 0x89, 0x0f], [0x4f, 0x89, 0x0f]] : List (List Byte)).map
    (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.ok (.storeMem64 (.base .rdi) .rcx), .ok (.storeMem64 (.base .r15) .rcx),
      .ok (.storeMem64 (.base .rdi) .rcx), .ok (.storeMem64 (.base .r15) .rcx),
      .ok (.storeMem64 (.base .rdi) .r9), .ok (.storeMem64 (.base .r15) .r9),
      .ok (.storeMem64 (.base .rdi) .r9), .ok (.storeMem64 (.base .r15) .r9)] := by rfl

/-- On SIB forms all three extension bits have distinct roles. -/
example : ([[0x48, 0x8b, 0x14, 0x8f], [0x49, 0x8b, 0x14, 0x8f],
      [0x4a, 0x8b, 0x14, 0x8f], [0x4b, 0x8b, 0x14, 0x8f],
      [0x4c, 0x8b, 0x14, 0x8f], [0x4d, 0x8b, 0x14, 0x8f],
      [0x4e, 0x8b, 0x14, 0x8f], [0x4f, 0x8b, 0x14, 0x8f]] : List (List Byte)).map
    (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.ok (.loadMem64 .rdx (.indexed .rdi .rcx 2)),
      .ok (.loadMem64 .rdx (.indexed .r15 .rcx 2)),
      .ok (.loadMem64 .rdx (.indexed .rdi .r9 2)),
      .ok (.loadMem64 .rdx (.indexed .r15 .r9 2)),
      .ok (.loadMem64 .r10 (.indexed .rdi .rcx 2)),
      .ok (.loadMem64 .r10 (.indexed .r15 .rcx 2)),
      .ok (.loadMem64 .r10 (.indexed .rdi .r9 2)),
      .ok (.loadMem64 .r10 (.indexed .r15 .r9 2))] := by rfl

example : ([[0x48, 0x89, 0x14, 0x8f], [0x49, 0x89, 0x14, 0x8f],
      [0x4a, 0x89, 0x14, 0x8f], [0x4b, 0x89, 0x14, 0x8f],
      [0x4c, 0x89, 0x14, 0x8f], [0x4d, 0x89, 0x14, 0x8f],
      [0x4e, 0x89, 0x14, 0x8f], [0x4f, 0x89, 0x14, 0x8f]] : List (List Byte)).map
    (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.ok (.storeMem64 (.indexed .rdi .rcx 2) .rdx),
      .ok (.storeMem64 (.indexed .r15 .rcx 2) .rdx),
      .ok (.storeMem64 (.indexed .rdi .r9 2) .rdx),
      .ok (.storeMem64 (.indexed .r15 .r9 2) .rdx),
      .ok (.storeMem64 (.indexed .rdi .rcx 2) .r10),
      .ok (.storeMem64 (.indexed .r15 .rcx 2) .r10),
      .ok (.storeMem64 (.indexed .rdi .r9 2) .r10),
      .ok (.storeMem64 (.indexed .r15 .r9 2) .r10)] := by rfl

example : Sequential.decodeAt (entry [0x4a, 0x8b, 0x04, 0x27]) =
    .ok (.loadMem64 .rax (.indexed .rdi .r12 0)) := by rfl
example : Sequential.decodeAt (entry [0x4f, 0x89, 0x14, 0xa4]) =
    .ok (.storeMem64 (.indexed .r12 .r12 2) .r10) := by rfl
-- Register mode retains its existing full-width MOV path, ignoring X.
example : Sequential.decodeAt (entry [0x4f, 0x8b, 0xfc]) =
    .ok (.movReg64 .r15 .r12) := by rfl

/-- High-half bits and byte order are deliberately unlike the low dword. -/
def data64 (base : Word) (address : Word) : Option Byte :=
  match (address - base).toNat with
  | 0 => some 0xef | 1 => some 0xcd | 2 => some 0xab | 3 => some 0x89
  | 4 => some 0x67 | 5 => some 0x45 | 6 => some 0x23 | 7 => some 0xf1
  | _ => some 0x5a

def registers : Register → Word
  | .rdi => 0x200000000 | .rcx => 0x100000001
  | .r15 => 0x400000000 | .r9 => 0x200000003
  | .rdx => 0x1122334489abcdef | .r10 => 0xfedcba9876543210
  | _ => 0xa5a5a5a5deadbeef

-- Independent expected effective addresses catch truncation and all SIB scales.
example (af : Bool) :
    ([([0x48, 0x8b, 0x14, 0x0f], 0x300000001),
      ([0x48, 0x8b, 0x14, 0x4f], 0x400000002),
      ([0x48, 0x8b, 0x14, 0x8f], 0x600000004),
      ([0x48, 0x8b, 0x14, 0xcf], 0xa00000008)] : List (List Byte × Word)).map
      (fun (bytes, expectedAddress) => nextView af
        (entry bytes registers (data64 expectedAddress))
        (fun s reads => (s.registers .rdx, s.registers .rcx, s.flags, s.rip, reads))) =
    [.ok (0xf123456789abcdef, 0x100000001, 0xfedcba9876543210, 4100,
        [⟨.data, 0x300000001, 8⟩]),
      .ok (0xf123456789abcdef, 0x100000001, 0xfedcba9876543210, 4100,
        [⟨.data, 0x400000002, 8⟩]),
      .ok (0xf123456789abcdef, 0x100000001, 0xfedcba9876543210, 4100,
        [⟨.data, 0x600000004, 8⟩]),
      .ok (0xf123456789abcdef, 0x100000001, 0xfedcba9876543210, 4100,
        [⟨.data, 0xa00000008, 8⟩])] := by rfl

-- Extended base, index and destination jointly affect actual execution.
example (af : Bool) : nextView af
    (entry [0x4f, 0x8b, 0x14, 0x8f] registers (data64 0xc0000000c))
    (fun s reads => (s.registers .r10, s.registers .rdx, s.registers .r15,
      s.registers .r9, s.flags, s.rip, reads)) =
    .ok (0xf123456789abcdef, 0x1122334489abcdef, 0x400000000,
      0x200000003, 0xfedcba9876543210, 4100, [⟨.data, 0xc0000000c, 8⟩]) := by rfl

-- A destination/base alias must read and record the old high64 address.
example (af : Bool) : nextView af (entry [0x4d, 0x8b, 0x3f]
    registers (data64 0x400000000))
    (fun s reads => (s.registers .r15, s.registers .rdi, s.flags, s.rip, reads)) =
    .ok (0xf123456789abcdef, 0x200000000, 0xfedcba9876543210, 4099,
      [⟨.data, 0x400000000, 8⟩]) := by rfl

-- The same capture rule applies when the destination aliases a SIB index.
example (af : Bool) : nextView af
    (entry [0x4e, 0x8b, 0x0c, 0x8f] registers (data64 0xa0000000c))
    (fun s reads => (s.registers .r9, s.registers .rdi, s.rip, reads)) =
    .ok (0xf123456789abcdef, 0x200000000, 4100, [⟨.data, 0xa0000000c, 8⟩]) := by rfl

-- RSP destinations are DATA loads, not stack pops, and RSP may be the base.
example (af : Bool) : nextView af (entry [0x48, 0x8b, 0x24, 0x04]
    (fun register => if register = .rsp then 0x100000001
      else if register = .rax then 0x200000000 else 42)
    (data64 0x300000001))
    (fun s reads => (s.registers .rsp, s.registers .rax, s.flags, s.rip, reads)) =
    .ok (0xf123456789abcdef, 0x200000000, 0xfedcba9876543210, 4100,
      [⟨.data, 0x300000001, 8⟩]) := by rfl

-- An extended R12 index and base really participate in effective addressing.
example (af : Bool) : nextView af (entry [0x4b, 0x8b, 0x04, 0x24]
    (fun register => if register = .r12 then 0x300000003 else 42)
    (data64 0x600000006))
    (fun s reads => (s.registers .rax, s.registers .r12, s.rip, reads)) =
    .ok (0xf123456789abcdef, 0x300000003, 4100, [⟨.data, 0x600000006, 8⟩]) := by rfl

/-- The checked extended SIB store changes all eight expected bytes, retains
both neighbors and both permission maps, preserves registers/flags and has no
DATA reads. Source high bits differ from every address register. -/
example (af : Bool) : nextView af
    (entry [0x4f, 0x89, 0x14, 0x8f] registers (data64 0xc0000000c)
      (fun address => decide (0xc0000000c ≤ address.toNat ∧ address.toNat < 0xc00000014)))
    (fun s reads => ([s.memory.read 0xc0000000b, s.memory.read 0xc0000000c,
        s.memory.read 0xc0000000d, s.memory.read 0xc0000000e, s.memory.read 0xc0000000f,
        s.memory.read 0xc00000010, s.memory.read 0xc00000011, s.memory.read 0xc00000012,
        s.memory.read 0xc00000013, s.memory.read 0xc00000014],
      s.registers .r10, s.registers .r15, s.registers .r9, s.flags, s.rip,
      s.memory.writable 0xc00000013, s.memory.writable 0xc00000014,
      s.memory.executable 4096, s.memory.executable 0xc0000000c, reads)) =
    .ok ([some 0x5a, some 0x10, some 0x32, some 0x54, some 0x76, some 0x98,
      some 0xba, some 0xdc, some 0xfe, some 0x5a],
      0xfedcba9876543210, 0x400000000, 0x200000003, 0xfedcba9876543210, 4100,
      true, false, true, false, []) := by rfl

-- Extending the base leaves the separate source field and full word intact.
example (af : Bool) : nextView af (entry [0x49, 0x89, 0x3f]
    (fun register => if register = .r15 then 0x612345678 else 0x8877665544332211)
    (data64 0x612345678) (fun _ => true))
    (fun s reads => (loadQWord s.memory 0x612345678, s.memory.read 0x12345678,
      s.registers .r15, s.flags, s.rip, reads)) =
    .ok (.ok 0x8877665544332211, some 0x5a, 0x612345678,
      0xfedcba9876543210, 4099, []) := by rfl

-- Source=base also captures the full64 address and source word.
example (af : Bool) : nextView af (entry [0x4d, 0x89, 0x3f]
    (fun _ => 0x612345678) (data64 0x612345678) (fun _ => true))
    (fun s reads => (loadQWord s.memory 0x612345678, s.registers .r15, s.rip, reads)) =
    .ok (.ok 0x612345678, 0x612345678, 4099, []) := by rfl

-- Actual instruction execution rejects each upper-byte permission/domain gap.
example (af : Bool) : ([8197, 8198, 8199, 8200] : List Word).map (fun denied =>
    nextView af (entry [0x48, 0x89, 0x07] (fun _ => 8193)
      (data64 8193) (fun address => address != denied)) (fun s _ => s.rip)) =
    [.error (.writeDenied 8193), .error (.writeDenied 8193),
      .error (.writeDenied 8193), .error (.writeDenied 8193)] := by rfl
example (af : Bool) : ([8197, 8198, 8199, 8200] : List Word).map (fun missing =>
    nextView af (entry [0x48, 0x89, 0x07] (fun _ => 8193)
      (fun address => if address = missing then none else data64 8193 address)
      (fun _ => true)) (fun s _ => s.rip)) =
    [.error (.writeDenied 8193), .error (.writeDenied 8193),
      .error (.writeDenied 8193), .error (.writeDenied 8193)] := by rfl
example (af : Bool) : ([8197, 8198, 8199, 8200] : List Word).map (fun missing =>
    nextView af (entry [0x48, 0x8b, 0x07] (fun _ => 8193)
      (fun address => if address = missing then none else data64 8193 address))
      (fun s _ => s.rip)) =
    [.error (.inaccessibleData 8197), .error (.inaccessibleData 8198),
      .error (.inaccessibleData 8199), .error (.inaccessibleData 8200)] := by rfl

example (af : Bool) : nextView af (entry [0x48, 0x8b, 0x07]
    (fun _ => 0x7ffffffffffc) (fun _ => some 0)) (fun s _ => s.rip) =
    .error (.inaccessibleData 0x800000000000) := by rfl
example (af : Bool) : nextView af (entry [0x48, 0x89, 0x07]
    (fun _ => 0x7ffffffffffc) (fun _ => some 0) (fun _ => true)) (fun s _ => s.rip) =
    .error (.writeDenied 0x7ffffffffffc) := by rfl
example (af : Bool) : nextView af (entry [0x48, 0x8b, 0x07]
    (fun _ => 0xfffffffffffffffa) (fun _ => some 0)) (fun s _ => s.rip) =
    .error (.inaccessibleData 0xfffffffffffffffa) := by rfl
example (af : Bool) : nextView af (entry [0x48, 0x89, 0x07]
    (fun _ => 0xfffffffffffffffa) (fun _ => some 0) (fun _ => true)) (fun s _ => s.rip) =
    .error (.writeDenied 0xfffffffffffffffa) := by rfl

/-- Displacements, RIP-relative/absent bases and absent indices remain
unsupported, even with extension bits. B cannot turn encoded base5 into R13. -/
example : ([[0x48, 0x8b, 0x47, 0], [0x48, 0x89, 0x87, 0, 0, 0, 0],
      [0x48, 0x8b, 0x05], [0x49, 0x89, 0x05],
      [0x48, 0x8b, 0x04, 0x0d], [0x4b, 0x89, 0x04, 0x0d],
      [0x48, 0x8b, 0x04, 0x27], [0x49, 0x89, 0x04, 0x27]] : List (List Byte)).map
    (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error .unsupportedEncoding, .error .unsupportedEncoding,
      .error .unsupportedEncoding, .error .unsupportedEncoding,
      .error .unsupportedEncoding, .error .unsupportedEncoding,
      .error .unsupportedEncoding, .error .unsupportedEncoding] := by rfl

-- No new byte, word, non-W REX, address-size, segment or repeated-prefix forms.
example : ([[0x40, 0x89, 0x07], [0x47, 0x8b, 0x07],
      [0x66, 0x48, 0x89, 0x07], [0x67, 0x48, 0x8b, 0x07],
      [0x64, 0x48, 0x8b, 0x07], [0xf2, 0x48, 0x8b, 0x07],
      [0xf3, 0x48, 0x89, 0x07]] : List (List Byte)).map
    (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error .unsupportedEncoding, .error .unsupportedEncoding,
      .error .unsupportedEncoding, .error (.unsupportedOpcode 0x67),
      .error (.unsupportedOpcode 0x64), .error (.unsupportedOpcode 0xf2),
      .error .unsupportedEncoding] := by rfl
example : ([[0x48, 0x88, 0x07], [0x48, 0x8a, 0x07],
      [0x48, 0x48, 0x89, 0x07], [0x48, 0x66, 0x89, 0x07],
      [0xf0, 0x48, 0x89, 0x07]] : List (List Byte)).map
    (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error .unsupportedEncoding, .error .unsupportedEncoding,
      .error .unsupportedEncoding, .error .unsupportedEncoding,
      .error .unsupportedEncoding] := by rfl

-- Every required instruction byte is fetched with execute permission.
example : Sequential.decodeAt (entry [0x48]) =
    .error (.inaccessibleInstruction 4097) := by rfl
example : Sequential.decodeAt (entry [0x48, 0x89]) =
    .error (.inaccessibleInstruction 4098) := by rfl
example : Sequential.decodeAt (entry [0x49, 0x8b, 0x04]) =
    .error (.inaccessibleInstruction 4099) := by rfl
example : Sequential.decodeAt { entry [0x4f, 0x89, 0x14, 0x8f] with
    memory := { (entry [0x4f, 0x89, 0x14, 0x8f]).memory with
      executable := fun address => decide (address ≠ 4099) } } =
    .error (.inaccessibleInstruction 4099) := by rfl

-- Read-only CFG admission excludes stores structurally, including a same-value
-- store, but continues to admit full-width loads and register operations.
example : Sequential.CFG.analyze [0x48, 0x89, 0x07, 0xc3] =
    .error (.unsupportedInstruction 0) := by rfl
example : Sequential.CFG.analyze [0x48, 0x89, 0xc0, 0x4f, 0x89, 0x14, 0x8f, 0xc3] =
    .error (.unsupportedInstruction 3) := by rfl
example : (Sequential.CFG.analyze [0x4f, 0x8b, 0x14, 0x8f, 0xc3]).isOk = true := by rfl

-- Actual operand success distinguishes DATA8 from STACK8 and retains DATA4.
example : Sequential.OperandReadSucceeds
    (entry [] (fun _ => 0) (data64 8193)) ⟨.data, 8193, 8⟩ := by exact ⟨_, rfl⟩
example : Sequential.OperandReadSucceeds
    (entry [] (fun _ => 0) (data64 8193)) ⟨.data, 8193, 4⟩ := by exact ⟨rfl, _, rfl⟩
example : ¬ Sequential.OperandReadSucceeds
    (entry [] (fun _ => 0) (data64 8193)) ⟨.data, 8193, 7⟩ := by
  intro impossible
  exact (by decide : (7 : Nat) ≠ 4) impossible.1

def tsoEntry (bytes : List Byte) : OS.TSO.State :=
  ⟨(entry bytes).memory, [⟨OS.Threads.Context.ofState (entry bytes), false, []⟩]⟩

-- Exercise the real old concurrent issue operation, not a decoder alias.
example : ([[0x48, 0x89, 0x07], [0x49, 0x8b, 0x0f],
      [0x4f, 0x89, 0x14, 0x8f], [0x4b, 0x8b, 0x04, 0x24]] : List (List Byte)).map
    (fun bytes => (OS.TSO.step (tsoEntry bytes) (.issue 0)).map (fun _ => ())) =
    [.error (.machine (.unsupportedOpcode 0x48)), .error (.machine (.unsupportedOpcode 0x49)),
      .error (.machine (.unsupportedOpcode 0x4f)), .error (.machine (.unsupportedOpcode 0x4b))] := by rfl

example : Sequential.Literals.instruction (.loadMem64 .r10 (.indexed .r15 .r9 2)) =
    "(.loadMem64 .r10 (.indexed .r15 .r9 2))" := by rfl
example : Sequential.Literals.instruction (.storeMem64 (.base .r12) .r8) =
    "(.storeMem64 (.base .r12) .r8)" := by rfl

end EDSL.Tests.SequentialMemory64

#audit_edsl
