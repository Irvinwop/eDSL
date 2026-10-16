/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.OS.TSO.Model
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialMoves
open X86

/-- Finite executable instruction bytes and separately mapped ordinary RAM. -/
def entry (code : List Byte) (registers : Register → Word := fun _ => 0)
    (data : Word → Option Byte := fun _ => none)
    (writable : Word → Bool := fun _ => false) : State where
  registers := registers
  flags := 0xabcdef
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

def registerInput : Register → Word
  | .rax => 0x1111111110000011 | .rcx => 0x2222222220000022
  | .rdx => 0x3333333330000033 | .rbx => 0x4444444440000044
  | .rsp => 0x5555555550000055 | .rbp => 0x6666666660000066
  | .rsi => 0xfedcba9880000001 | .rdi => 0x77777777f00000ff
  | _ => 0xabcdef0123456789

/-- Each low-register destination is tested through the actual byte decoder
and machine step. In particular ESP/EBP writes are not mistaken for memory,
and ESI<-ESI must clear the high half. These are literal x86 operand vectors,
not a second implementation of the ModRM bit extraction. -/
example (af : Bool) :
    ([([0x89, 0xf0], .rax), ([0x89, 0xf1], .rcx),
      ([0x89, 0xf2], .rdx), ([0x89, 0xf3], .rbx),
      ([0x89, 0xf4], .rsp), ([0x89, 0xf5], .rbp),
      ([0x89, 0xf6], .rsi), ([0x89, 0xf7], .rdi)] : List (List Byte × Register)).map
      (fun (bytes, destination) => nextView af (entry bytes registerInput)
        (fun s reads => (s.registers destination, s.flags, s.rip, reads))) =
    [.ok (0x80000001, 0xabcdef, 4098, []), .ok (0x80000001, 0xabcdef, 4098, []),
      .ok (0x80000001, 0xabcdef, 4098, []), .ok (0x80000001, 0xabcdef, 4098, []),
      .ok (0x80000001, 0xabcdef, 4098, []), .ok (0x80000001, 0xabcdef, 4098, []),
      .ok (0x80000001, 0xabcdef, 4098, []), .ok (0x80000001, 0xabcdef, 4098, [])] := by rfl

/-- With precisely the same ModRM bytes, 8B reverses the operand direction.
Every low-register source has different low bits; sign extension, swapped
operands, high-half retention and the self-move identity bug are observable. -/
example (af : Bool) :
    ([[0x8b, 0xf0], [0x8b, 0xf1], [0x8b, 0xf2], [0x8b, 0xf3],
      [0x8b, 0xf4], [0x8b, 0xf5], [0x8b, 0xf6], [0x8b, 0xf7]] : List (List Byte)).map
      (fun bytes => nextView af (entry bytes registerInput)
        (fun s reads => (s.registers .rsi, s.flags, s.rip, reads))) =
    [.ok (0x10000011, 0xabcdef, 4098, []), .ok (0x20000022, 0xabcdef, 4098, []),
      .ok (0x30000033, 0xabcdef, 4098, []), .ok (0x40000044, 0xabcdef, 4098, []),
      .ok (0x50000055, 0xabcdef, 4098, []), .ok (0x60000066, 0xabcdef, 4098, []),
      .ok (0x80000001, 0xabcdef, 4098, []), .ok (0xf00000ff, 0xabcdef, 4098, [])] := by rfl

/-- This observation also detects collateral writes outside the destination,
including extension registers. -/
example (af : Bool) : nextView af (entry [0x89, 0xf1] registerInput)
    (fun s reads => (s.registers .rcx, s.registers .rsi, s.registers .rax,
      s.registers .rsp, s.registers .r8, s.registers .r15, s.flags, s.rip, reads)) =
    .ok (0x80000001, 0xfedcba9880000001, 0x1111111110000011,
      0x5555555550000055, 0xabcdef0123456789, 0xabcdef0123456789, 0xabcdef, 4098, []) := by rfl

def wordBytes (base : Word) : Word → Option Byte := fun address =>
  if address = base then some 0x98
  else if address = base + 1 then some 0xba
  else if address = base + 2 then some 0xdc
  else if address = base + 3 then some 0xfe
  else some 0x5a

/-- RDI is both destination and a >4GiB base. The read event and result must
use the old RDI; the result is unsigned, despite its set bit31. -/
example (af : Bool) : nextView af
    (entry [0x8b, 0x3f] (fun _ => 0x600000004) (wordBytes 0x600000004))
    (fun s reads => (s.registers .rdi, s.registers .rsi, s.flags, s.rip, reads)) =
    .ok (0xfedcba98, 0x600000004, 0xabcdef, 4098, [⟨.data, 0x600000004, 4⟩]) := by rfl

/-- The memory register field covers every low-register destination too,
including ESP/EBP and the preserved legacy EAX encoding. -/
example (af : Bool) :
    ([([0x8b, 0x07], .rax), ([0x8b, 0x0f], .rcx),
      ([0x8b, 0x17], .rdx), ([0x8b, 0x1f], .rbx),
      ([0x8b, 0x27], .rsp), ([0x8b, 0x2f], .rbp),
      ([0x8b, 0x37], .rsi), ([0x8b, 0x3f], .rdi)] : List (List Byte × Register)).map
      (fun (bytes, destination) => nextView af
        (entry bytes (fun _ => 0x600000004) (wordBytes 0x600000004))
        (fun s _ => s.registers destination)) =
    [.ok 0xfedcba98, .ok 0xfedcba98, .ok 0xfedcba98, .ok 0xfedcba98,
      .ok 0xfedcba98, .ok 0xfedcba98, .ok 0xfedcba98, .ok 0xfedcba98] := by rfl

/-- Independently different source values exercise every low-register field
in the store direction, including source=base and the legacy ESI store. -/
example (af : Bool) :
    ([[0x89, 0x07], [0x89, 0x0f], [0x89, 0x17], [0x89, 0x1f],
      [0x89, 0x27], [0x89, 0x2f], [0x89, 0x37], [0x89, 0x3f]] : List (List Byte)).map
      (fun bytes => nextView af
        (entry bytes (fun register => if register = .rdi then 8192 else registerInput register)
          (wordBytes 8192) (fun _ => true))
        (fun s _ => loadDWord s.memory 8192)) =
    [.ok (.ok 0x10000011), .ok (.ok 0x20000022), .ok (.ok 0x30000033), .ok (.ok 0x40000044),
      .ok (.ok 0x50000055), .ok (.ok 0x60000066), .ok (.ok 0x80000001), .ok (.ok 8192)] := by rfl

def indexedRegisters : Register → Word := fun register =>
  if register = .rdi then 0x200000000 else if register = .rcx then 0x100000001
  else if register = .rdx then 0xaabbccdd12345678 else 0x55

def scaleData (address : Word) : Option Byte :=
  if address = 0x300000001 then some 0x81
  else if address = 0x300000002 then some 0x12
  else if address = 0x300000003 then some 0x34
  else if address = 0x300000004 then some 0x80
  else if address = 0x400000002 then some 0x92
  else if address = 0x400000003 then some 0x23
  else if address = 0x400000004 then some 0x45
  else if address = 0x400000005 then some 0x91
  else if address = 0x600000004 then some 0xa3
  else if address = 0x600000005 then some 0x34
  else if address = 0x600000006 then some 0x56
  else if address = 0x600000007 then some 0xa2
  else if address = 0xa00000008 then some 0xb4
  else if address = 0xa00000009 then some 0x45
  else if address = 0xa0000000a then some 0x67
  else if address = 0xa0000000b then some 0xb3
  else none

/-- All four SIB scales use full64 base AND index. Distinct values are mapped
only at the four independently specified mathematical effective addresses;
incorrect scaling and address truncation cannot pass by reading common data. -/
example (af : Bool) :
    ([[0x8b, 0x14, 0x0f], [0x8b, 0x14, 0x4f],
      [0x8b, 0x14, 0x8f], [0x8b, 0x14, 0xcf]] : List (List Byte)).map
      (fun bytes => nextView af (entry bytes indexedRegisters scaleData)
        (fun s reads => (s.registers .rdx, s.flags, s.rip, reads))) =
    [.ok (0x80341281, 0xabcdef, 4099, [⟨.data, 0x300000001, 4⟩]),
      .ok (0x91452392, 0xabcdef, 4099, [⟨.data, 0x400000002, 4⟩]),
      .ok (0xa25634a3, 0xabcdef, 4099, [⟨.data, 0x600000004, 4⟩]),
      .ok (0xb36745b4, 0xabcdef, 4099, [⟨.data, 0xa00000008, 4⟩])] := by rfl

/-- All four scales also select the store destination, rather than affecting
only load decoding. Only one of the four widely separated targets may change. -/
example (af : Bool) :
    ([[0x89, 0x14, 0x0f], [0x89, 0x14, 0x4f],
      [0x89, 0x14, 0x8f], [0x89, 0x14, 0xcf]] : List (List Byte)).map
      (fun bytes => nextView af
        (entry bytes indexedRegisters (fun _ => some 0x5a) (fun _ => true))
        (fun s reads => (s.memory.read 0x300000001, s.memory.read 0x400000002,
          s.memory.read 0x600000004, s.memory.read 0xa00000008, s.rip, reads))) =
    [.ok (some 0x78, some 0x5a, some 0x5a, some 0x5a, 4099, []),
      .ok (some 0x5a, some 0x78, some 0x5a, some 0x5a, 4099, []),
      .ok (some 0x5a, some 0x5a, some 0x78, some 0x5a, 4099, []),
      .ok (some 0x5a, some 0x5a, some 0x5a, some 0x78, 4099, [])] := by rfl

/-- Loading ECX also aliases the SIB index. This differs from base aliasing:
the old high index bits must participate in both the address and read event. -/
example (af : Bool) : nextView af
    (entry [0x8b, 0x0c, 0x8f] indexedRegisters (wordBytes 0x600000004))
    (fun s reads => (s.registers .rcx, s.registers .rdi, s.registers .rdx,
      s.flags, s.rip, reads)) =
    .ok (0xfedcba98, 0x200000000, 0xaabbccdd12345678,
      0xabcdef, 4099, [⟨.data, 0x600000004, 4⟩]) := by rfl

/-- A legal non-RDI base and destination are exercised at an unaligned address. -/
example (af : Bool) : nextView af (entry [0x8b, 0x1a]
    (fun register => if register = .rdx then 8193 else 0xfedcba9876543210)
    (wordBytes 8193))
    (fun s reads => (s.registers .rbx, s.registers .rdx, s.flags, s.rip, reads)) =
    .ok (0xfedcba98, 8193, 0xabcdef, 4098, [⟨.data, 8193, 4⟩]) := by rfl

/-- RSP is a legal SIB base even though a missing SIB index is unsupported.
Writing ESP still performs a data read at the old full-width address; it does
not reinterpret the operand as a stack pop or use the newly narrowed RSP. -/
example (af : Bool) : nextView af (entry [0x8b, 0x24, 0x04]
    (fun register => if register = .rsp then 0x100000001
      else if register = .rax then 0x200000000 else 0)
    (wordBytes 0x300000001))
    (fun s reads => (s.registers .rsp, s.registers .rax, s.rip, reads)) =
    .ok (0xfedcba98, 0x200000000, 4099, [⟨.data, 0x300000001, 4⟩]) := by rfl

/-- The actual SIB store writes four little-endian low32 bytes, retains both
neighbors and all permission queries, and produces no operand-read event. -/
example (af : Bool) : nextView af
    (entry [0x89, 0x14, 0x8f] indexedRegisters (wordBytes 0x600000004)
      (fun address => decide (0x600000004 ≤ address.toNat ∧ address.toNat < 0x600000008)))
    (fun s reads => (s.memory.read 0x600000003, s.memory.read 0x600000004,
      s.memory.read 0x600000005, s.memory.read 0x600000006, s.memory.read 0x600000007,
      s.memory.read 0x600000008, s.registers .rdx, s.registers .rcx, s.flags, s.rip,
      s.memory.writable 0x600000007, s.memory.writable 0x600000008,
      s.memory.executable 0x600000004, s.memory.executable 4096, reads)) =
    .ok (some 0x5a, some 0x78, some 0x56, some 0x34, some 0x12, some 0x5a,
      0xaabbccdd12345678, 0x100000001, 0xabcdef, 4099, true, false, false, true, []) := by rfl

/-- Source and high64 base are the same register. Narrowing the source must
not narrow the address; the unchanged RDI and explicit bytes detect either bug. -/
example (af : Bool) : nextView af (entry [0x89, 0x3f]
    (fun _ => 0x612345678) (wordBytes 0x612345678) (fun _ => true))
    (fun s reads => (s.memory.read 0x612345678, s.memory.read 0x612345679,
      s.memory.read 0x61234567a, s.memory.read 0x61234567b,
      s.memory.read 0x12345678, s.registers .rdi, s.flags, s.rip, reads)) =
    .ok (some 0x78, some 0x56, some 0x34, some 0x12,
      some 0x5a, 0x612345678, 0xabcdef, 4098, []) := by rfl

/-- An indexed store also supports source=index and must retain the full64
index register, while storing only its low32 value. -/
example (af : Bool) : nextView af
    (entry [0x89, 0x0c, 0x8f] indexedRegisters (wordBytes 0x600000004) (fun _ => true))
    (fun s reads => (s.memory.read 0x600000004, s.memory.read 0x600000005,
      s.memory.read 0x600000006, s.memory.read 0x600000007,
      s.registers .rcx, s.flags, s.rip, reads)) =
    .ok (some 1, some 0, some 0, some 0, 0x100000001, 0xabcdef, 4099, []) := by rfl

/-- The fourth byte is part of the operation: a three-byte readable/writable
prefix neither completes a load nor permits a partially visible store. -/
example (af : Bool) : nextView af
    (entry [0x8b, 0x0f] (fun _ => 8192)
      (fun address => if 8192 ≤ address.toNat ∧ address.toNat < 8195 then some 0 else none))
    (fun s _ => s.rip) = .error (.inaccessibleData 8195) := by rfl
example (af : Bool) : nextView af
    (entry [0x89, 0x07] (fun _ => 8192) (wordBytes 8192)
      (fun address => decide (8192 ≤ address.toNat ∧ address.toNat < 8195)))
    (fun s _ => s.rip) = .error (.writeDenied 8192) := by rfl
example (af : Bool) : nextView af
    (entry [0x89, 0x07] (fun _ => 8192)
      (fun address => if address = 8195 then none else some 0) (fun _ => true))
    (fun s _ => s.rip) = .error (.writeDenied 8192) := by rfl

/-- Mapped bytes and affirmative permissions cannot bypass canonicality or
the whole-operand nonwrap check, including a fault after valid leading bytes. -/
example (af : Bool) : nextView af
    (entry [0x8b, 0x0f] (fun _ => 0x7ffffffffffd) (fun _ => some 0))
    (fun s _ => s.rip) = .error (.inaccessibleData 0x800000000000) := by rfl
example (af : Bool) : nextView af
    (entry [0x89, 0x07] (fun _ => 0x7ffffffffffd) (fun _ => some 0) (fun _ => true))
    (fun s _ => s.rip) = .error (.writeDenied 0x7ffffffffffd) := by rfl
example (af : Bool) : nextView af
    (entry [0x8b, 0x0f] (fun _ => 0xfffffffffffffffe) (fun _ => some 0))
    (fun s _ => s.rip) = .error (.inaccessibleData 0xfffffffffffffffe) := by rfl
example (af : Bool) : nextView af
    (entry [0x89, 0x07] (fun _ => 0xfffffffffffffffe) (fun _ => some 0) (fun _ => true))
    (fun s _ => s.rip) = .error (.writeDenied 0xfffffffffffffffe) := by rfl

/-- The last nonwrapping four-byte word in the upper canonical region is
valid. Rejecting all high addresses would incorrectly satisfy only negatives. -/
example (af : Bool) : nextView af
    (entry [0x8b, 0x0f] (fun _ => 0xfffffffffffffffc) (wordBytes 0xfffffffffffffffc))
    (fun s reads => (s.registers .rcx, s.rip, reads)) =
    .ok (0xfedcba98, 4098, [⟨.data, 0xfffffffffffffffc, 4⟩]) := by rfl

/-- Every preexisting MOV encoding wins before the generic fallback, including
both memory directions. Existing theorem/client representations stay stable. -/
example : ([[0x89, 0x37], [0x89, 0x06], [0x89, 0xf8], [0x89, 0xf0],
      [0x8b, 0x07], [0x8b, 0x06]] : List (List Byte)).map
    (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.ok (.legacy .storeEsiRdi), .ok (.legacy .storeEaxRsi),
      .ok (.legacy .movEaxEdi), .ok (.legacy .movEaxEsi),
      .ok (.legacy .loadEaxRdi), .ok (.legacy .loadEaxRsi)] := by rfl

/-- Prefixes, displacements, RIP-relative and missing SIB operands are outside
this profile. In particular no-index SIB cannot be lowered to a 2-byte base
instruction: it would silently give the wrong encoded length. -/
example : Sequential.decodeAt (entry [0x66, 0x89, 0xc0]) =
    .error (.unsupportedOpcode 0x66) := by rfl
example : Sequential.decodeAt (entry [0x67, 0x8b, 0x0f]) =
    .error (.unsupportedOpcode 0x67) := by rfl
example : Sequential.decodeAt (entry [0xf0, 0x89, 0x07]) =
    .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (entry [0x48, 0x89, 0x07]) =
    .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (entry [0x49, 0x8b, 0x0f]) =
    .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (entry [0x89, 0x47, 0]) = .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (entry [0x8b, 0x8f, 0, 0, 0, 0]) = .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (entry [0x8b, 0x05, 0, 0, 0, 0]) = .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (entry [0x89, 0x04, 0x27]) = .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (entry [0x8b, 0x04, 0x0d]) = .error .unsupportedEncoding := by rfl
example : Sequential.decodeAt (entry [0x89]) = .error (.inaccessibleInstruction 4097) := by rfl
example : Sequential.decodeAt (entry [0x8b, 0x04]) = .error (.inaccessibleInstruction 4098) := by rfl

/-- Fetch permission remains necessary for every encoded byte, including the
new third SIB byte. Readable code bytes alone cannot authorize decoding. -/
example : Sequential.decodeAt { entry [0x89, 0x14, 0x8f] with
    memory := { (entry [0x89, 0x14, 0x8f]).memory with
      executable := fun address => decide (address = 4096 ∨ address = 4097) } } =
    .error (.inaccessibleInstruction 4098) := by rfl

/-- Actual discovery retains its read-only policy even when a store might
write the existing value, and rejects a later store after valid register code.
The positive case confirms register MOV and load admission were retained. -/
example : Sequential.CFG.analyze [0x89, 0x07, 0xc3] =
    .error (.unsupportedInstruction 0) := by rfl
example : Sequential.CFG.analyze [0x89, 0x14, 0x8f, 0xc3] =
    .error (.unsupportedInstruction 0) := by rfl
example : Sequential.CFG.analyze [0x89, 0xf1, 0x89, 0x07, 0xc3] =
    .error (.unsupportedInstruction 2) := by rfl
example : (Sequential.CFG.analyze [0x89, 0xf1, 0x8b, 0x0f, 0xc3]).isOk = true := by rfl

def tsoEntry (bytes : List Byte) : OS.TSO.State :=
  ⟨(entry bytes).memory, [⟨OS.Threads.Context.ofState (entry bytes), false, []⟩]⟩

/-- Check the real TSO issue entry point rather than merely its decoder alias:
new ordinary sequential stores cannot enter its FIFO/atomicity contracts. -/
example : ([[0x89, 0x07], [0x8b, 0x0f], [0x89, 0xf1], [0x8b, 0xf1],
      [0x89, 0x14, 0x8f], [0x8b, 0x14, 0x8f]] : List (List Byte)).map
    (fun bytes => (OS.TSO.step (tsoEntry bytes) (.issue 0)).map (fun _ => ())) =
    [.error (.machine .unsupportedEncoding), .error (.machine .unsupportedEncoding),
      .error (.machine .unsupportedEncoding), .error (.machine .unsupportedEncoding),
      .error (.machine .unsupportedEncoding), .error (.machine .unsupportedEncoding)] := by rfl

end EDSL.Tests.SequentialMoves

#audit_edsl
