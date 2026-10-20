/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.AtomicAdd64
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.AtomicAdd64
open X86

/-- Literal little-endian input bytes and independently protected neighbors.
No qword write/extraction helper constructs the test inputs. -/
def data (bytes : List Byte) : Memory where
  read address :=
    if address = 4096 then some 0x90
    else if address = 65535 then some 0x5a
    else if address = 65544 then some 0xa5
    else if 65536 ≤ address.toNat ∧ address.toNat < 65544
      then bytes[address.toNat - 65536]?
    else none
  executable := fun address => address == 4096
  writable := fun address => decide (65536 ≤ address.toNat ∧ address.toNat < 65544)

structure View where
  label : FetchAddEvent64
  readback : Except Error Word
  bytes : List (Option Byte)
  code : Option Byte
  codeExecutable : Bool
  highWritable : Bool
  outsideWritable : Bool
  deriving Repr

def observe (memory : Memory) (delta : Word) : Except Error View := do
  let (final, label) ← fetchAddQWord memory 65536 delta
  return ⟨label, loadQWord final 65536,
    [65535,65536,65537,65538,65539,65540,65541,65542,65543,65544].map final.read,
    final.read 4096, final.executable 4096, final.writable 65543, final.writable 65544⟩

/-- A carry out of the low dword must reach the existing high dword. The
literal byte/readback oracle also catches wrong byte order and overwide writes. -/
example : observe (data [0xff,0xff,0xff,0xff,0x12,0x34,0x56,0x78]) 1 = .ok {
    label := ⟨1, ⟨65536,0x78563412ffffffff,0x7856341300000000⟩⟩
    readback := .ok 0x7856341300000000
    bytes := [some 0x5a,some 0,some 0,some 0,some 0,some 0x13,some 0x34,some 0x56,
      some 0x78,some 0xa5]
    code := some 0x90
    codeExecutable := true
    highWritable := true
    outsideWritable := false } := by rfl

-- Full-width wrap, a high-bit argument and a high-bit carry have distinct oracles.
example : observe (data [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff]) 1 = .ok {
    label := ⟨1, ⟨65536,0xffffffffffffffff,0⟩⟩
    readback := .ok 0
    bytes := [some 0x5a,some 0,some 0,some 0,some 0,some 0,some 0,some 0,some 0,some 0xa5]
    code := some 0x90
    codeExecutable := true
    highWritable := true
    outsideWritable := false } := by rfl
example : (observe (data [0xff,0xff,0xff,0xff,0x12,0x34,0x56,0x78]) 0x8000000000000001).map
    (fun view => (view.label,view.readback)) =
    .ok (⟨0x8000000000000001,⟨65536,0x78563412ffffffff,0xf856341300000000⟩⟩,
      .ok 0xf856341300000000) := by rfl
example : (observe (data [0,0,0,0,0,0,0,0x80]) 0x8000000000000001).map
    (fun view => (view.label,view.readback)) =
    .ok (⟨0x8000000000000001,⟨65536,0x8000000000000000,1⟩⟩,.ok 1) := by rfl

/-- Delta zero still returns the complete high-half old value and an event. -/
example : (observe (data [0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef]) 0).map
    (fun view => (view.label,view.readback,view.bytes)) =
    .ok (⟨0,⟨65536,0xefcdab8967452301,0xefcdab8967452301⟩⟩,.ok 0xefcdab8967452301,
      [some 0x5a,some 1,some 0x23,some 0x45,some 0x67,some 0x89,some 0xab,some 0xcd,
        some 0xef,some 0xa5]) := by rfl

def consecutive : Except Error (FetchAddEvent64 × FetchAddEvent64 × Except Error Word) := do
  let (middle, first) ← fetchAddQWord (data [0xff,0xff,0xff,0xff,0,0,0,0]) 65536 1
  let (final, second) ← fetchAddQWord middle 65536 0xffffffff00000000
  return (first,second,loadQWord final 65536)

/-- The second operation must read current memory, not an initial snapshot;
its old value is above 2^32 and its final value wraps at 2^64. -/
example : consecutive = .ok
    (⟨1,⟨65536,0xffffffff,0x100000000⟩⟩,
      ⟨0xffffffff00000000,⟨65536,0x100000000,0⟩⟩,.ok 0) := by rfl

/-- A general current-memory link follows from old/readback contracts. This
is a sequential primitive property, with no scheduler/history claim. -/
theorem consecutive_old {memory : Memory} {address firstDelta secondDelta : Word}
    {first second : Memory × FetchAddEvent64}
    (firstSuccess : fetchAddQWord memory address firstDelta = .ok first)
    (secondSuccess : fetchAddQWord first.1 address secondDelta = .ok second) :
    second.2.event.before = first.2.event.after := by
  have before := fetchAddQWord_old first.1 address secondDelta second secondSuccess
  have after := fetchAddQWord_readback memory address firstDelta first firstSuccess
  rw [before] at after
  exact Except.ok.inj after

-- Every current writable bit is required, including every upper byte at delta0.
example : ([65536,65537,65538,65539,65540,65541,65542,65543] : List Word).map
    (fun denied => (fetchAddQWord { data [1,2,3,4,5,6,7,8] with
      writable := fun address => address != denied } 65536 0).map (fun _ => true)) =
    List.replicate 8 (.error (.writeDenied 65536)) := by rfl

-- Present low bytes do not authorize a missing upper byte, even for delta0.
example : ([65536,65537,65538,65539,65540,65541,65542,65543] : List Word).map
    (fun missing => (fetchAddQWord { data [1,2,3,4,5,6,7,8] with
      read := fun address => if address = missing then none
        else (data [1,2,3,4,5,6,7,8]).read address } 65536 0).map (fun _ => true)) =
    List.replicate 8 (.error (.writeDenied 65536)) := by rfl

-- Unchanged low bytes also cannot exempt an upper-byte permission for high deltas.
example : ([65540,65541,65542,65543] : List Word).map
    (fun denied => (fetchAddQWord { data [1,2,3,4,5,6,7,8] with
      writable := fun address => address != denied } 65536 0x8000000000000000).map
      (fun _ => true)) = List.replicate 4 (.error (.writeDenied 65536)) := by rfl

def accessible : Memory where
  read := fun _ => some 0xff
  executable := fun _ => false
  writable := fun _ => true

-- Mapped and writable bytes cannot bypass alignment/canonical/no-wrap gates.
example : ([65537,65540,65543,0x800000000000,0x7fffffffffff,
    0xfffffffffffffff9,0xffffffffffffffff] : List Word).map
    (fun address => (fetchAddQWord accessible address 0).map (fun _ => true)) =
    [.error (.unsupportedAtomicAddress 65537),.error (.unsupportedAtomicAddress 65540),
      .error (.unsupportedAtomicAddress 65543),.error (.unsupportedAtomicAddress 0x800000000000),
      .error (.unsupportedAtomicAddress 0x7fffffffffff),
      .error (.unsupportedAtomicAddress 0xfffffffffffffff9),
      .error (.unsupportedAtomicAddress 0xffffffffffffffff)] := by rfl

-- The address gate precedes preflight; lack of bytes does not change that error.
example : fetchAddQWord { accessible with
    read := fun _ => none
    writable := fun _ => false } 65537 0 = .error (.unsupportedAtomicAddress 65537) := by rfl

-- Legal edge qwords must not be overrejected by an off-by-one/wrap check.
example : ([0x7ffffffffff8,0xffff800000000000,0xfffffffffffffff8] : List Word).map
    (fun address => (fetchAddQWord accessible address 1).map
      (fun result => (result.2.event.before,result.2.event.after,loadQWord result.1 address))) =
    [.ok (0xffffffffffffffff,0,.ok 0),.ok (0xffffffffffffffff,0,.ok 0),
      .ok (0xffffffffffffffff,0,.ok 0)] := by rfl

end EDSL.Tests.AtomicAdd64

#audit_edsl
