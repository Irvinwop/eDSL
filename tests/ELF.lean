/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.Loader
import EDSL.Examples.Compiler.Increment
import EDSL.Audit

namespace EDSL.Tests.ELF
open X86 OS.AddressSpace

set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Handwritten ELF64LE: entry 0x400080, one RX LOAD with four file bytes and
-- eight memory bytes. File and virtual page offsets are both 128.
def file : List Byte := [
  0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  2, 0, 62, 0, 1, 0, 0, 0, 0x80, 0, 0x40, 0, 0, 0, 0, 0,
  0x40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 64, 0, 56, 0, 1, 0, 0, 0, 0, 0, 0, 0,
  1, 0, 0, 0, 5, 0, 0, 0, 0x80, 0, 0, 0, 0, 0, 0, 0,
  0x80, 0, 0x40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  4, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0,
  0, 0x10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0x8d, 0x47, 0x01, 0xc3]

def image : EDSL.ELF.Image := ⟨0x400080, [⟨128, 0x400080, 4, 8, 5, 4096⟩]⟩

def prior : Space where
  cells address :=
    match address.toNat with
    | 32768 => some ⟨0, readWrite⟩
    | 32769 => some ⟨0x20, readWrite⟩
    | 32770 | 32771 | 32772 | 32773 | 32774 | 32775 => some ⟨0, readWrite⟩
    | 65536 => some ⟨0xa5, inaccessible⟩
    | _ => none

-- This is a satisfiable loader + caller + machine execution, not a field fixture
-- assertion: the caller must observe modular wraparound and the preserved RET.
def observed : Option (Word × Word × Word × Option Byte × Option Byte) := do
  let loaded ← (EDSL.ELF.load file prior).toOption
  let state : State := {
    registers := fun register => if register = .rdi then 0xffffffff
      else if register = .rsp then 32768 else 0xfeedface00000000
    rip := EDSL.ELF.codeAddress loaded.image
    flags := 0x202
    memory := toMemory loaded.space }
  let result ← (run 2 state).toOption
  return (result.state.registers .rax, result.state.rip, result.state.registers .rsp,
    result.state.memory.read 0x400084, contents loaded.space 65536)

example : observed = some (0, 8192, 32776, some 0, some 0xa5) := by decide

def observedPermissions : Option (Bool × Bool) := do
  let loaded ← (EDSL.ELF.load file prior).toOption
  return ((toMemory loaded.space).writable 0x400080, (toMemory loaded.space).executable 0x400080)

example : observedPermissions = some (false, true) := by decide

-- Full observed bytes and the selected window have kernel-checked evidence.
theorem parsed : EDSL.ELF.parse file = .ok image :=
  EDSL.ELF.checkParsed_sound file image (by decide)

theorem entry_checked : EDSL.ELF.checkEntry file image Examples.Compiler.Increment.bytes = true := by
  decide

example (caller : Space) : CodeAt (toMemory (EDSL.ELF.install file image caller))
    0x400080 Examples.Compiler.Increment.bytes :=
  EDSL.ELF.checked_entry_code file image _ caller entry_checked

def errorIs (candidate : List Byte) (expected : EDSL.ELF.Error) : Bool :=
  match EDSL.ELF.parse candidate with
  | .error observed => decide (observed = expected)
  | .ok _ => false

example : errorIs (file.take 63) .truncated = true := by decide
example : errorIs (file.take 110) .truncated = true := by decide
example : errorIs (file.set 5 2) .unsupportedFormat = true := by decide
example : errorIs (file.set 64 2) (.unsupportedProgramHeader 2) = true := by decide
example : errorIs (file.set 96 5) .invalidImage = true := by decide
example : errorIs (file.set 104 3) .invalidImage = true := by decide
example : errorIs (file.set 24 0x84) .invalidImage = true := by decide
example : errorIs (file.set 68 6) .invalidImage = true := by decide

-- An entry that is still file-backed may leave too few bytes for the contract.
def checkIncrement (candidate : List Byte) : Bool :=
  match EDSL.ELF.parse candidate with
  | .error _ => false
  | .ok parsedImage => EDSL.ELF.checkEntry candidate parsedImage Examples.Compiler.Increment.bytes

example : checkIncrement (file.set 24 0x81) = false := by decide
example : checkIncrement (file.set 130 2) = false := by decide

-- These bytes would match RX BSS, so the file-backed-window check itself matters.
example : EDSL.ELF.checkEntry (file.set 24 0x81) { image with entry := 0x400081 }
    [0x47, 0x01, 0xc3, 0] = false := by decide

example : EDSL.ELF.Segment.valid 132 ⟨128, 12416, 4, 8, 5, 3⟩ = false := by decide

example : EDSL.ELF.Segment.valid 132 ⟨128, 0x800000000080, 4, 8, 5, 4096⟩ = false := by decide

-- Disjoint byte intervals sharing one page must not pass collision validation.
def samePage : EDSL.ELF.Image :=
  ⟨0x400080, [⟨128, 0x400080, 4, 8, 5, 4096⟩, ⟨144, 0x400090, 1, 1, 4, 4096⟩]⟩

example : EDSL.ELF.valid (file ++ List.replicate 128 0) samePage = false := by decide

-- A hidden caller cell in page padding still prevents a load over that page.
def collision : Space where
  cells address := if address = 0x400000 then some ⟨0x5a, inaccessible⟩ else prior.cells address

def collisionRejected : Bool :=
  match EDSL.ELF.load file collision with
  | .error .mappingCollision => true
  | _ => false

example : collisionRejected = true := by decide

end EDSL.Tests.ELF

#audit_edsl
