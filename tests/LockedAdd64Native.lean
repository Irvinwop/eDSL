/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.LockedAdd64
import EDSL.Audit

set_option warningAsError true

/- Runtime replay of project-owned hardware observations. No observation is
promoted to a theorem or to a universal CPU/OS/TSO/source-order claim. The actual
LockedAdd64.step supplies ALL ISA/arithmetic/flag semantics. The capture supplies
expected full words and effective flags; there is no second flag calculator. -/
namespace EDSL.Tests.LockedAdd64Native
open X86

def allRegisters : List Register :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

def directBases : List Nat := [0,1,2,3,6,7,8,9,10,11,14,15]

structure Capture where
  id : Nat
  source : Nat
  base : Nat
  ignoredX : Nat
  vector : Nat
  beforePC : Word
  afterPC : Word
  beforeCode : List Byte
  afterCode : List Byte
  beforeFlags : Word
  afterFlags : Word
  beforeRegisters : List Word
  afterRegisters : List Word
  address : Word
  beforeMemory : List Word
  afterMemory : List Word

def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def parseNumbers (line : String) : Except String (Array Nat) := do
  let values ← (line.splitOn "\t").mapM fun field =>
    match field.toNat? with
    | some value => if value < 2^64 then .ok value else .error "word-overflow"
    | none => .error "nondecimal-field"
  require (values.length == 58) "field-count"
  return values.toArray

def parseCapture (line : String) : Except String Capture := do
  let fields ← parseNumbers line
  let n := fun i => fields[i]!
  let w := fun i => BitVec.ofNat 64 (n i)
  require ((List.range 10).all fun i => n (7+i) < 256) "byte-overflow"
  return {
    id := n 0, source := n 1, base := n 2, ignoredX := n 3, vector := n 4
    beforePC := w 5, afterPC := w 6
    beforeCode := (List.range 5).map fun i => BitVec.ofNat 8 (n (7+i))
    afterCode := (List.range 5).map fun i => BitVec.ofNat 8 (n (12+i))
    beforeFlags := w 17, afterFlags := w 18
    beforeRegisters := (List.range 16).map fun i => w (19+i)
    afterRegisters := (List.range 16).map fun i => w (35+i)
    address := w 51
    beforeMemory := (List.range 3).map fun i => w (52+i)
    afterMemory := (List.range 3).map fun i => w (55+i) }

/-- Byte representation of the three captured qwords, not an ISA operation. -/
def memoryBytes (words : List Word) : List Byte :=
  words.flatMap fun word => (List.range 8).map fun i => word.extractLsb' (8*i) 8

def entry (capture : Capture) : State where
  registers r := capture.beforeRegisters.getD (allRegisters.idxOf r) 0
  rip := capture.beforePC
  flags := capture.beforeFlags
  memory := {
    read := fun a =>
      if capture.beforePC.toNat ≤ a.toNat ∧ a.toNat < capture.beforePC.toNat + 5
      then capture.beforeCode[a.toNat - capture.beforePC.toNat]?
      else if capture.address.toNat - 8 ≤ a.toNat ∧ a.toNat < capture.address.toNat + 16
      then (memoryBytes capture.beforeMemory)[a.toNat - (capture.address.toNat - 8)]?
      else none
    executable := fun a => decide
      (capture.beforePC.toNat ≤ a.toNat ∧ a.toNat < capture.beforePC.toNat + 5)
    writable := fun a => decide
      (capture.address.toNat ≤ a.toNat ∧ a.toNat < capture.address.toNat + 8) }

/-- Replay and compare actual bytes, all GPRs, full RFLAGS, full qword/event,
all 24 captured data bytes, five code bytes and finite outside/permission frames.
Permissions describe the replay fixture, not observations of physical PTEs. -/
def validate (capture : Capture) : Except String Unit := do
  require (capture.source < 16 && directBases.contains capture.base &&
    capture.ignoredX < 2 && capture.vector < 8) "matrix-coordinate"
  require (capture.address.toNat ≥ 8 && capture.address.toNat + 16 < 2^47 &&
    capture.address.toNat % 8 == 0 && capture.beforePC.toNat + 5 < 2^47 &&
    (capture.address.toNat + 16 ≤ capture.beforePC.toNat ||
      capture.beforePC.toNat + 5 ≤ capture.address.toNat - 8)) "fixture-address-profile"
  let initial := entry capture
  let instruction ← match LockedAdd64.decodeAt initial with
    | .ok instruction => .ok instruction
    | .error fault => .error s!"decode: {repr fault}"
  require (instruction.bytes == capture.beforeCode &&
    instruction.source == allRegisters.getD capture.source .rax &&
    instruction.base == allRegisters.getD capture.base .rax &&
    (instruction.rex.toNat / 2) % 2 == capture.ignoredX) "captured-encoding"
  let observation ← match LockedAdd64.step initial with
    | .ok observation => .ok observation
    | .error fault => .error s!"step: {repr fault}"
  let final := observation.state
  require (allRegisters.map final.registers == capture.afterRegisters) "complete-GPRs"
  require (final.flags == capture.afterFlags) "complete-RFLAGS"
  require ((capture.afterFlags &&& ~~~arithmeticFlagMask) ==
    (capture.beforeFlags &&& ~~~arithmeticFlagMask)) "outside-defined-flags-frame"
  require (final.rip == capture.afterPC) "observed-continuation"
  require (observation.event.delta == capture.beforeRegisters.getD capture.source 0 &&
    observation.event.event.address == capture.address &&
    observation.event.event.before == capture.beforeMemory.getD 1 0 &&
    observation.event.event.after == capture.afterMemory.getD 1 0) "complete-qword-event"
  let readback ← match loadQWord final.memory capture.address with
    | .ok word => .ok word
    | .error fault => .error s!"readback: {repr fault}"
  require (readback == capture.afterMemory.getD 1 0) "complete-qword-readback"
  require (observation.accesses == [.rmw8 capture.address]) "modeled-RMW-footprint"
  let dataQueries := (List.range 24).map fun i => capture.address - 8 + BitVec.ofNat 64 i
  require (dataQueries.map final.memory.read == (memoryBytes capture.afterMemory).map some)
    "complete-data-and-neighbor-frame"
  let codeQueries := (List.range 5).map fun i => capture.beforePC + BitVec.ofNat 64 i
  require (codeQueries.map final.memory.read == capture.afterCode.map some) "observed-code-frame"
  let outside := [capture.address - 9, capture.address + 16, capture.beforePC - 1,
    capture.beforePC + 5]
  require (outside.all fun a => final.memory.read a == initial.memory.read a) "outside-memory-frame"
  require ((dataQueries ++ codeQueries ++ outside).all fun a =>
    final.memory.executable a == initial.memory.executable a &&
    final.memory.writable a == initial.memory.writable a) "modeled-permission-frame"

def coverageIndex (capture : Capture) : Nat :=
  ((capture.source * 12 + directBases.idxOf capture.base) * 2 + capture.ignoredX) * 8 + capture.vector

end EDSL.Tests.LockedAdd64Native

#audit_edsl

namespace LockedAdd64NativeRuntime
open EDSL.Tests.LockedAdd64Native

def ioError (message : String) : IO α := throw (IO.userError message)

def replay (input negativeDirectory : System.FilePath) : IO Unit := do
  let text ← IO.FS.readFile input
  if text.utf8ByteSize > 4 * 1024 * 1024 then ioError "oversized capture input"
  let lines := text.splitOn "\n"
  if lines.head? != some "locked-add64-native-v1" then ioError "capture format/version"
  let mut seen := Array.replicate 3072 false
  let mut count := 0
  let mut first := ""
  for line in lines.drop 1 do
    if line.isEmpty then continue
    let capture ← match parseCapture line with
      | .error error => ioError s!"capture parse: {error}"
      | .ok capture => pure capture
    match validate capture with
    | .error error => ioError s!"capture {capture.id}: {error}"
    | .ok () => pure ()
    let index := coverageIndex capture
    if capture.id != count || index ≥ 3072 || seen[index]! then ioError "duplicate/order/coverage"
    seen := seen.set! index true
    if count == 0 then first := line
    count := count + 1
  if count != 3072 || !seen.all id then ioError s!"incomplete matrix: {count}/3072"
  IO.println s!"PASS actual LockedAdd64.step replay: {count} CPU captures; all GPRs/full RFLAGS/qword/code/data frames"

  -- Corrupt ACTUAL first capture, with exact Nat arithmetic (no floating point
  -- or assigned-value assertions). Each record is reparsed by the same parser
  -- and must fail the semantic comparison at the specifically expected gate.
  let original ← match parseNumbers first with
    | .ok fields => pure fields
    | .error error => ioError error
  IO.FS.createDirAll negativeDirectory
  let controls : List (String × Nat × Nat × String) := [
    ("qword-high", 56, 2^40, "complete-qword-event"),
    ("old-response-high", 35, 2^40, "complete-GPRs"),
    ("defined-flag", 18, 1, "complete-RFLAGS"),
    ("opcode", 10, 1, "decode: EDSL.X86.Error.unsupportedEncoding")]
  for (name, column, mask, expectedError) in controls do
    let changed := original.set! column (Nat.xor original[column]! mask)
    let line := String.intercalate "\t" (changed.toList.map toString)
    IO.FS.writeFile (negativeDirectory / s!"{name}.tsv") s!"locked-add64-native-v1\n{line}\n"
    let capture ← match parseCapture line with
      | .ok capture => pure capture
      | .error error => ioError s!"negative control parse failure: {name}: {error}"
    match validate capture with
    | .ok () => ioError s!"negative control admitted: {name}"
    | .error error =>
      if error != expectedError then ioError s!"wrong negative gate: {name}: {error}"
      IO.println s!"REJECT synthetic captured-record corruption: {name}: {error}"
  IO.println "PASS 4 semantic negative controls. Runtime conformance evidence only; no universal proof/physical TSO/Linux/source-order/corpus claim."

end LockedAdd64NativeRuntime

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [input, negatives] =>
    try
      LockedAdd64NativeRuntime.replay input negatives
      return 0
    catch error =>
      IO.eprintln s!"FAIL fixture/validation: {error}"
      return 1
  | _ =>
    IO.eprintln "usage: LockedAdd64Native.lean CAPTURES.tsv NEGATIVE_OUTPUT_DIRECTORY"
    return 2
