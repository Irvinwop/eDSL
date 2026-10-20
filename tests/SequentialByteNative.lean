/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.SequentialByteComparison

set_option autoImplicit false

namespace EDSL.Tests.SequentialByteNative
open X86 X86.Sequential

private def entry (left : Nat) (bytes : List Byte) : State where
  registers := fun register => if register = .rbx then 8191
    else 0xfedcba9876543210
  rip := 4096
  flags := 0xffffffffffffffff
  memory := {
    read := fun address =>
      if address = 8191 then some (BitVec.ofNat 8 left)
      else if 4096 ≤ address.toNat ∧ address.toNat < 4099
      then bytes[address.toNat - 4096]?
      else none
    executable := fun address => decide (4096 ≤ address.toNat ∧ address.toNat < 4099)
    writable := fun _ => false }

def checkNative (flags : ByteArray) : IO Unit := do
  if flags.size != 256 * 256 * 5 then throw (IO.userError "invalid native flags stream size")
  for left in [0:256] do
    for right in [0:256] do
      let offset := (left * 256 + right) * 5
      let bytes := (flags.extract offset (offset + 3)).toList.map
        (fun byte => BitVec.ofNat 8 byte.toNat)
      if bytes != [0x80,0x3b,BitVec.ofNat 8 right] then
        throw (IO.userError s!"native immediate coverage/encoding differs for {left},{right}")
      let expected := flags[offset + 3]!.toNat + 256 * flags[offset + 4]!.toNat
      let initial := entry left bytes
      match Sequential.step false initial with
      | .error fault => throw (IO.userError s!"model fault for {left},{right}: {repr fault}")
      | .ok observation =>
        match observation.result with
        | .next final =>
          if (final.flags &&& arithmeticFlagMask).toNat != expected then
            throw (IO.userError s!"native flags differ for {left},{right}")
          if final.rip != 4099 || decide (observation.reads ≠ [⟨.data,8191,1⟩]) then
            throw (IO.userError s!"incorrect byte read footprint/length for {left},{right}")
        | _ => throw (IO.userError "byte compare did not continue")
  IO.println "Public Sequential.step matched all 65536 native flag vectors and DATA1 footprints"

def checkFrozen : IO Unit := do
  for (path, offset, expected) in
      [ ("corpus/v1/gcc/final.elf", 0x2f60, SequentialByteComparison.gcc35),
        ("corpus/v1/clang/final.elf", 0x14a0, SequentialByteComparison.clang34) ] do
    let file ← IO.FS.readBinFile path
    let bytes := (file.extract offset (offset + expected.length)).toList.map
      (fun byte => BitVec.ofNat 8 byte.toNat)
    if bytes != expected then throw (IO.userError s!"frozen file slice differs: {path}")
    match CFG.analyze bytes with
    | .error fault => throw (IO.userError s!"frozen window rejected: {repr fault}")
    | .ok graph => IO.println s!"{path}: actual {bytes.length}-byte slice discovered {graph.nodes.length} nodes"

end EDSL.Tests.SequentialByteNative

def main (args : List String) : IO Unit := do
  let path ← match args with
    | [path] => pure path
    | _ => throw (IO.userError "usage: SequentialByteNative.lean FLAGS.bin")
  EDSL.Tests.SequentialByteNative.checkNative (← IO.FS.readBinFile path)
  EDSL.Tests.SequentialByteNative.checkFrozen

#audit_edsl
