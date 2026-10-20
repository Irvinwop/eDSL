/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine

set_option autoImplicit false

namespace EDSL.Tests.SequentialSearchNative
open X86 X86.Sequential

/- Finite Linux x86-64 conformance against the actual linked bytes captured by
fixtures/sequential-search-native.c. This is an executable validator, not a
proof oracle or a universal hardware correspondence theorem. It consumes only
the v1 stream specified in that fixture; no model flag formula supplies expected
status bits. The native process checks RO/guard boundaries and address/source
GPR preservation, with DF restored before C resumes.

The logical address registers below deliberately differ from host pointers.
They encode the same base/index/source operands with full-width values above
4 GiB and unaligned effective addresses. RIP is also above 4 GiB. Only the
instruction bytes and the precise DATA1/DATA4 footprint are accessible, plus
two frame sentinels. Success therefore checks exact fetch extent and catches
truncated addresses or excessive operand reads. We check every GPR, the complete
flags word (including synthetic high bits), and RAM/permissions on the mapped
support, its boundaries and selected holes. These finite RAM observations do
not replace the model's independently proved universal memory frame lemmas.
-/

private def cmp8Count : Nat := 2 * 256 * 256
private def cmp32Count : Nat := 2 * 2 * 16 * 16
private def movCount : Nat := 2 * 7 * 4
private def recordSize : Nat := 31
private def streamSize : Nat := 32 + recordSize * (cmp8Count + cmp32Count + movCount)

private def little (stream : ByteArray) (offset width : Nat) : Nat :=
  (List.range width).foldl
    (fun value i => value + stream[offset + i]!.toNat * 2 ^ (8 * i)) 0

private def codeAt (stream : ByteArray) (offset length : Nat) : List Byte :=
  (stream.extract offset (offset + length)).toList.map (fun byte => BitVec.ofNat 8 byte.toNat)

private def checkHeader (stream : ByteArray) : Except String Unit := do
  if stream.size != streamSize then throw "invalid native stream length"
  if (stream.extract 0 8).toList != [83,83,78,65,84,48,49,10] then
    throw "invalid native stream magic"
  for (offset, expected) in
      [(8,1), (12,cmp8Count), (16,cmp32Count), (20,movCount), (24,recordSize), (28,0)] do
    if little stream offset 4 != expected then
      throw s!"invalid native schema/count at header offset {offset}"

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def expectHeaderRejection (stream : ByteArray) (description : String) : IO Unit :=
  match checkHeader stream with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"accepted {description}")

private def registers : List Register :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

private def poison (register : Register) : Word :=
  match register with
  | .rax => 0x123456789abcdef0 | .rcx => 0x23456789abcdef01
  | .rdx => 0x3456789abcdef012 | .rbx => 0x456789abcdef0123
  | .rsp => 0x56789abcdef01234 | .rbp => 0x6789abcdef012345
  | .rsi => 0x789abcdef0123456 | .rdi => 0x89abcdef01234567
  | .r8 => 0x123456789abcdef0 | .r9 => 0xabcdef0123456789
  | .r10 => 0xbcdef0123456789a | .r11 => 0xcdef0123456789ab
  | .r12 => 0xdef0123456789abc | .r13 => 0xef0123456789abcd
  | .r14 => 0xf0123456789abcde | .r15 => 0x0123456789abcdef

private def codeBase : Word := 0x400000001000
private def sentinelA : Word := 0x1000000001000
private def sentinelB : Word := 0x7fffffffeff0

private def baseValue (variant : Nat) : Word :=
  if variant = 0 then 0x100000021 else 0x700000007

private def indexValue (variant : Nat) : Word :=
  if variant = 0 then 0x200000003 else 0x100000005

/- Independent, explicit expected sums: no Address.eval or decoder supplies
these addresses. CMP8 uses scale one; the encoded CMP32 SIB scale is four. -/
private def dataAddress (width variant : Nat) : Word :=
  if width = 1 then
    if variant = 0 then 0x300000024 else 0x80000000c
  else
    if variant = 0 then 0x90000002d else 0xb0000001b

private def memory (bytes : List Byte) (operand : Option (Word × Nat × Nat)) : Memory where
  read := fun address =>
    if codeBase.toNat ≤ address.toNat ∧ address.toNat < codeBase.toNat + bytes.length then
      bytes[address.toNat - codeBase.toNat]?
    else if address = sentinelA then some 0xa7
    else if address = sentinelB then some 0x69
    else match operand with
      | some (base, width, value) =>
        if base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + width then
          some (BitVec.ofNat 8 (value / 2 ^ (8 * (address.toNat - base.toNat))))
        else none
      | none => none
  executable := fun address =>
    decide (codeBase.toNat ≤ address.toNat ∧ address.toNat < codeBase.toNat + bytes.length)
  writable := fun _ => false

private def highFlags (variant : Nat) : Word :=
  if variant % 2 = 0 then 0 else 0xfffffffffffff000

private def compareEntry (bytes : List Byte) (encoding width variant left source : Nat)
    (flags : Word) : State where
  registers := fun register =>
    if register = .rdi then baseValue variant
    else if register = (if encoding = 0 then .rax else .rcx) then indexValue variant
    else if register = .rdx then BitVec.ofNat 64 source
    else poison register
  rip := codeBase
  flags := flags
  memory := memory bytes (some (dataAddress width variant, width, left))

private def moveEntry (bytes : List Byte) (flags : Word) : State where
  registers := poison
  rip := codeBase
  flags := flags
  memory := memory bytes none

private def checkMemoryFrame (initial final : State) (codeLength : Nat)
    (operand : Option (Word × Nat)) : IO Unit := do
  let mut queries := [0, codeBase - 1, codeBase + BitVec.ofNat 64 codeLength,
    sentinelA - 1, sentinelA, sentinelA + 1, sentinelB - 1, sentinelB, sentinelB + 1,
    0xffffffffffffffff]
  for offset in [0:codeLength] do
    queries := (codeBase + BitVec.ofNat 64 offset) :: queries
  for register in registers do
    queries := initial.registers register :: queries
  if let some (address, width) := operand then
    queries := (address - 1) :: (address + BitVec.ofNat 64 width) :: queries
    for offset in [0:width] do
      queries := (address + BitVec.ofNat 64 offset) :: queries
  for query in queries do
    require (final.memory.read query == initial.memory.read query &&
      final.memory.executable query == initial.memory.executable query &&
      final.memory.writable query == initial.memory.writable query)
      s!"RAM/permission frame differs at {query.toNat}"

private def checkObservation (initial : State) (codeLength : Nat) (flags : Word)
    (reads : List Read) (write : Option (Register × Word)) (af : Bool) : IO Unit := do
  match Sequential.step af initial with
  | .error fault => throw (IO.userError s!"public step rejected native encoding: {repr fault}")
  | .ok observation =>
    require (observation.reads == reads) s!"incorrect DATA footprint: {repr observation.reads}"
    match observation.result with
    | .next final =>
      require (final.rip == codeBase + BitVec.ofNat 64 codeLength) "incorrect next RIP/length"
      require (final.flags == flags) s!"CPU/model full flags differ: {final.flags.toNat} != {flags.toNat}"
      for register in registers do
        let expected := match write with
          | some (destination, value) => if register = destination then value else initial.registers register
          | none => initial.registers register
        require (final.registers register == expected) s!"register frame/result differs: {repr register}"
      let operand := match reads with
        | [read] => some (read.address, read.bytes)
        | _ => none
      checkMemoryFrame initial final codeLength operand
    | _ => throw (IO.userError "native nonbranch instruction did not continue")

private def expectFault (state : State) (expected : Error) : IO Unit := do
  match Sequential.step false state with
  | .error actual =>
    require (actual == expected) s!"incorrect fault: {repr actual}, expected {repr expected}"
  | .ok _ => throw (IO.userError s!"accepted missing/nonexecutable byte: {repr expected}")

/- These negatives remove each required byte from a successfully validated
actual encoding. They check fetch and read primitives rather than mocking the
CPU. Exact-length positive states already leave every trailing byte absent. -/
private def checkBoundaries (initial : State) (codeLength : Nat)
    (operand : Option (Word × Nat)) : IO Unit := do
  for offset in [0:codeLength] do
    let address := codeBase + BitVec.ofNat 64 offset
    expectFault { initial with memory := { initial.memory with
      read := fun query => if query = address then none else initial.memory.read query } }
      (.inaccessibleInstruction address)
    expectFault { initial with memory := { initial.memory with
      executable := fun query => if query = address then false else initial.memory.executable query } }
      (.inaccessibleInstruction address)
  if let some (base, width) := operand then
    for offset in [0:width] do
      let address := base + BitVec.ofNat 64 offset
      expectFault { initial with memory := { initial.memory with
        read := fun query => if query = address then none else initial.memory.read query } }
        (.inaccessibleData address)

private def patterns : Array Nat := #[0,0x8d5,0x891,0x44]
private def corners32 : Array Nat :=
  #[0,1,0xf,0x10,0x7f,0x80,0xff,0x100,0xffff,0x10000,0x1000000,
    0x7fffffff,0x80000000,0x80000001,0xfffffffe,0xffffffff]

/- Explicit semantic corner contracts distinguish sign-extension at bit 31
from zero-extension and from sign-extension at bits 7 or 15. -/
private def moveCases : Array (Nat × Nat) :=
  #[(0,0), (1,1), (0x80,0x80), (0xffff,0xffff), (0x7fffffff,0x7fffffff),
    (0x80000000,0xffffffff80000000), (0xffffffff,0xffffffffffffffff)]

private def checkIncoming (before : Word) (pattern : Nat) : IO Unit :=
  require ((before &&& 0xcd5).toNat == 0x400 + patterns[pattern % 4]!)
    "native capture did not exercise the requested incoming status flags and set DF"

private def checkCompare (stream : ByteArray) (record encoding width variant left source pattern : Nat)
    (boundaries : Bool) : IO Unit := do
  let offset := 32 + record * recordSize
  let bytes := codeAt stream offset 3
  let sib : Byte := if width = 1 then (if encoding = 0 then 0x07 else 0x0f)
    else (if encoding = 0 then 0x87 else 0x8f)
  require (bytes == [if width = 1 then 0x38 else 0x39, 0x14, sib])
    "native CMP encoding/order differs"
  let before := BitVec.ofNat 64 (little stream (offset + 3) 8)
  let after := BitVec.ofNat 64 (little stream (offset + 11) 8)
  checkIncoming before pattern
  require (((before ^^^ after) &&& ~~~(0x8d5 : Word)) == 0)
    "native CMP changed nonarithmetic flags"
  require (little stream (offset + 19) 8 == source) "native CMP source GPR changed/coverage differs"
  require (little stream (offset + 27) 4 == left) "native CMP memory frame/coverage differs"
  let high := highFlags (record + variant)
  let initial := compareEntry bytes encoding width variant left source (before ||| high)
  let address := dataAddress width variant
  for af in [false,true] do
    checkObservation initial 3 (after ||| high) [⟨.data,address,width⟩] none af
  if boundaries then checkBoundaries initial 3 (some (address,width))

def checkNative (stream : ByteArray) : IO Unit := do
  match checkHeader stream with
  | .error message => throw (IO.userError message)
  | .ok _ => pure ()
  -- These are actual capture mutations; a parser must reject partial/extra
  -- records and incorrect count/record schemas before attempting replay.
  expectHeaderRejection (stream.extract 0 (stream.size - 1)) "truncated record"
  expectHeaderRejection (stream.push 0) "trailing record byte"
  expectHeaderRejection (stream.set! 12 1) "incorrect CMP8 count"
  expectHeaderRejection (stream.set! 16 1) "incorrect CMP32 count"
  expectHeaderRejection (stream.set! 20 0) "incorrect MOV count"
  expectHeaderRejection (stream.set! 24 30) "incorrect record size"
  expectHeaderRejection (stream.set! 8 2) "unknown schema version"
  expectHeaderRejection (stream.set! 0 0) "incorrect magic"
  expectHeaderRejection (stream.set! 28 1) "nonzero reserved field"
  let mut record := 0
  for encoding in [0:2] do
    for left in [0:256] do
      for right in [0:256] do
        let source := 0xa5c3d2e1b7f90000 + right
        checkCompare stream record encoding 1 encoding left source (left + right)
          (left == 0 && right == 0)
        record := record + 1
    IO.println s!"CMP8 encoding {encoding}: all 65536 native pairs matched public step, both AF choices"
  for encoding in [0:2] do
    for variant in [0:2] do
      for li in [0:corners32.size] do
        for ri in [0:corners32.size] do
          let left := corners32[li]!
          let right := corners32[ri]!
          let source := (if variant = 0 then 0xa5c3d2e100000000 else 0) + right
          checkCompare stream record encoding 4 variant left source (li + ri + variant)
            (li == 0 && ri == 0)
          record := record + 1
  IO.println "CMP32: 1024 native corner pairs matched public step, DATA4, SIB*4, full address/source widths"
  for destination in [0:2] do
    for immediate in [0:moveCases.size] do
      for pattern in [0:4] do
        let offset := 32 + record * recordSize
        let bytes := codeAt stream offset 7
        let (value, expected) := moveCases[immediate]!
        let suffix := (List.range 4).map (fun i => BitVec.ofNat 8 (value / 2 ^ (8 * i)))
        require (bytes == [if destination = 0 then 0x48 else 0x49,0xc7,0xc0] ++ suffix)
          "native MOV encoding/order differs"
        let before := BitVec.ofNat 64 (little stream (offset + 7) 8)
        let after := BitVec.ofNat 64 (little stream (offset + 15) 8)
        let observed := BitVec.ofNat 64 (little stream (offset + 23) 8)
        checkIncoming before pattern
        require (before == after) "native C7 changed flags"
        require (observed.toNat == expected) "native C7 violated the full64 sign-extension corner contract"
        let high := highFlags (pattern + immediate)
        let initial := moveEntry bytes (before ||| high)
        let register := if destination = 0 then Register.rax else Register.r8
        for af in [false,true] do
          checkObservation initial 7 (after ||| high) [] (some (register,observed)) af
        if pattern = 0 then checkBoundaries initial 7 none
        record := record + 1
  require (record == cmp8Count + cmp32Count + movCount) "incomplete native record coverage"
  IO.println "C7: 56 native records matched full64 sign extension, no operand reads, all GPR/flags frames"
  IO.println "Finite native conformance only; schema, exact fetch boundaries and DATA1/DATA4 faults passed"

end EDSL.Tests.SequentialSearchNative

def main (args : List String) : IO Unit := do
  let path ← match args with
    | [path] => pure path
    | _ => throw (IO.userError "usage: SequentialSearchNative.lean CAPTURE.bin")
  EDSL.Tests.SequentialSearchNative.checkNative (← IO.FS.readBinFile path)
