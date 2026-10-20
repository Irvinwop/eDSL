/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine

set_option autoImplicit false

namespace EDSL.Tests.SequentialByteOrderNative
open X86 X86.Sequential

/- Finite replay of actual CPU observations from the companion C fixture.
The CPU supplies results and flags; no model arithmetic formula supplies an
expected result. Stream metadata and requested INPUT coverage are authenticated
separately from semantic replay. Every supported record checks public step,
both AF choices, full flags, all sixteen GPRs, exact RIP and DATA1/no reads.

Native addresses are relocated, not serialized. Ordinary host operand RAM is
read-only and ends at a guard page. Instrumentation uses its own stack; this is
not a hardware observation of instruction-fetch permissions or of every memory
location. Model fetch/access/canonicality faults are checked independently.
The universal fullRAMFrame theorem below covers every read and permission map
entry of an admitted public step. Runtime frame samples additionally check the
concrete mapped support, boundaries and holes. High flag bits are synthetic
model frame challenges, not claimed observations of privileged CPU flags.

The 192 native AH records are deliberately outside the supported ISA subset:
they must produce unsupportedEncoding for BOTH AF choices, not a successful
comparison with SPL or a low-byte operation. Finite agreement is not a CPU/OS,
source, concurrency or address-space refinement theorem or a new certificate.
-/

/-- A public decoded new instruction with neither store intent preserves the
complete RAM value map and both permission maps at every 64-bit address. The
executable validator checks precisely these admission conditions per record. -/
theorem fullRAMFrame {initial final : State} {instruction : Sequential.Instruction}
    {af : Bool} {observation : Observation}
    (decoded : Sequential.decodeAt initial = .ok instruction)
    (newInstruction : instruction.isNew = true)
    (noStore : instruction.storeIntent initial = none)
    (noStore64 : instruction.storeIntent64 initial = none)
    (success : Sequential.step af initial = .ok observation)
    (next : observation.result = .next final) : final.memory = initial.memory := by
  rw [step_eq_execute af decoded] at success
  exact execute_new_memory newInstruction noStore noStore64 success next

/-- Universal pointwise consequence; permission preservation includes unmapped
holes and noncanonical addresses, not only the runtime query list. -/
theorem fullRAMAt {initial final : State} {instruction : Sequential.Instruction}
    {af : Bool} {observation : Observation}
    (decoded : Sequential.decodeAt initial = .ok instruction)
    (newInstruction : instruction.isNew = true)
    (noStore : instruction.storeIntent initial = none)
    (noStore64 : instruction.storeIntent64 initial = none)
    (success : Sequential.step af initial = .ok observation)
    (next : observation.result = .next final) (address : Word) :
    final.memory.read address = initial.memory.read address ∧
    final.memory.executable address = initial.memory.executable address ∧
    final.memory.writable address = initial.memory.writable address := by
  rw [fullRAMFrame decoded newInstruction noStore noStore64 success next]
  exact ⟨rfl, rfl, rfl⟩

private structure Probe where
  code : List Byte
  operation : Nat
  destination : Nat
  source : Nat
  base : Nat := 255
  index : Nat := 255
  deriving Inhabited

/- These independent literal/operand descriptors name the bytes inspected in
the linked native executable. They do not call the model encoder or decoder. -/
private def probes : Array Probe := #[
  ⟨[0x0f,0xb6,0x0c,0x07],1,1,255,7,0⟩,
  ⟨[0x0f,0xb6,0x04,0x0f],1,0,255,7,1⟩,
  ⟨[0x44,0x0f,0xb6,0x04,0x06],1,8,255,6,0⟩,
  ⟨[0x44,0x0f,0xb6,0x04,0x0e],1,8,255,6,1⟩,
  ⟨[0x45,0x0f,0xb6,0x0c,0x00],1,9,255,8,0⟩,
  ⟨[0x47,0x0f,0xb6,0x14,0x01],1,10,255,9,8⟩,
  ⟨[0x0f,0xb6,0x00],1,0,255,0,255⟩,
  ⟨[0x45,0x0f,0xb6,0x00],1,8,255,8,255⟩,
  ⟨[0x0f,0xb6,0xc1],2,0,1,255,255⟩,
  ⟨[0x0f,0xb6,0xc0],2,0,0,255,255⟩,
  ⟨[0x44,0x0f,0xb6,0xc1],2,8,1,255,255⟩,
  ⟨[0x41,0x0f,0xb6,0xc1],2,0,9,255,255⟩,
  ⟨[0x45,0x0f,0xb6,0xc1],2,8,9,255,255⟩,
  ⟨[0x45,0x0f,0xb6,0xc0],2,8,8,255,255⟩,
  ⟨[0x45,0x0f,0xb6,0xe5],2,12,13,255,255⟩,
  ⟨[0x40,0x0f,0xb6,0xc6],2,0,6,255,255⟩,
  ⟨[0x44,0x38,0xc1],3,1,8,255,255⟩,
  ⟨[0x44,0x38,0xc0],3,0,8,255,255⟩,
  ⟨[0x41,0x38,0xc1],3,9,0,255,255⟩,
  ⟨[0x45,0x38,0xca],3,10,9,255,255⟩,
  ⟨[0x45,0x38,0xc0],3,8,8,255,255⟩,
  ⟨[0x40,0x38,0xee],3,6,5,255,255⟩,
  ⟨[0x45,0x3a,0xca],3,9,10,255,255⟩,
  ⟨[0x44,0x29,0xc0],4,0,8,255,255⟩,
  ⟨[0x41,0x29,0xc1],4,9,0,255,255⟩,
  ⟨[0x45,0x29,0xca],4,10,9,255,255⟩,
  ⟨[0x45,0x29,0xc0],4,8,8,255,255⟩,
  ⟨[0x29,0xc0],4,0,0,255,255⟩,
  ⟨[0x45,0x2b,0xca],4,9,10,255,255⟩,
  ⟨[0x29,0xc8],4,0,1,255,255⟩,
  ⟨[0x41,0x29,0xc8],4,8,1,255,255⟩,
  ⟨[0x44,0x29,0xc8],4,0,9,255,255⟩,
  ⟨[0x0f,0xb6,0xc4],5,0,0,255,255⟩,
  ⟨[0x38,0xe0],6,0,0,255,255⟩,
  ⟨[0x38,0xc4],7,0,0,255,255⟩]

private def registers : Array Register :=
  #[.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

private def registerAt (index : Nat) : Register := (registers[index]?).getD .rax

private def poison : Array Nat := #[
  0x123456789abcde40,0x23456789abcdef51,0x3456789abcdef062,0x456789abcdef0173,
  0x56789abcdef01284,0x6789abcdef012395,0x789abcdef01234a6,0x89abcdef012345b7,
  0x9abcdef0123456c8,0xabcdef01234567d9,0xbcdef012345678ea,0xcdef0123456789fb,
  0xdef0123456789a0c,0xef0123456789ab1d,0xf0123456789abc2e,0x0123456789abcd3f]

private def byteCorners : Array Nat :=
  #[0,1,2,3,0xf,0x10,0x55,0x7e,0x7f,0x80,0x81,0xaa,0xf0,0xfe,0xff,0x40]

private def wordCorners : Array Nat :=
  #[0,1,0xf,0x10,0x7f,0x80,0xff,0x100,0xffff,0x10000,0x1000000,
    0x7fffffff,0x80000000,0x80000001,0xfffffffe,0xffffffff]

private def patterns : Array Nat := #[0,0x8d5,0x891,0x44]
private def codeBase : Word := 0x400000001000
private def dataBase : Word := 0x300000024
private def logicalBase : Word := 0x200000021
private def logicalIndex : Word := 0x100000003
private def sentinelA : Word := 0x1000000001000
private def sentinelB : Word := 0x7fffffffeff0
private def recordSize : Nat := 72
private def total : Nat := 15648
private def streamSize : Nat := 48 + total * recordSize

private def little (stream : ByteArray) (offset width : Nat) : Nat :=
  (List.range width).foldl
    (fun value i => value + stream[offset + i]!.toNat * 2 ^ (8 * i)) 0

private def checkHeader (stream : ByteArray) : Except String Unit := do
  if stream.size != streamSize then throw "invalid stream length (truncated/trailing bytes)"
  if (stream.extract 0 8).toList != [83,66,79,78,65,84,49,10] then throw "invalid stream magic"
  for (offset, expected) in
      [(8,1),(12,total),(16,35),(20,recordSize),(24,8192),(28,512),
       (32,3104),(36,3648),(40,192),(44,0)] do
    if little stream offset 4 != expected then throw s!"invalid schema/count at header offset {offset}"

private def checkRecordShape (stream : ByteArray) (offset id : Nat) (p : Probe)
    (li ri variant : Nat) : Except String Unit := do
  if offset + recordSize > stream.size then throw "truncated record"
  let sourceWidth := if p.operation = 4 then 4 else 1
  let destinationWidth := if p.operation = 3 ∨ p.operation ≥ 6 then 1 else 4
  for (field, width, expected) in
      [(0,2,id),(2,1,p.operation),(3,1,p.source),(4,1,p.destination),
       (5,1,sourceWidth),(6,1,destinationWidth),(7,1,p.code.length),
       (8,2,li),(10,2,ri),(12,1,variant),(13,1,15),(14,2,0),(71,1,0)] do
    if little stream (offset + field) width != expected then
      throw s!"invalid operation/operand/width/order/frame at record {id}, field {field}"
  for i in [0:5] do
    let expected := if i < p.code.length then p.code[i]!.toNat else 0
    if little stream (offset + 16 + i) 1 != expected then throw "linked instruction/padding mismatch"

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (value : Except String Unit) : IO Unit :=
  match value with
  | .error message => throw (IO.userError message)
  | .ok _ => pure ()

private def memory (bytes : List Byte) (rip : Word) (operand : Option (Word × Byte)) : Memory where
  read := fun address =>
    let offset := (address - rip).toNat
    if offset < bytes.length then bytes[offset]?
    else if address = sentinelA then some 0xa7
    else if address = sentinelB then some 0x69
    else match operand with
      | some (base,value) => if address = base then some value else none
      | none => none
  executable := fun address => decide ((address - rip).toNat < bytes.length)
  writable := fun _ => false

private def dirty (value variant : Nat) (source : Bool) : Word :=
  let high : Word := if variant % 2 = 0 then 0xa5c3d2e100000000 else 0x19b7f06d00000000
  (if source then high ^^^ 0x5aa5ff0000000000 else high) ||| BitVec.ofNat 64 value

private def entry (p : Probe) (li ri variant : Nat) (flags : Word) : State := Id.run do
  let mut values := poison.map (BitVec.ofNat 64)
  if p.operation = 1 then
    if p.index != 255 then values := values.set! p.index logicalIndex
    values := values.set! p.base (if p.index = 255 then dataBase else logicalBase)
  else if p.operation ≥ 5 then
    values := values.set! 0 (dirty (byteCorners[li]! + 256 * byteCorners[(li + 5) % 16]!) variant false)
  else
    let corners := if p.operation = 4 then wordCorners else byteCorners
    values := values.set! p.destination (dirty corners[li]! variant false)
    if p.source != p.destination then
      values := values.set! p.source (dirty corners[if p.operation = 2 then li else ri]! variant true)
  return {
    registers := fun register => values[(registers.toList.idxOf register)]!
    rip := codeBase
    flags := flags
    memory := memory p.code codeBase
      (if p.operation = 1 then some (dataBase,BitVec.ofNat 8 li) else none) }

private def highFlags (variant : Nat) : Word :=
  if variant % 2 = 0 then 0 else 0xfedcba9800000000

private def checkRAMSamples (initial final : State) (codeLength : Nat)
    (operand : Option Word) : IO Unit := do
  let mut queries := [0, initial.rip - 1, initial.rip + BitVec.ofNat 64 codeLength,
    sentinelA - 1, sentinelA, sentinelA + 1, sentinelB - 1, sentinelB, sentinelB + 1,
    0x800000000000,0xffff7fffffffffff,0xffffffffffffffff]
  for i in [0:codeLength] do queries := (initial.rip + BitVec.ofNat 64 i) :: queries
  for register in registers do queries := initial.registers register :: queries
  if let some address := operand then queries := (address - 1) :: address :: (address + 1) :: queries
  for address in queries do
    require (final.memory.read address == initial.memory.read address &&
      final.memory.executable address == initial.memory.executable address &&
      final.memory.writable address == initial.memory.writable address) "RAM/permission frame differs"

private def checkStep (initial : State) (p : Probe) (afterFlags destinationAfter : Word)
    (operand : Option Word) : IO Unit := do
  let instruction ← match Sequential.decodeAt initial with
    | .error fault => throw (IO.userError s!"public decode rejected CPU bytes: {repr fault}")
    | .ok instruction => pure instruction
  require (instruction.length == p.code.length) "decoded length differs from linked bytes"
  -- These are exactly the hypotheses of fullRAMFrame, for this public step.
  require (instruction.isNew && instruction.storeIntent initial == none &&
    instruction.storeIntent64 initial == none) "public instruction failed fullRAMFrame admission"
  let reads : List Read := match operand with
    | some address => [⟨.data,address,1⟩]
    | none => []
  for af in [false,true] do
    match Sequential.step af initial with
    | .error fault => throw (IO.userError s!"public step rejected CPU bytes: {repr fault}")
    | .ok observation =>
      require (observation.reads == reads) s!"incorrect operand footprint: {repr observation.reads}"
      match observation.result with
      | .next final =>
        require (final.rip == initial.rip + BitVec.ofNat 64 p.code.length) "next RIP differs"
        require (final.flags == afterFlags) "full CPU/model flags differ"
        for i in [0:registers.size] do
          let register := registerAt i
          let expected := if i = p.destination then destinationAfter else initial.registers register
          require (final.registers register == expected) s!"CPU/model result or GPR frame differs: {repr register}"
        checkRAMSamples initial final p.code.length operand
      | _ => throw (IO.userError "nonbranch native instruction did not continue")

private def expectFault (initial : State) (expected : Error) : IO Unit := do
  for af in [false,true] do
    match Sequential.step af initial with
    | .error actual => require (actual == expected) s!"incorrect model fault: {repr actual}; expected {repr expected}"
    | .ok _ => throw (IO.userError s!"accepted faulting model input: {repr expected}")

private def checkBoundaries (initial : State) (p : Probe)
    (afterFlags destinationAfter : Word) : IO Unit := do
  for i in [0:p.code.length] do
    let address := initial.rip + BitVec.ofNat 64 i
    expectFault { initial with memory := { initial.memory with
      read := fun query => if query = address then none else initial.memory.read query } }
      (.inaccessibleInstruction address)
    expectFault { initial with memory := { initial.memory with
      executable := fun query => if query = address then false else initial.memory.executable query } }
      (.inaccessibleInstruction address)
  -- The last instruction byte crosses out of the low canonical region.
  let cross : Word := 0x800000000000 - BitVec.ofNat 64 (p.code.length - 1)
  let crossingMemory := memory p.code cross
    (if p.operation = 1 then some (dataBase,(initial.memory.read dataBase).getD 0) else none)
  expectFault { initial with rip := cross, memory := crossingMemory }
    (.inaccessibleInstruction 0x800000000000)
  if p.operation = 1 then
    expectFault { initial with memory := { initial.memory with
      read := fun query => if query = dataBase then none else initial.memory.read query } }
      (.inaccessibleData dataBase)
    let value := (initial.memory.read dataBase).getD 0
    -- Single-byte access is valid even where a widened DATA4 would cross the
    -- canonical hole or wrap. These model addresses are synthetic.
    for address in ([0x7fffffffffff,0xffff800000000000,0xffffffffffffffff] : List Word) do
      let relocated := { initial with
        registers := fun register => if register = registerAt p.base then
          address - (if p.index = 255 then 0 else logicalIndex) else initial.registers register
        memory := memory p.code initial.rip (some (address,value)) }
      checkStep relocated p afterFlags destinationAfter (some address)
    for address in ([0x800000000000,0xffff7fffffffffff] : List Word) do
      let relocated := { initial with
        registers := fun register => if register = registerAt p.base then
          address - (if p.index = 255 then 0 else logicalIndex) else initial.registers register
        memory := memory p.code initial.rip (some (address,value)) }
      expectFault relocated (.inaccessibleData address)

private def checkRecord (stream : ByteArray) (record id : Nat) (p : Probe)
    (li ri variant : Nat) (boundaries : Bool) : IO Unit := do
  let offset := 48 + record * recordSize
  checked (checkRecordShape stream offset id p li ri variant)
  let before := BitVec.ofNat 64 (little stream (offset + 21) 8)
  let after := BitVec.ofNat 64 (little stream (offset + 29) 8)
  let destinationBefore := BitVec.ofNat 64 (little stream (offset + 37) 8)
  let sourceBefore := BitVec.ofNat 64 (little stream (offset + 45) 8)
  let destinationAfter := BitVec.ofNat 64 (little stream (offset + 53) 8)
  let sourceAfter := BitVec.ofNat 64 (little stream (offset + 61) 8)
  let pattern := patterns[(li + 3 * ri + variant) % 4]!
  require ((before &&& 0xcd5).toNat == 0x400 + pattern) "incoming CPU flags/DF coverage differs"
  require (((before ^^^ after) &&& ~~~(0x8d5 : Word)) == 0) "CPU nonarithmetic flags frame differs"
  if p.operation = 1 ∨ p.operation = 2 ∨ p.operation = 5 then
    require (before == after) "CPU MOVZX flags frame differs"
  let high := highFlags variant
  let initial := entry p li ri variant (before ||| high)
  require (destinationBefore == initial.registers (registerAt p.destination)) "CPU destination prestate/coverage differs"
  let expectedSource := if p.operation = 1 then BitVec.ofNat 64 li
    else initial.registers (registerAt p.source)
  require (sourceBefore == expectedSource) "CPU source prestate/coverage differs"
  -- Frames are observations of ALL actual CPU GPRs; no pointer is serialized.
  let mask := little stream (offset + 69) 2
  for i in [0:16] do
    let preserved := mask / 2 ^ i % 2 == 1
    if p.operation = 3 ∨ p.operation ≥ 6 ∨ i != p.destination then
      require preserved "CPU full GPR frame differs"
    else require (preserved == (destinationBefore == destinationAfter)) "CPU destination frame mask inconsistent"
  let expectedSourceAfter := if p.operation = 1 then sourceBefore
    else if p.source = p.destination then destinationAfter else sourceBefore
  require (sourceAfter == expectedSourceAfter) "CPU source frame/alias result differs"
  if p.operation ≥ 5 then
    expectFault initial .unsupportedEncoding
  else
    if p.operation = 3 then require (destinationAfter == destinationBefore) "CPU CMP destination changed"
    checkStep initial p (after ||| high) destinationAfter (if p.operation = 1 then some dataBase else none)
    if boundaries then checkBoundaries initial p (after ||| high) destinationAfter

private def requireRejection (result : Except String Unit) (description : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"accepted malformed capture: {description}")

private def checkMalformed (stream : ByteArray) : IO Unit := do
  requireRejection (checkHeader (stream.extract 0 (stream.size - 1))) "truncation"
  requireRejection (checkHeader (stream.push 0)) "trailing byte"
  for field in [0,8,12,16,20,24,28,32,36,40,44] do
    let mutated := stream.set! field (stream[field]! ^^^ 1)
    requireRejection (checkHeader mutated) s!"header field {field}"
  let p := probes[0]!
  for field in [0,2,3,4,5,6,7,8,10,12,13,14,16,71] do
    let mutated := stream.set! (48 + field) (stream[48 + field]! ^^^ 1)
    requireRejection (checkRecordShape mutated 48 0 p 0 0 0) s!"record field {field}"
  -- Padding belongs to the authenticated instruction field as well.
  let regOffset := 48 + 8192 * recordSize
  requireRejection (checkRecordShape (stream.set! (regOffset + 20) 1)
    regOffset 8 probes[8]! 0 0 0) "nonzero instruction padding"

private def checkObservationNegatives (stream : ByteArray) : IO Unit := do
  -- Mutate actual CPU observations, then run the same public-step validator.
  -- Arithmetic flag and result mutants pass schema/frame checks and must be
  -- rejected by CPU/model comparison, not by a copied arithmetic formula.
  for (record,id,field) in
      [(0,0,53),(0,0,57),(0,0,69),(0,0,37),(0,0,45),
       (8192 + 512,16,29),(8192 + 512 + 3104,23,53),
       (8192 + 512 + 3104,23,57)] do
    let offset := 48 + record * recordSize + field
    let mutated := stream.set! offset (stream[offset]! ^^^ 1)
    let accepted ← try
      checkRecord mutated record id probes[id]! 0 0 0 false
      pure true
    catch _ => pure false
    require (!accepted) s!"accepted corrupted native observation: probe {id}, field {field}"

private def checkHighByteSubset : IO Unit := do
  -- Independent encoding contracts for AH, CH, DH and BH on both operand
  -- sides. Actual AH CPU records above also distinguish this exclusion from
  -- a claim that these encodings are invalid x86 instructions.
  for low in [0:4] do
    let highRM := BitVec.ofNat 8 (0xc4 + low)
    let highReg := BitVec.ofNat 8 (0xe0 + 8 * low)
    for bytes in [[0x0f,0xb6,highRM],[0x38,highRM],[0x38,highReg],
        [0x3a,highRM],[0x3a,highReg]] do
      let initial : State := {
        registers := fun _ => 0x123456789abc807f
        flags := 0x602
        rip := codeBase
        memory := memory bytes codeBase none }
      expectFault initial .unsupportedEncoding

def checkNative (stream : ByteArray) : IO Unit := do
  checked (checkHeader stream)
  checkMalformed stream
  checkObservationNegatives stream
  checkHighByteSubset
  let mut record := 0
  for id in [0:probes.size] do
    let p := probes[id]!
    let leftCount := if p.operation = 1 then 256 else 16
    let rightCount := if (p.operation = 3 ∨ p.operation = 4) ∧ p.destination != p.source then 16 else 1
    let variants := if p.operation = 3 ∨ p.operation = 4 then 2 else 4
    for li in [0:leftCount] do
      for ri in [0:rightCount] do
        for variant in [0:variants] do
          try
            checkRecord stream record id p li ri variant (li == 0 && ri == 0 && variant == 0)
          catch error => throw (IO.userError s!"record {record}, probe {id}, input {li}/{ri}/{variant}: {error}")
          record := record + 1
    IO.println s!"probe {id}: native records accepted; both AF choices checked"
  require (record == total) "incomplete record coverage"
  IO.println "15456 native supported records matched public step; 192 native AH records rejected by subset"
  IO.println "28 malformed-capture controls, 8 corrupted CPU observations, and 20 AH/CH/DH/BH encoding exclusions rejected"
  IO.println "Full flags/GPR/RIP, universal RAM frame admission, DATA1/no-read and boundary/schema/observation negatives passed"
  IO.println "Finite native evidence only; no new certificate, score, CPU/OS/source/concurrency refinement claim"

end EDSL.Tests.SequentialByteOrderNative

#print axioms EDSL.Tests.SequentialByteOrderNative.fullRAMFrame
#print axioms EDSL.Tests.SequentialByteOrderNative.fullRAMAt

def main (args : List String) : IO Unit := do
  let path ← match args with
    | [path] => pure path
    | _ => throw (IO.userError "usage: SequentialByteOrderNative.lean CAPTURE.bin")
  EDSL.Tests.SequentialByteOrderNative.checkNative (← IO.FS.readBinFile path)
