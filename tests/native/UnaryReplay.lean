/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Machine
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.UnaryReplay
open X86 X86.Sequential

/- The literal table is independent of production semantics. The C++ observer
does not read it. This module parses observations, checks that table and emits
kernel-checked finite production-step theorems; IO success alone is not a proof.
Only RAX/RCX/R8/R9 were observed on hardware. Other GPRs, permissions and high
flag challenges in clients are model frames, not extra physical observations.
PUSHFQ masks RF/VM; no physical/OS/source/concurrency refinement is asserted. -/

inductive Probe where
  | negEax | negEcx | negR8d | negR9d
  | swapRax | swapRcx | swapR8 | swapR9
  deriving BEq, DecidableEq, Repr, Inhabited

def Probe.all : List Probe :=
  [.negEax,.negEcx,.negR8d,.negR9d,.swapRax,.swapRcx,.swapR8,.swapR9]

def Probe.negative : Probe → Bool
  | .negEax | .negEcx | .negR8d | .negR9d => true
  | _ => false

def Probe.destination : Probe → Register
  | .negEax | .swapRax => .rax
  | .negEcx | .swapRcx => .rcx
  | .negR8d | .swapR8 => .r8
  | .negR9d | .swapR9 => .r9

/-- Literal descriptions of the linked fixture windows, not a model encoder. -/
def Probe.bytes : Probe → List Byte
  | .negEax => [0xf7,0xd8] | .negEcx => [0xf7,0xd9]
  | .negR8d => [0x41,0xf7,0xd8] | .negR9d => [0x41,0xf7,0xd9]
  | .swapRax => [0x48,0x0f,0xc8] | .swapRcx => [0x48,0x0f,0xc9]
  | .swapR8 => [0x49,0x0f,0xc8] | .swapR9 => [0x49,0x0f,0xc9]

def Probe.instruction : Probe → Sequential.Instruction
  | .negEax => .negReg32 .rax false | .negEcx => .negReg32 .rcx false
  | .negR8d => .negReg32 .r8 true | .negR9d => .negReg32 .r9 true
  | .swapRax => .bswapReg64 .rax | .swapRcx => .bswapReg64 .rcx
  | .swapR8 => .bswapReg64 .r8 | .swapR9 => .bswapReg64 .r9

def Probe.operation (p : Probe) : String := if p.negative then "neg32" else "bswap64"

def Probe.registerName : Probe → String
  | .negEax => "eax" | .negEcx => "ecx" | .negR8d => "r8d" | .negR9d => "r9d"
  | .swapRax => "rax" | .swapRcx => "rcx" | .swapR8 => "r8" | .swapR9 => "r9"

def Probe.sourceName : Probe → String
  | .negEax => "negEax" | .negEcx => "negEcx" | .negR8d => "negR8d" | .negR9d => "negR9d"
  | .swapRax => "swapRax" | .swapRcx => "swapRcx" | .swapR8 => "swapR8" | .swapR9 => "swapR9"

def allRegisters : List Register :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

def observedRegisters : List Register := [.rax,.rcx,.r8,.r9]

/-- Unobserved registers receive distinct synthetic full64 model challenges. -/
def modelCanary : Register → Word
  | .rax => 0x1122334455667788 | .rcx => 0x8877665544332211
  | .rdx => 0x8000000000000002 | .rbx => 0xffffffff00000003
  | .rsp => 0xffff800000001004 | .rbp => 0x0000800000000005
  | .rsi => 0x1234567800000006 | .rdi => 0x8765432100000007
  | .r8 => 0x0123456789abcdef | .r9 => 0xfedcba9876543210
  | .r10 => 0x80000000fffffff0 | .r11 => 0xffffffff00000011
  | .r12 => 0x0011223344556612 | .r13 => 0x7766554433221113
  | .r14 => 0x55555555aaaaaa14 | .r15 => 0xaaaaaaaa55555515

def observed (values : List Word) (r : Register) : Word :=
  match r with
  | .rax => (values[0]?).getD 0 | .rcx => (values[1]?).getD 0
  | .r8 => (values[2]?).getD 0 | .r9 => (values[3]?).getD 0
  | _ => modelCanary r

def codeBase : Word := 0x400000001000

/-- Code is read-only/executable. Two DATA sentinels exercise separate value,
write and execute maps; all remaining addresses are holes. -/
def replayMemory (bytes : List Byte) (base : Word := codeBase) : Memory where
  read := fun address =>
    if (address - base).toNat < bytes.length then bytes[(address - base).toNat]?
    else if address = 0x7fffffffffff then some 0xa7
    else if address = 0xffff800000000000 then some 0x69 else none
  executable := fun address => decide ((address - base).toNat < bytes.length)
  writable := fun address => address == 0xffff800000000000

structure Row where
  probe : Probe
  code : List Byte
  before : List Word
  after : List Word
  flagsBefore : Word
  flagsAfter : Word
  input : Word
  output : Word
  arithmeticFlags : Word
  seed : Nat
  deriving Inhabited

def Row.initial (row : Row) : State where
  registers := observed row.before
  rip := codeBase
  flags := row.flagsBefore
  memory := replayMemory row.code

def arithmeticMask : Word := 0x8d5

/-- ADD-established seed flags, independently supplied as fixed literals. -/
def seedFlags : List Word := [0x44,0x55,0x894,0x845,0x10,0x4,0,0x84]

def literalCheck (row : Row) : Bool :=
  row.before.length == 4 && row.after.length == 4 && row.seed < 8 &&
  observed row.before row.probe.destination == row.input &&
  observed row.after row.probe.destination == row.output &&
  observedRegisters.all (fun r => if r = row.probe.destination then true
    else observed row.before r == modelCanary r && observed row.after r == observed row.before r) &&
  row.flagsBefore &&& arithmeticMask == (seedFlags[row.seed]?).getD 0 &&
  row.flagsBefore &&& 0x40400 == 0 && row.flagsBefore &&& 2 == 2 &&
  row.flagsBefore &&& 0x30000 == 0 && row.flagsAfter &&& 0x30000 == 0 &&
  (if row.probe.negative then
    row.flagsAfter &&& arithmeticMask == row.arithmeticFlags &&
    (row.flagsBefore ^^^ row.flagsAfter) &&& ~~~arithmeticMask == 0
   else row.flagsAfter == row.flagsBefore)

def frameQueries (row : Row) : List Word :=
  [0,codeBase-1,codeBase,codeBase+1,codeBase+2,codeBase+3,
   codeBase + BitVec.ofNat 64 row.code.length,
   0x7ffffffffffe,0x7fffffffffff,0x800000000000,
   0xffff7fffffffffff,0xffff800000000000,0xffff800000000001,0xffffffffffffffff]

/-- A projection of the FULL production step, with both AF choices. No
execution, decoding, negation, byte swap or flag formula is reimplemented here. -/
def stepCheck (row : Row) : Bool :=
  [false,true].all fun af =>
    match Sequential.step af row.initial with
    | .error _ => false
    | .ok observation => match observation.result with
      | .next final =>
        final.rip == codeBase + BitVec.ofNat 64 row.code.length &&
        final.flags == row.flagsAfter && observation.reads == [] &&
        allRegisters.all (fun r => final.registers r == observed row.after r) &&
        (frameQueries row).all (fun a =>
          final.memory.read a == row.initial.memory.read a &&
          final.memory.executable a == row.initial.memory.executable a &&
          final.memory.writable a == row.initial.memory.writable a)
      | _ => false

def check (row : Row) : Bool :=
  literalCheck row && row.code == row.probe.bytes &&
  (match Sequential.decodeAt row.initial with
    | .ok instruction => decide (instruction = row.probe.instruction)
    | .error _ => false) &&
  row.probe.instruction.length == row.code.length &&
  row.probe.instruction.isNew && !row.probe.instruction.isLocked &&
  !row.probe.instruction.choosesAF &&
  row.probe.instruction.storeIntent row.initial == none &&
  row.probe.instruction.storeIntent64 row.initial == none && stepCheck row

/-- Universal whole-memory frame, beyond the finite query list. The checker
authenticates its decode/new/no-store hypotheses for every generated row. -/
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

theorem fullRAMAt {initial final : State} {instruction : Sequential.Instruction}
    {af : Bool} {observation : Observation}
    (decoded : Sequential.decodeAt initial = .ok instruction)
    (newInstruction : instruction.isNew = true)
    (noStore : instruction.storeIntent initial = none)
    (noStore64 : instruction.storeIntent64 initial = none)
    (success : Sequential.step af initial = .ok observation)
    (next : observation.result = .next final) (a : Word) :
    final.memory.read a = initial.memory.read a ∧
    final.memory.executable a = initial.memory.executable a ∧
    final.memory.writable a = initial.memory.writable a := by
  rw [fullRAMFrame decoded newInstruction noStore noStore64 success next]
  exact ⟨rfl,rfl,rfl⟩

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

private def fixedHex (n : Nat) : String :=
  let text := hex n
  String.ofList (List.replicate (16 - text.length) '0') ++ text

private def parseHex (width : Nat) (s : String) : IO Word := do
  require (s.length == width) s!"expected {width} hex digits: {s}"
  let mut value := 0
  for c in s.toList do
    let digit := if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
      else if 'a' ≤ c && c ≤ 'f' then 10 + c.toNat - 'a'.toNat else 16
    require (digit < 16) s!"invalid lower-case hexadecimal: {s}"
    value := 16 * value + digit
  return BitVec.ofNat 64 value

private structure Literal where
  negative : Bool
  name : String
  input : Word
  output : Word
  flags : Word
  deriving Inhabited

private def words (s : String) : Array String :=
  ((s.replace "\t" " ").splitOn " ").filter (· != "") |>.toArray

private def readLiterals (path : System.FilePath) : IO (Array Literal) := do
  let mut result := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let f := words line
    require (f.size == 5) "literal row must have five fields"
    let negative := f[0]! == "neg32"
    require (negative || f[0]! == "bswap64") "unknown literal operation"
    require (!result.any (fun l => l.negative == negative && l.name == f[1]!)) "duplicate literal"
    let flags ← if negative then parseHex 4 f[4]! else do
      require (f[4]! == "PRESERVE") "BSWAP literal must preserve flags"
      pure 0
    require (flags &&& ~~~arithmeticMask == 0) "literal arithmetic flags out of range"
    result := result.push ⟨negative,f[1]!,← parseHex 16 f[2]!,← parseHex 16 f[3]!,flags⟩
  require ((result.filter (·.negative)).size == 28 && result.size == 44) "incomplete literal dataset"
  return result

private def captureHeader : String :=
  "case_id\toperation\tregister\tseed\tinstruction_hex\trequested_input" ++
  "\tbefore_rax\tbefore_rcx\tbefore_r8\tbefore_r9\tafter_rax\tafter_rcx\tafter_r8\tafter_r9" ++
  "\trflags_before\trflags_after\tclassification"

private def codeHex (bytes : List Byte) : String :=
  String.join (bytes.map fun b => let s := hex b.toNat; if s.length = 1 then "0" ++ s else s)

private def checkOpcodeFiles (directory : System.FilePath) : IO Unit := do
  for p in Probe.all do
    let bytes ← IO.FS.readBinFile (directory / s!"{p.operation}-{p.registerName}.bin")
    require (bytes.toList.map (BitVec.ofNat 8 ∘ UInt8.toNat) == p.bytes) "live opcode file mismatch"

private def readRows (literals : Array Literal) (path : System.FilePath) : IO (Array Row) := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  require (lines.head? == some captureHeader) "capture header/schema mismatch"
  let mut rows := #[]
  let mut seen : Array (String × String × String × Nat) := #[]
  for line in lines.drop 1 do
    if line.isEmpty then continue
    let f := (line.splitOn "\t").toArray
    let context := s!"capture row {rows.size + 2}"
    require (f.size == 17) s!"{context}: expected 17 tab-separated fields"
    let some p := Probe.all.find? (fun p => p.operation == f[1]! && p.registerName == f[2]!)
      | throw (IO.userError s!"{context}: unknown operation/register")
    let some literal := literals.find? (fun l => l.negative == p.negative && l.name == f[0]!)
      | throw (IO.userError s!"{context}: no independent literal")
    let some seed := f[3]!.toNat? | throw (IO.userError s!"{context}: invalid seed")
    require (seed < 8 && f[3]! == toString seed) s!"{context}: invalid seed spelling/range"
    let key := (f[1]!,f[0]!,f[2]!,seed)
    require (!seen.contains key) s!"{context}: duplicate case/register/seed"
    seen := seen.push key
    require (f[4]! == codeHex p.bytes && f[16]! == "LITERAL") s!"{context}: instruction/classification mismatch"
    let before ← (f.toList.drop 6 |>.take 4).mapM (parseHex 16)
    let after ← (f.toList.drop 10 |>.take 4).mapM (parseHex 16)
    let row : Row := {
      probe := p, code := p.bytes, before := before, after := after,
      flagsBefore := ← parseHex 16 f[14]!, flagsAfter := ← parseHex 16 f[15]!,
      input := literal.input, output := literal.output, arithmeticFlags := literal.flags, seed := seed }
    require ((← parseHex 16 f[5]!) == literal.input && literalCheck row)
      s!"{context}: independent input/result/flags/prestate/frame check failed"
    rows := rows.push row
  require (rows.size == 1408 && (rows.filter (·.probe.negative)).size == 896)
    "incomplete matrix: expected 896 NEG32 and 512 BSWAP64"
  -- Uniqueness, membership in the fixed 44 x 4 x 8 matrix and this count
  -- establish completeness; explicitly check every required key as well.
  for literal in literals do
    for p in Probe.all do
      if p.negative != literal.negative then continue
      for seed in [0:8] do
        require (seen.contains (p.operation,literal.name,p.registerName,seed)) "missing required observation"
  return rows

private def wordSource (w : Word) : String := "0x" ++ hex w.toNat

private def listSource (ws : List Word) : String :=
  "[" ++ String.intercalate "," (ws.map wordSource) ++ "]"

private def rowSource (r : Row) : String :=
  "{ probe := ." ++ r.probe.sourceName ++ ", code := " ++
  listSource (r.code.map (·.setWidth 64)) ++ ", before := " ++ listSource r.before ++
  ", after := " ++ listSource r.after ++ ", flagsBefore := " ++ wordSource r.flagsBefore ++
  ", flagsAfter := " ++ wordSource r.flagsAfter ++ ", input := " ++ wordSource r.input ++
  ", output := " ++ wordSource r.output ++ ", arithmeticFlags := " ++ wordSource r.arithmeticFlags ++
  ", seed := " ++ toString r.seed ++ " }"

private def generate (rows : Array Row) (directory : System.FilePath) (stem : String) : IO Unit := do
  require (!stem.isEmpty && stem.toList.all Char.isAlpha) "module prefix must be alphabetic"
  IO.FS.createDirAll directory
  let mut modules : Array String := #[]
  -- Bound the DATA per module, never the kernel's resource settings.
  for chunk in [0:(rows.size + 15) / 16] do
    let name := s!"{stem}Chunk{chunk}"
    modules := modules.push name
    let mut source := "import tests.native.UnaryReplay\nset_option autoImplicit false\n" ++
      s!"namespace EDSL.Tests.UnaryReplay.{stem}\n"
    for i in [chunk * 16:min rows.size ((chunk + 1) * 16)] do
      source := source ++ s!"def row{i} : Row := {rowSource rows[i]!}\n" ++
        s!"theorem row{i}_pass : check row{i} = true := by decide +kernel\n"
    source := source ++ s!"end EDSL.Tests.UnaryReplay.{stem}\n"
    IO.FS.writeFile (directory / s!"{name}.lean") source
  IO.FS.writeFile (directory / s!"{stem}.modules") (String.intercalate "\n" modules.toList ++ "\n")
  IO.println s!"Generated {rows.size} observations in {modules.size} modules; kernel compilation still required."

private def selftest (rows : Array Row) : IO Unit := do
  -- These mutate a real observation and call the SAME full-step projection,
  -- bypassing the literal/schema guard. They detect weakened comparisons.
  let row := rows[0]!
  require (stepCheck row) "actual step rejects first valid observation"
  for bad in [
      { row with after := row.after.set 0 (row.after[0]! ^^^ 0x100000000) },
      { row with after := row.after.set 1 (row.after[1]! ^^^ 1) },
      { row with flagsAfter := row.flagsAfter ^^^ 0x10 },
      { row with flagsAfter := row.flagsAfter ^^^ 0x1000000000000000 },
      { row with before := row.before.set 0 1 },
      { row with code := [0xf7,0xd9] }] do
    require (!stepCheck bad) "full-step checker accepted corrupted observation"
  let some swap := rows.find? (fun r => !r.probe.negative && r.input == 0x0123456789abcdef)
    | throw (IO.userError "missing asymmetric BSWAP control")
  require (stepCheck swap) "actual step rejects asymmetric BSWAP observation"
  for bad in [
      { swap with after := swap.after.set 0 (swap.after[0]! ^^^ 0x100000000) },
      { swap with flagsAfter := swap.flagsAfter ^^^ 1 },
      { swap with code := [0x49,0x0f,0xc8] }] do
    require (!stepCheck bad) "full-step checker accepted corrupted BSWAP observation"
  IO.println "PASS: 9 full-production-step observation corruption controls."

def main (args : List String) : IO Unit := do
  match args with
  | ["inputs",expected,destination] =>
    let literals ← readLiterals expected
    let lines := literals.toList.map fun l =>
      s!"{if l.negative then "neg32" else "bswap64"}\t{l.name}\t{fixedHex l.input.toNat}"
    IO.FS.writeFile destination (String.intercalate "\n" lines ++ "\n")
  | ["generate",expected,capture,opcodes,directory,stem] =>
    let literals ← readLiterals expected
    checkOpcodeFiles opcodes
    let rows ← readRows literals capture
    selftest rows
    generate rows directory stem
  | _ => throw (IO.userError "usage: UnaryReplay inputs EXPECTED.tsv INPUTS.tsv | generate EXPECTED.tsv CAPTURE.tsv OPCODES OUTPUT PREFIX")

end EDSL.Tests.UnaryReplay
