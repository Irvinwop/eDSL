/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.native.RegisterCapture
import EDSL.X86.Sequential.ShiftOne

set_option autoImplicit false

namespace EDSL.Tests.ShiftOneReplay
open X86 X86.Sequential RegisterCapture

/- Only these eleven GPRs and PUSHFQ words were physically captured. RSP is
live; RSI/RDI/R10/R11/R14 use shared synthetic canaries. RIP and all RAM/read/
execute/write maps are model data. Assumptions: Linux x86-64 SysV long mode,
stable ordinary RAM/code/stack, CET/IBT/shadow stacks off, AC/DF/TF off, and no
debug/asynchronous boundary intervention. PUSHFQ hides RF/VM. Finite agreement
is not physical refinement, ABI/OS authority, compiler preservation or corpus
credit. Synthetic AF controls are not additional physical observations. -/
def selectedRegisters : List Register :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.r8,.r9,.r12,.r13,.r15]

structure Probe where
  name : String
  destination : Register
  code : List Byte

instance : Inhabited Probe := ⟨⟨"",.rax,[]⟩⟩

/-- Independent literal window contract, not an encoder or decoder. -/
def probes : List Probe := [
  ⟨"shr_rax_48",.rax,[0x48,0xd1,0xe8]⟩, ⟨"shr_rcx_48",.rcx,[0x48,0xd1,0xe9]⟩,
  ⟨"shr_rdx_48",.rdx,[0x48,0xd1,0xea]⟩, ⟨"shr_rbx_48",.rbx,[0x48,0xd1,0xeb]⟩,
  ⟨"shr_rbp_48",.rbp,[0x48,0xd1,0xed]⟩, ⟨"shr_r8_49",.r8,[0x49,0xd1,0xe8]⟩,
  ⟨"shr_r9_49",.r9,[0x49,0xd1,0xe9]⟩, ⟨"shr_r12_49",.r12,[0x49,0xd1,0xec]⟩,
  ⟨"shr_r13_49",.r13,[0x49,0xd1,0xed]⟩, ⟨"shr_r15_49",.r15,[0x49,0xd1,0xef]⟩,
  ⟨"shr_rax_4a",.rax,[0x4a,0xd1,0xe8]⟩, ⟨"shr_rcx_4a",.rcx,[0x4a,0xd1,0xe9]⟩,
  ⟨"shr_rdx_4a",.rdx,[0x4a,0xd1,0xea]⟩, ⟨"shr_rbx_4a",.rbx,[0x4a,0xd1,0xeb]⟩,
  ⟨"shr_rbp_4a",.rbp,[0x4a,0xd1,0xed]⟩, ⟨"shr_r8_4b",.r8,[0x4b,0xd1,0xe8]⟩,
  ⟨"shr_r9_4b",.r9,[0x4b,0xd1,0xe9]⟩, ⟨"shr_r12_4b",.r12,[0x4b,0xd1,0xec]⟩,
  ⟨"shr_r13_4b",.r13,[0x4b,0xd1,0xed]⟩, ⟨"shr_r15_4b",.r15,[0x4b,0xd1,0xef]⟩,
  ⟨"shr_rax_4c",.rax,[0x4c,0xd1,0xe8]⟩, ⟨"shr_rcx_4c",.rcx,[0x4c,0xd1,0xe9]⟩,
  ⟨"shr_rdx_4c",.rdx,[0x4c,0xd1,0xea]⟩, ⟨"shr_rbx_4c",.rbx,[0x4c,0xd1,0xeb]⟩,
  ⟨"shr_rbp_4c",.rbp,[0x4c,0xd1,0xed]⟩, ⟨"shr_r8_4d",.r8,[0x4d,0xd1,0xe8]⟩,
  ⟨"shr_r9_4d",.r9,[0x4d,0xd1,0xe9]⟩, ⟨"shr_r12_4d",.r12,[0x4d,0xd1,0xec]⟩,
  ⟨"shr_r13_4d",.r13,[0x4d,0xd1,0xed]⟩, ⟨"shr_r15_4d",.r15,[0x4d,0xd1,0xef]⟩,
  ⟨"shr_rax_4e",.rax,[0x4e,0xd1,0xe8]⟩, ⟨"shr_rcx_4e",.rcx,[0x4e,0xd1,0xe9]⟩,
  ⟨"shr_rdx_4e",.rdx,[0x4e,0xd1,0xea]⟩, ⟨"shr_rbx_4e",.rbx,[0x4e,0xd1,0xeb]⟩,
  ⟨"shr_rbp_4e",.rbp,[0x4e,0xd1,0xed]⟩, ⟨"shr_r8_4f",.r8,[0x4f,0xd1,0xe8]⟩,
  ⟨"shr_r9_4f",.r9,[0x4f,0xd1,0xe9]⟩, ⟨"shr_r12_4f",.r12,[0x4f,0xd1,0xec]⟩,
  ⟨"shr_r13_4f",.r13,[0x4f,0xd1,0xed]⟩, ⟨"shr_r15_4f",.r15,[0x4f,0xd1,0xef]⟩]

def inputs : List (String × Word) := [
  ("zero",0), ("one",1), ("two",2), ("three",3), ("nibble_last",0xf),
  ("nibble_next",0x10), ("nibble_next_odd",0x11), ("byte_signed_last",0x7f),
  ("byte_high",0x80), ("byte_high_odd",0x81), ("byte_last",0xff),
  ("byte_next",0x100), ("byte_next_odd",0x101), ("word_last",0xffff),
  ("word_next",0x10000), ("word_next_odd",0x10001),
  ("low32_signed_last",0x7fffffff), ("low32_high",0x80000000),
  ("low32_last",0xffffffff), ("high32_first",0x100000000),
  ("high32_first_odd",0x100000001), ("signed_last_even",0x7ffffffffffffffe),
  ("signed_last",0x7fffffffffffffff), ("highbit",0x8000000000000000),
  ("highbit_one",0x8000000000000001), ("highbit_two",0x8000000000000002),
  ("allones_even",0xfffffffffffffffe), ("allones",0xffffffffffffffff),
  ("dirty_alternating",0xa5a5a5a55a5a5a5a), ("dirty_alternating_odd",0x5a5a5a5aa5a5a5a5),
  ("dirty_high_zero_low",0xdeadbeef00000000), ("dirty_high_one_low",0x1234567800000001)]

def afMask : Word := 0x10
def arithmeticMask : Word := 0x8d5
def definedMask : Word := 0x8c5
def seedFlags : List Word := [0x44,0x55,0x894,0x845,0x10,0x4,0,0x84]

structure Row where
  probe : Nat
  input : Nat
  seed : Nat
  capture : Capture
  deriving Inhabited

def Row.window (r : Row) : Probe := (probes[r.probe]?).getD default

/-- Independent Nat division, remainder and arithmetic bit count. No hardware,
production result/flag helper, shift operation or program interpreter. -/
def mathematicalResult (c : Capture) (destination : Register) : Word :=
  BitVec.ofNat 64 ((registers selectedRegisters c.before destination).toNat / 2)

def mathematicalDefinedFlags (c : Capture) (destination : Register) : Word :=
  let x := (registers selectedRegisters c.before destination).toNat
  let y := x / 2
  let bits := (List.range 8).foldl (fun total i => total + (y / 2^i) % 2) 0
  BitVec.ofNat 64 ((x % 2) + (if bits % 2 == 0 then 4 else 0) +
    (if y == 0 then 64 else 0) + (if y ≥ 2^63 then 128 else 0) +
    (if x ≥ 2^63 then 2048 else 0))

def independentCheck (r : Row) : Bool :=
  let c := r.capture
  let p := r.window
  r.probe < 40 && r.input < 32 && r.seed < 8 && c.code == p.code &&
  c.before.length == 11 && c.after.length == 11 &&
  (List.range 11).all (fun j => if j == 4 then true else
    c.before[j]? == some ((inputs[(r.input + (if j < 4 then j else j-1)) % 32]?).getD ("",0)).2) &&
  c.flagsBefore &&& arithmeticMask == (seedFlags[r.seed]?).getD 0 &&
  c.flagsBefore &&& 0x40500 == 0 && c.flagsBefore &&& 2 == 2 &&
  (c.flagsBefore ||| c.flagsAfter) &&& 0x30000 == 0 &&
  registers selectedRegisters c.before .rsp != 0 &&
  (registers selectedRegisters c.before .rsp).toNat % 8 == 0 &&
  registers selectedRegisters c.after p.destination == mathematicalResult c p.destination &&
  selectedRegisters.all (fun reg => reg == p.destination ||
    registers selectedRegisters c.after reg == registers selectedRegisters c.before reg) &&
  c.flagsAfter &&& definedMask == mathematicalDefinedFlags c p.destination &&
  c.flagsAfter &&& ~~~arithmeticMask == c.flagsBefore &&& ~~~arithmeticMask

/-- Full GPR model and finite map challenges, reusable by controls that bypass
parsing and independent contracts. Universal map preservation is below. -/
def projection (c : Capture) (initial final : State) (length : Nat) : Bool :=
  final.rip == initial.rip + BitVec.ofNat 64 length &&
  final.flags &&& ~~~afMask == c.flagsAfter &&& ~~~afMask &&
  UnaryReplay.allRegisters.all (fun r =>
    final.registers r == registers selectedRegisters c.after r) &&
  (frameQueries c.code.length).all (fun a =>
    final.memory.read a == initial.memory.read a &&
    final.memory.executable a == initial.memory.executable a &&
    final.memory.writable a == initial.memory.writable a)

/-- Both plain next observations must exist, with no operand reads/events.
The actual full physical flags equal the model choice selected by observed
AF. The two admitted model flags differ by exactly AF, never by defined bits. -/
def stepCheck (c : Capture) : Bool :=
  let initial := c.initial selectedRegisters
  match Sequential.step false initial, Sequential.step true initial with
  | .ok first, .ok second => match first.result, second.result with
    | .next left, .next right =>
      first.reads == [] && second.reads == [] &&
      projection c initial left 3 && projection c initial right 3 &&
      !left.flags.getLsbD 4 && right.flags.getLsbD 4 &&
      left.flags ^^^ right.flags == afMask &&
      (if c.flagsAfter.getLsbD 4 then right.flags else left.flags) == c.flagsAfter
    | _, _ => false
  | _, _ => false

def modelCheck (c : Capture) (destination : Register) : Bool :=
  let initial := c.initial selectedRegisters
  let instruction := Sequential.Instruction.shrOne64 destination
  c.before.length == 11 && c.after.length == 11 && c.code.length == 3 &&
  (match Sequential.decodeAt initial with
    | .ok actual => decide (actual = instruction)
    | .error _ => false) &&
  instruction.length == 3 && instruction.isNew && instruction.choosesAF &&
  !instruction.isLocked && instruction.operandReads initial == [] &&
  instruction.storeIntent initial == none && instruction.storeIntent64 initial == none &&
  c.flagsAfter == shrOneFlags64 c.flagsBefore (initial.registers destination)
    (c.flagsAfter.getLsbD 4) && stepCheck c

def check (r : Row) : Bool :=
  independentCheck r && modelCheck r.capture r.window.destination

/-- Decode authenticates the universal production context theorem: every RAM
address/permission and every other GPR, exact RIP, and no operand effects.
Its state is the model; no unobserved physical state is inferred. -/
theorem decodedContext {initial : State} {destination : Register}
    (decoded : Sequential.decodeAt initial = .ok (.shrOne64 destination)) (af : Bool) :
    ∃ final, Sequential.step af initial = .ok ⟨.next final, []⟩ ∧
      (final.registers destination).toNat = (initial.registers destination).toNat / 2 ∧
      (∀ r, r ≠ destination → final.registers r = initial.registers r) ∧
      final.memory = initial.memory ∧
      final.flags = shrOneFlags64 initial.flags (initial.registers destination) af ∧
      final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask ∧
      final.rip = initial.rip + 3 := by
  obtain ⟨final, actual, _, result, others, memory, flags, preserved, rip⟩ :=
    execute_shrOne64_context initial destination af
  exact ⟨final, (step_eq_execute af decoded).trans actual,
    result, others, memory, flags, preserved, rip⟩

export Sequential (execute_shrOne64_choices shrOneFlags64_observed_witness)
export RegisterCapture (fullRAMFrame fullRAMAt)

private def fixedHex (w : Word) : String :=
  let s := hex w.toNat
  String.ofList (List.replicate (16-s.length) '0') ++ s

private def exactTable (path : System.FilePath) (lines : List String) : IO Unit := do
  require ((← IO.FS.readFile path) == String.intercalate "\n" lines ++ "\n")
    s!"literal matrix table mismatch: {path}"

private def readTables (directory : System.FilePath) : IO Unit := do
  exactTable (directory / "probes.tsv") ("probe\tdestination\tinstruction_hex" ::
    probes.map (fun p => s!"{p.name}\t{(UnaryReplay.allRegisters.idxOf p.destination)}\t{codeHex p.code}"))
  exactTable (directory / "inputs.tsv") ("case_id\tvalue" ::
    inputs.map (fun i => s!"{i.1}\t{fixedHex i.2}"))
  exactTable (directory / "seeds.tsv") ("seed\tarithmetic_flags" ::
    (List.range 8).map (fun n => s!"{n}\t{fixedHex ((seedFlags[n]?).getD 0)}"))
  for p in probes do
    let bytes ← IO.FS.readBinFile (directory / "opcodes" / s!"{p.name}.bin")
    require (bytes.toList.map (BitVec.ofNat 8 ∘ UInt8.toNat) == p.code)
      s!"saved opcode file mismatch: {p.name}"

private def header : String :=
  "case_id\tprobe\tseed\tinstruction_hex\trflags_before\trflags_after" ++
  "\tbefore_rax\tbefore_rcx\tbefore_rdx\tbefore_rbx\tbefore_rsp\tbefore_rbp" ++
  "\tbefore_r8\tbefore_r9\tbefore_r12\tbefore_r13\tbefore_r15" ++
  "\tafter_rax\tafter_rcx\tafter_rdx\tafter_rbx\tafter_rsp\tafter_rbp" ++
  "\tafter_r8\tafter_r9\tafter_r12\tafter_r13\tafter_r15"

private def readRows (path : System.FilePath) : IO (Array Row) := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  require (lines.head? == some header && lines.getLast? == some "") "capture header/termination mismatch"
  let mut rows := #[]
  let mut seen := Array.replicate 10240 false
  for line in lines.drop 1 |>.dropLast do
    let f := (line.splitOn "\t").toArray
    require (f.size == 28) "malformed capture field count"
    let some p := probes.findIdx? (fun p => p.name == f[1]!)
      | throw (IO.userError "unknown probe")
    let some i := inputs.findIdx? (fun i => i.1 == f[0]!)
      | throw (IO.userError "unknown input")
    let seed ← parseNat f[2]!
    require (seed < 8) "invalid seed"
    let key := (p*32+i)*8+seed
    require (!seen[key]!) "duplicate observation"
    seen := seen.set! key true
    let c : Capture := ⟨← parseCode f[3]!,
      ← (f.toList.drop 6 |>.take 11).mapM (parseHex 16),
      ← (f.toList.drop 17 |>.take 11).mapM (parseHex 16),
      ← parseHex 16 f[4]!, ← parseHex 16 f[5]!⟩
    let row : Row := ⟨p,i,seed,c⟩
    require (independentCheck row) s!"independent input/result/flags/frame mismatch: row {rows.size}"
    require (modelCheck c row.window.destination) s!"production SHR projection mismatch: row {rows.size}"
    rows := rows.push row
  require (rows.size == 10240 && seen.all id) "incomplete matrix: expected every 40 x 32 x 8 key exactly once"
  return rows

private def selftest (rows : Array Row) : IO Unit := do
  let some row := rows.find? (fun r => r.probe == 0 && r.input == 24 && r.seed == 1)
    | throw (IO.userError "missing highbit+1 control")
  let c := row.capture
  require (stepCheck c) "production rejected valid control"
  -- Bypass parser and mathematical/metadata guards: reach actual stepCheck.
  for mask in ([1,4,0x40,0x80,0x800,0x200,0x1000000000000000] : List Word) do
    require (!stepCheck { c with flagsAfter := c.flagsAfter ^^^ mask })
      "production projection accepted changed defined/preserved flag"
  for bad in [
      { c with after := c.after.set 0 (c.after[0]! ^^^ 1) },
      { c with after := c.after.set 0 (c.after[0]! ^^^ 0x100000000) },
      { c with after := c.after.set 1 (c.after[1]! ^^^ 1) },
      { c with after := c.after.set 4 (c.after[4]! ^^^ 8) },
      { c with code := [0x48,0xd1] },
      { c with code := [0x49,0xd1,0xe8] }] do
    require (!stepCheck bad) "production projection accepted corrupted register/bytes/REX target"
  require (!modelCheck { c with code := c.code ++ [0x90] } .rax)
    "production adapter accepted wrong window length"
  for af in [false,true] do
    let synthetic := { c with flagsAfter :=
      (c.flagsAfter &&& ~~~afMask) ||| (if af then afMask else 0) }
    require (stepCheck synthetic && modelCheck synthetic .rax &&
      independentCheck { row with capture := synthetic }) "AF policy excluded an independent choice"
  let initial := c.initial selectedRegisters
  let .ok observation := Sequential.step false initial
    | throw (IO.userError "control production step failed")
  let .next final := observation.result | throw (IO.userError "control not plain next")
  require (!projection c initial final 2 && !projection c initial final 4 &&
    !projection c initial { final with rip := initial.rip } 3)
    "projection accepted wrong length or no RIP advance"
  let address : Word := 0xffff800000000000
  for memory in [
      { final.memory with read := fun a => if a == address then some 0x68 else final.memory.read a },
      { final.memory with executable := fun a => if a == address then true else final.memory.executable a },
      { final.memory with writable := fun a => if a == address then false else final.memory.writable a }] do
    require (!projection c initial { final with memory := memory } 3)
      "projection accepted corrupted synthetic value/execute/write map"
  require (!projection c initial
    { final with registers := fun r => if r == .r14 then final.registers r ^^^ 1 else final.registers r } 3)
    "projection ignored unobserved model GPR"
  IO.println "PASS: direct production/projection controls; both synthetic AF choices accepted."

private def generate (rows : Array Row) (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  let mut modules := []
  let mut coverage := "row\tmodule\tcase_id\tprobe\tseed\n"
  -- 32 observations/module, ordinary kernel reduction and default budgets.
  for chunk in [0:320] do
    let name := s!"ShiftOneChunk{chunk}"
    modules := modules ++ [name]
    let mut source := "import tests.native.ShiftOneReplay\nset_option autoImplicit false\n" ++
      "namespace EDSL.Tests.ShiftOneReplay.Generated\n"
    for i in [chunk*32:(chunk+1)*32] do
      let r := rows[i]!
      source := source ++ s!"def row{i} : Row := " ++
        "{ probe := " ++ toString r.probe ++ ", input := " ++ toString r.input ++
        ", seed := " ++ toString r.seed ++ ", capture := " ++ r.capture.source ++ " }\n" ++
        s!"theorem row{i}_pass : check row{i} = true := by decide +kernel\n"
      coverage := coverage ++ s!"{i}\t{name}\t{((inputs[r.input]?).getD ("",0)).1}\t{r.window.name}\t{r.seed}\n"
    source := source ++ "end EDSL.Tests.ShiftOneReplay.Generated\n"
    IO.FS.writeFile (directory / s!"{name}.lean") source
  IO.FS.writeFile (directory / "ShiftOne.modules") (String.intercalate "\n" modules ++ "\n")
  IO.FS.writeFile (directory / "coverage.tsv") coverage
  IO.println "Generated all 10240 rows exactly once in 320 modules; kernel compilation and audit required."

def main (args : List String) : IO Unit := do
  match args with
  | ["generate",directory,output] =>
    readTables directory
    let rows ← readRows (System.FilePath.mk directory / "capture.tsv")
    selftest rows
    generate rows output
  | ["check",directory,capture] =>
    readTables directory
    let rows ← readRows capture
    IO.println s!"PASS: {rows.size} saved rows; IO check alone is not a kernel proof."
  | _ => throw (IO.userError "usage: ShiftOneReplay generate SEALED_RUN OUTPUT | check SEALED_RUN CAPTURE.tsv")

end EDSL.Tests.ShiftOneReplay
