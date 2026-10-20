/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.native.RegisterCapture

set_option autoImplicit false

namespace EDSL.Tests.CounterDisplacementReplay
open X86 X86.Sequential RegisterCapture

/- One family validator for any future client of these instructions. Probe
metadata is a literal contract, not a decoder/encoder or alternate executor.
All claimed model behavior is checked with public production decodeAt/step.
Physical snapshots cover only selectedRegisters. Synthetic canaries and RAM
maps plus universal fullRAMFrame/fullRAMAt remain MODEL frame challenges.
PUSHFQ RF/VM masking, AC/DF/debug/ordinary-RAM/CET target limits remain explicit;
finite observations do not establish universal physical ISA or OS refinement. -/
def selectedRegisters : List Register :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.r8,.r9,.r12,.r13,.r15]

structure Probe where
  name : String
  kind : Nat -- 0 ADD32, 1 INC32, 2 LEA64
  destination : Register
  base : Register
  index : Option Register
  scale : Fin 4
  immediate : Byte
  prefixed : Bool
  sib : Bool
  code : List Byte

instance : Inhabited Probe := ⟨⟨"",0,.rax,.rax,none,0,0,false,false,[]⟩⟩

def Probe.instruction (p : Probe) : Sequential.Instruction :=
  if p.kind == 0 then .addImm32 p.destination p.immediate p.prefixed
  else if p.kind == 1 then .inc32 p.destination p.prefixed
  else .lea64 p.destination (if p.sib then
    .sibDisp8 p.base p.index p.scale p.immediate else .baseDisp8 p.base p.immediate)

structure Row where
  probe : Probe
  capture : Capture
  seed : Nat
  deriving Inhabited

def signedByte (b : Byte) : Int :=
  if b.toNat < 128 then Int.ofNat b.toNat else Int.ofNat b.toNat - 256

def input (r : Row) (register : Register) : Word :=
  registers selectedRegisters r.capture.before register

/-- Independent modular mathematical result, with prestate operands. This
uses integer arithmetic, never the model's Address.eval, execute or flag APIs. -/
def mathematicalResult (r : Row) : Word :=
  if r.probe.kind == 2 then
    BitVec.ofInt 64 (Int.ofNat (input r r.probe.base).toNat +
      (match r.probe.index with
        | none => 0
        | some index => Int.ofNat (input r index).toNat * Int.ofNat (2 ^ r.probe.scale.val)) +
      signedByte r.probe.immediate)
  else
    let x := (input r r.probe.destination).toNat % 4294967296
    let y := if r.probe.kind == 1 then 1 else signedByte r.probe.immediate
    BitVec.ofInt 64 ((Int.ofNat x + y) % 4294967296)

/-- Six arithmetic predicates independently defined in Nat/Int: unsigned
carry, signed overflow, low-nibble carry, even low-byte parity, zero and sign.
INC uses incoming CF, including on wrap. All other saved bits are compared. -/
def mathematicalFlags (r : Row) : Word :=
  if r.probe.kind == 2 then r.capture.flagsBefore
  else
    let x := (input r r.probe.destination).toNat % 4294967296
    let y := if r.probe.kind == 1 then 1 else signedByte r.probe.immediate
    let unsignedY := (y % 4294967296).toNat
    let signedX : Int := if x < 2147483648 then Int.ofNat x else Int.ofNat x - 4294967296
    let sum := signedX + y
    let output := (mathematicalResult r).toNat
    let bits := (List.range 8).foldl (fun total i => total + (output / 2^i) % 2) 0
    let cf := if r.probe.kind == 1 then r.capture.flagsBefore.toNat % 2 == 1
      else decide (x + unsignedY ≥ 4294967296)
    let status := (if cf then 1 else 0) + (if bits % 2 == 0 then 4 else 0) +
      (if x % 16 + unsignedY % 16 ≥ 16 then 16 else 0) +
      (if output == 0 then 64 else 0) + (if output ≥ 2147483648 then 128 else 0) +
      (if sum < -2147483648 ∨ sum > 2147483647 then 2048 else 0)
    (r.capture.flagsBefore &&& ~~~UnaryReplay.arithmeticMask) ||| BitVec.ofNat 64 status

def independentCheck (r : Row) : Bool :=
  r.probe.kind < 3 && r.capture.code == r.probe.code &&
  r.capture.before.length == 11 && r.capture.after.length == 11 && r.seed < 4 &&
  r.capture.flagsBefore &&& UnaryReplay.arithmeticMask ==
    (UnaryReplay.seedFlags[r.seed]?).getD 0 &&
  r.capture.flagsBefore &&& 0x40500 == 0 && r.capture.flagsBefore &&& 2 == 2 &&
  (r.capture.flagsBefore ||| r.capture.flagsAfter) &&& 0x30000 == 0 &&
  input r .rsp != 0 && (input r .rsp).toNat % 8 == 0 &&
  registers selectedRegisters r.capture.after r.probe.destination == mathematicalResult r &&
  selectedRegisters.all (fun register => if register = r.probe.destination then true
    else registers selectedRegisters r.capture.after register == input r register) &&
  r.capture.flagsAfter == mathematicalFlags r

def check (r : Row) : Bool :=
  independentCheck r && RegisterCapture.check selectedRegisters r.capture r.probe.instruction

private def register (n : Nat) : IO Register := do
  let some r := UnaryReplay.allRegisters[n]? | throw (IO.userError "invalid register number")
  return r

private def readProbes (path : System.FilePath) (opcodes : System.FilePath) : IO (Array Probe) := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  require (lines.head? == some "probe\tkind\tdestination\tbase\tindex\tscale\timm8\tprefixed\tinstruction_hex")
    "probe table header/schema mismatch"
  let mut result := #[]
  for line in lines.drop 1 do
    if line.isEmpty then continue
    let f := (line.splitOn "\t").toArray
    require (f.size == 9) "malformed probe table"
    require (!f[0]!.isEmpty && f[0]!.toList.all (fun c => c.isAlphanum || c == '_') &&
      !result.any (fun p => p.name == f[0]!)) "invalid/duplicate probe name"
    let kind ← parseNat f[1]!
    let dst ← register (← parseNat f[2]!)
    let base ← register (← parseNat f[3]!)
    let idx ← parseNat f[4]!
    let index ← if idx == 16 then pure none else some <$> register idx
    let scale ← parseNat f[5]!
    let imm ← parseNat f[6]!
    let pref ← parseNat f[7]!
    require (kind < 3 && scale < 4 && imm < 256 && pref < 2 && dst != .rsp)
      "unsupported probe contract"
    let scale : Fin 4 ← if h : scale < 4 then pure ⟨scale,h⟩
      else throw (IO.userError "unsupported SIB scale")
    let code ← parseCode f[8]!
    let live ← IO.FS.readBinFile (opcodes / s!"{f[0]!}.bin")
    require (live.toList.map (BitVec.ofNat 8 ∘ UInt8.toNat) == code) "live opcode file mismatch"
    let p : Probe := ⟨f[0]!,kind,dst,base,index,scale,BitVec.ofNat 8 imm,
      pref == 1,code.length == 5,code⟩
    result := result.push p
  require (result.size == 72 && (result.filter (·.kind == 0)).size == 40 &&
    (result.filter (·.kind == 1)).size == 8 && (result.filter (·.kind == 2)).size == 24)
    "incomplete probe table"
  return result

private def readInputs (path : System.FilePath) : IO (Array (String × Word)) := do
  let mut result := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.isEmpty then continue
    let f := (line.splitOn "\t").toArray
    require (f.size == 2 && !result.any (fun i => i.1 == f[0]!)) "malformed/duplicate input table"
    result := result.push (f[0]!,← parseHex 16 f[1]!)
  require (result.size == 12) "incomplete input table"
  return result

private def header : String :=
  "case_id\tprobe\tseed\tinstruction_hex\trflags_before\trflags_after" ++
  "\tbefore_rax\tbefore_rcx\tbefore_rdx\tbefore_rbx\tbefore_rsp\tbefore_rbp" ++
  "\tbefore_r8\tbefore_r9\tbefore_r12\tbefore_r13\tbefore_r15" ++
  "\tafter_rax\tafter_rcx\tafter_rdx\tafter_rbx\tafter_rsp\tafter_rbp" ++
  "\tafter_r8\tafter_r9\tafter_r12\tafter_r13\tafter_r15"

private def readRows (probes : Array Probe) (inputs : Array (String × Word))
    (path : System.FilePath) : IO (Array Row) := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  require (lines.head? == some header) "capture header/schema mismatch"
  let mut result := #[]
  let mut seen : Array (String × String × Nat) := #[]
  for line in lines.drop 1 do
    if line.isEmpty then continue
    let f := (line.splitOn "\t").toArray
    require (f.size == 28) "malformed capture field count"
    let some p := probes.find? (fun p => p.name == f[1]!)
      | throw (IO.userError "unknown probe")
    let some c := inputs.toList.findIdx? (fun i => i.1 == f[0]!)
      | throw (IO.userError "unknown input")
    let seed ← parseNat f[2]!
    require (seed < 4) "invalid seed"
    let key := (f[0]!,p.name,seed)
    require (!seen.contains key) "duplicate observation"
    seen := seen.push key
    require (f[3]! == codeHex p.code) "captured opcode mismatch"
    let before ← (f.toList.drop 6 |>.take 11).mapM (parseHex 16)
    let after ← (f.toList.drop 17 |>.take 11).mapM (parseHex 16)
    let row : Row := ⟨p,⟨p.code,before,after,← parseHex 16 f[4]!,← parseHex 16 f[5]!⟩,seed⟩
    for j in [0:11] do
      if j == 4 then continue
      let requested := inputs[(c + (if j < 4 then j else j-1)) % 12]!.2
      require (before[j]! == requested) "controlled input mismatch"
    require (independentCheck row) "independent mathematical result/flags/frame mismatch"
    result := result.push row
  require (result.size == 3456) "incomplete matrix"
  for i in inputs do
    for p in probes do
      for seed in [0:4] do
        require (seen.contains (i.1,p.name,seed)) "missing required observation"
  return result

private def registerSource (r : Register) : String :=
  match r with
  | .rax => ".rax" | .rcx => ".rcx" | .rdx => ".rdx" | .rbx => ".rbx"
  | .rsp => ".rsp" | .rbp => ".rbp" | .rsi => ".rsi" | .rdi => ".rdi"
  | .r8 => ".r8" | .r9 => ".r9" | .r10 => ".r10" | .r11 => ".r11"
  | .r12 => ".r12" | .r13 => ".r13" | .r14 => ".r14" | .r15 => ".r15"

private def Probe.source (p : Probe) : String :=
  "{ name := " ++ reprStr p.name ++ ", kind := " ++ toString p.kind ++
  ", destination := " ++ registerSource p.destination ++ ", base := " ++ registerSource p.base ++
  ", index := " ++ (match p.index with | none => "none" | some r => "some " ++ registerSource r) ++
  ", scale := " ++ toString p.scale.val ++ ", immediate := " ++ wordSource (p.immediate.setWidth 64) ++
  ", prefixed := " ++ toString p.prefixed ++ ", sib := " ++ toString p.sib ++
  ", code := " ++ listSource (p.code.map (·.setWidth 64)) ++ " }"

private def selftest (rows : Array Row) : IO Unit := do
  let mut count := 0
  -- These controls bypass all independent/schema/fixture guards and challenge
  -- the actual production full-step projection on REAL captured observations.
  for name in ["add_eax_01","inc_r12d","lea_sib_dest_index_alias","lea_sib_all_alias"] do
    let some row := rows.find? (fun r => r.probe.name == name && r.seed == 1)
      | throw (IO.userError "missing semantic corruption control")
    let c := row.capture
    let some dest := selectedRegisters.findIdx? (· == row.probe.destination)
      | throw (IO.userError "unobserved destination")
    let other := if dest == 0 then 1 else 0
    require (RegisterCapture.stepCheck selectedRegisters c) "production step rejected valid control"
    for bad in [
        { c with after := c.after.set dest (c.after[dest]! ^^^ 0x100000000) },
        { c with after := c.after.set other (c.after[other]! ^^^ 1) },
        { c with flagsAfter := c.flagsAfter ^^^ 1 },
        { c with flagsAfter := c.flagsAfter ^^^ 0x10 },
        { c with flagsAfter := c.flagsAfter ^^^ 0x800 },
        { c with flagsAfter := c.flagsAfter ^^^ 0x1000000000000000 }] do
      require (!RegisterCapture.stepCheck selectedRegisters bad)
        "full production step accepted corrupted observation"
      count := count+1
  let some inc := rows.find? (fun r => r.probe.name == "inc_r12d" && r.seed == 1)
    | throw (IO.userError "missing INC CF control")
  require (!RegisterCapture.stepCheck selectedRegisters
    { inc.capture with flagsBefore := inc.capture.flagsBefore ^^^ 1 })
    "INC production step ignored incoming CF"
  let some lea := rows.find? (fun r => r.probe.name == "lea_sib_noindex_r12")
    | throw (IO.userError "missing no-index/R12 control")
  require (!RegisterCapture.stepCheck selectedRegisters
    { lea.capture with code := [0x4b,0x8d,0x4c,0x64,0xff] })
    "production step confused no-index with R12"
  let some alias := rows.find? (fun r => r.probe.name == "lea_sib_all_alias")
    | throw (IO.userError "missing prestate alias control")
  let some pos := selectedRegisters.findIdx? (· == .r13)
    | throw (IO.userError "missing R13 capture")
  require (!RegisterCapture.stepCheck selectedRegisters
    { alias.capture with before := alias.capture.before.set pos (alias.capture.before[pos]! ^^^ 1) })
    "LEA production step ignored aliased prestate"
  IO.println s!"PASS: {count+3} direct full-production-step corruption controls (both AF choices)."

private def generate (rows : Array Row) (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  let mut modules := []
  -- Split finite DATA per module; never change kernel recursion/heartbeat caps.
  for chunk in [0:(rows.size+15)/16] do
    let name := s!"CounterDisplacementChunk{chunk}"
    modules := modules ++ [name]
    let mut source := "import tests.native.CounterDisplacementReplay\nset_option autoImplicit false\n" ++
      "namespace EDSL.Tests.CounterDisplacementReplay.Generated\n"
    for i in [chunk*16:min rows.size ((chunk+1)*16)] do
      let r := rows[i]!
      source := source ++ s!"def row{i} : Row := " ++ "{ probe := " ++ r.probe.source ++
        ", capture := " ++ r.capture.source ++ ", seed := " ++ toString r.seed ++ " }\n" ++
        s!"theorem row{i}_pass : check row{i} = true := by decide +kernel\n"
    source := source ++ "end EDSL.Tests.CounterDisplacementReplay.Generated\n"
    IO.FS.writeFile (directory / s!"{name}.lean") source
  IO.FS.writeFile (directory / "CounterDisplacement.modules") (String.intercalate "\n" modules ++ "\n")
  IO.println s!"Generated {rows.size} observations in {modules.length} modules; kernel compilation required."

def main (args : List String) : IO Unit := do
  match args with
  | ["generate",probes,inputs,capture,opcodes,directory] =>
    let ps ← readProbes probes opcodes
    let ins ← readInputs inputs
    let rows ← readRows ps ins capture
    selftest rows
    generate rows directory
  | _ => throw (IO.userError "usage: CounterDisplacementReplay generate PROBES.tsv INPUTS.tsv CAPTURE.tsv OPCODES OUTPUT")

end EDSL.Tests.CounterDisplacementReplay
