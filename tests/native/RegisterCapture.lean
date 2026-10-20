/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.native.UnaryReplay

set_option autoImplicit false

namespace EDSL.Tests.RegisterCapture
open X86 X86.Sequential

/- Shared capture mechanics. Only the selected list describes physical GPR
observations. Every other register uses the independent unary model canary;
RAM/value/execute/write maps are synthetic. This helper does not decode or
execute an instruction itself, or infer a hardware permission map. -/
structure Capture where
  code : List Byte
  before : List Word
  after : List Word
  flagsBefore : Word
  flagsAfter : Word
  deriving Inhabited

def registers (selected : List Register) (values : List Word) (r : Register) : Word :=
  ((selected.zip values).lookup r).getD (UnaryReplay.modelCanary r)

def Capture.initial (selected : List Register) (capture : Capture) : State where
  registers := registers selected capture.before
  rip := UnaryReplay.codeBase
  flags := capture.flagsBefore
  memory := UnaryReplay.replayMemory capture.code

def frameQueries (codeLength : Nat) : List Word :=
  [0,UnaryReplay.codeBase-1,UnaryReplay.codeBase,UnaryReplay.codeBase+1,
   UnaryReplay.codeBase+2,UnaryReplay.codeBase+3,UnaryReplay.codeBase+4,
   UnaryReplay.codeBase + BitVec.ofNat 64 codeLength,
   0x7ffffffffffe,0x7fffffffffff,0x800000000000,
   0xffff7fffffffffff,0xffff800000000000,0xffff800000000001,0xffffffffffffffff]

/-- Actual public production step for BOTH AF choices. All sixteen modeled
GPRs are compared; only `selected` entries came from physical observations.
Universal RAM/map preservation is separately supplied by fullRAMFrame below. -/
def stepCheck (selected : List Register) (capture : Capture) : Bool :=
  [false,true].all fun af =>
    let initial := capture.initial selected
    match Sequential.step af initial with
    | .error _ => false
    | .ok observation => match observation.result with
      | .next final =>
        final.rip == UnaryReplay.codeBase + BitVec.ofNat 64 capture.code.length &&
        final.flags == capture.flagsAfter && observation.reads == [] &&
        UnaryReplay.allRegisters.all (fun r =>
          final.registers r == registers selected capture.after r) &&
        (frameQueries capture.code.length).all (fun a =>
          final.memory.read a == initial.memory.read a &&
          final.memory.executable a == initial.memory.executable a &&
          final.memory.writable a == initial.memory.writable a)
      | _ => false

def check (selected : List Register) (capture : Capture)
    (instruction : Sequential.Instruction) : Bool :=
  capture.before.length == selected.length && capture.after.length == selected.length &&
  (match Sequential.decodeAt (capture.initial selected) with
    | .ok actual => decide (actual = instruction)
    | .error _ => false) && instruction.length == capture.code.length &&
  instruction.isNew && !instruction.isLocked && !instruction.choosesAF &&
  instruction.storeIntent (capture.initial selected) == none &&
  instruction.storeIntent64 (capture.initial selected) == none &&
  stepCheck selected capture

-- These existing universal theorems preserve the ENTIRE read/execute/write
-- maps for the authenticated decode/new/no-store/success conditions above.
-- They do not upgrade any modeled map into a physical observation.
export UnaryReplay (fullRAMFrame fullRAMAt)

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def parseHex (width : Nat) (s : String) : IO Word := do
  require (s.length == width) s!"expected {width} lower-case hex digits"
  let mut value := 0
  for c in s.toList do
    let digit := if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
      else if 'a' ≤ c && c ≤ 'f' then 10 + c.toNat - 'a'.toNat else 16
    require (digit < 16) "malformed lower-case hexadecimal"
    value := 16 * value + digit
  return BitVec.ofNat 64 value

def parseNat (s : String) : IO Nat := do
  let some n := s.toNat? | throw (IO.userError "malformed decimal")
  require (s == toString n) "noncanonical decimal"
  return n

def codeHex (bytes : List Byte) : String :=
  String.join (bytes.map fun b => let s := hex b.toNat; if s.length = 1 then "0" ++ s else s)

def parseCode (s : String) : IO (List Byte) := do
  require (!s.isEmpty && s.length % 2 == 0 && s.length ≤ 30) "malformed opcode length"
  let chars := s.toList.toArray
  let mut result := []
  for i in [0:s.length / 2] do
    let pair := String.ofList [chars[2*i]!,chars[2*i+1]!]
    result := result ++ [(← parseHex 2 pair).setWidth 8]
  return result

def wordSource (w : Word) : String := "0x" ++ hex w.toNat

def listSource (ws : List Word) : String :=
  "[" ++ String.intercalate "," (ws.map wordSource) ++ "]"

def Capture.source (c : Capture) : String :=
  "{ code := " ++ listSource (c.code.map (·.setWidth 64)) ++
  ", before := " ++ listSource c.before ++ ", after := " ++ listSource c.after ++
  ", flagsBefore := " ++ wordSource c.flagsBefore ++ ", flagsAfter := " ++ wordSource c.flagsAfter ++ " }"

end EDSL.Tests.RegisterCapture
