/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ELF.FunctionCandidateSource
import EDSL.Examples.Verification.DoubleELF
import tests.ELFFunctionSymbol
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ELFFunctionCandidate
open X86 ELF ELF.FunctionCandidate
open Examples.Verification

private def data (file : List Byte) : ByteArray :=
  ⟨file.toArray.map fun byte => byte.toNat.toUInt8⟩

private def selectedBytes (file name : List Byte) : Except FunctionCandidate.Error (List Byte) :=
  (extract (data file) name).map (·.bytes)

private def equalResult (left right : Except FunctionCandidate.Error (List Byte)) : Bool :=
  match left, right with
  | .ok a, .ok b => a == b
  | .error a, .error b => decide (a = b)
  | _, _ => false

private def rejectsStale (changedFile changedName : List Byte) : Bool :=
  match extract (data DoubleELF.file) DoubleELF.name with
  | .error _ => false
  | .ok input => !input.check changedFile changedName

private def rejectsShortenedExtent : Bool :=
  match extract (data DoubleELF.file) DoubleELF.name with
  | .error _ => false
  | .ok input => !({ input with bytes := input.bytes.dropLast } : FunctionInput).check
      DoubleELF.file DoubleELF.name

/-- Regression checks for the untrusted candidate producer. These run normally,
not as semantics theorems. Generated artifact/CFG proofs are kernel checked
separately; the independently encoded fixtures do not use this extractor. -/
def checks : List (String × Bool) := [
  -- The entry is a different function: never substitute it for the named body.
  ("named non-entry bytes", equalResult (selectedBytes DoubleELF.file DoubleELF.name)
    (.ok [0x48, 0x8d, 4, 0x3f, 0xc3])),
  ("other declared full extent", equalResult (selectedBytes DoubleELF.file
    [0x68, 0x65, 0x6c, 0x70, 0x65, 0x72]) (.ok [0xb8, 42, 0, 0, 0, 0xc3])),
  ("missing name", equalResult (selectedBytes DoubleELF.file [0x6e, 0x6f, 0x6e, 0x65]) (.error .missingName)),
  -- An undefined dynamic alias still counts; no table can be silently omitted.
  ("complete dynamic table", equalResult (selectedBytes ELFFunctionSymbol.dynamic.file
    ELFFunctionSymbol.requested) (.ok [0xb8, 42, 0, 0, 0, 0xc3])),
  ("dynamic duplicate", equalResult (selectedBytes ELFFunctionSymbol.dynamicAlias.file
    ELFFunctionSymbol.requested) (.error .duplicateName)),
  ("repeated dynamic table", !(extract (data ELFFunctionSymbol.repeatedDynamic.file)
    ELFFunctionSymbol.requested).isOk),
  ("zero extent", !(extract (data ELFFunctionSymbol.zeroExtent.file)
    ELFFunctionSymbol.requested).isOk),
  ("wrong LOAD mapping", !(extract (data ELFFunctionSymbol.wrongLoadOffset.file)
    ELFFunctionSymbol.requested).isOk),
  -- Stale evidence cannot authenticate changed selected bytes or another name.
  ("stale extracted selected byte", rejectsStale
    (ELFFunctionSymbol.putLE DoubleELF.file 0x88 1 0x90) DoubleELF.name),
  ("stale extracted external name", rejectsStale DoubleELF.file
    [0x64, 0x6f, 0x75, 0x62, 0x6c, 0x66]),
  ("shortened extracted extent", rejectsShortenedExtent)]

def run : IO Unit := do
  for (name, passed) in checks do
    unless passed do throw (IO.userError s!"named ELF candidate regression: {name}")
  (← IO.getStdout).putStrLn s!"PASS: {checks.length} independent named ELF candidate regressions; no semantic proof claim"

end EDSL.Tests.ELFFunctionCandidate
#audit_edsl
