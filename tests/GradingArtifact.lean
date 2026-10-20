/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Artifact
import EDSL.Audit

namespace EDSL.Tests.GradingArtifact
open X86 Grading

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

-- Standard external hex spellings exercise nibble order and both extremes.
example : Hex.decode "00010f107f80feff" = some [0, 1, 15, 16, 127, 128, 254, 255] := by decide
example : Hex.encode [0, 1, 15, 16, 127, 128, 254, 255] = "00010f107f80feff" := by decide
example : Hex.decode "Ff" = none := by decide
example : Hex.decode "0" = none := by decide
example : Hex.decode "0g" = none := by decide
example : Hex.decode "00 01" = none := by decide
example (bytes : List Byte) : Hex.literal (Hex.encode bytes) = bytes := Hex.literal_encode bytes

-- RET never truncates the selected window, and unsupported bytes can be
-- selected. Functional correctness is a separate fixed theorem obligation.
example : (Artifact.raw [0xc3, 0xff, 0x90]).selectedBytes = some [0xc3, 0xff, 0x90] := by decide
example : (Artifact.raw [0xff]).selectedBytes = some [0xff] := by decide
example : (Artifact.raw []).selectedBytes = none := by decide

-- Independent ELF64LE header, RX segment with four file bytes and eight RAM
-- bytes. The final four zero bytes are BSS, never file-backed instructions.
def file : List Byte := Hex.literal (
  "7f454c46020101000000000000000000" ++
  "02003e00010000008000400000000000" ++
  "40000000000000000000000000000000" ++
  "00000000400038000100000000000000" ++
  "01000000050000008000000000000000" ++
  "80004000000000000000000000000000" ++
  "04000000000000000800000000000000" ++
  "00100000000000000000000000000000" ++
  "8d4701c3")

-- An actual 65-byte executable file span catches accidental reuse of the
-- older CFG importer's 64-byte admission limit.
def longer : List Byte := ((file.take 128 ++ List.replicate 65 0x90).set 96 65).set 104 65

-- These are executable validator tests, not fixture-specific proof claims.
-- Integration separately forces kernel reduction of the full-file binding.
#eval (show IO Unit from do
  unless (Artifact.elf file 4).selectedBytes == some [0x8d, 0x47, 1, 0xc3] do
    throw (IO.userError "ELF entry bytes differ from independently specified code")
  for candidate in [Artifact.elf file 5,
      Artifact.elf (file.set 68 4) 4,
      Artifact.elf (file.set 24 0x81) 4,
      Artifact.elf (file.take 131) 4,
      Artifact.elf file 0,
      Artifact.elf longer 66] do
    unless (candidate : Artifact).selectedBytes.isNone do
      throw (IO.userError "invalid ELF code selection admitted")
  unless (Artifact.elf longer 65).selectedBytes == some (List.replicate 65 0x90) do
    throw (IO.userError "complete 65-byte executable span rejected"))

-- The general artifact wrapper entails the same fixed raw claim; no client
-- expected type, graph validity premise or favorable input predicate occurs.
example (id : TaskID) (artifact : Artifact) (code : List Byte)
    (selected : artifact.selectedBytes = some code) (proof : Grading.Claim id code) :
    Artifact.Claim id artifact := Artifact.certify id artifact code selected proof

end EDSL.Tests.GradingArtifact

#audit_edsl
