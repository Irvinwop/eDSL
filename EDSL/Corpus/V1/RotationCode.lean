/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Arithmetic64.Rotation
import EDSL.X86.VCGen.CompilerComparisons

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.RotationCode
open X86

abbrev Compiler := X86.VCGen.CompilerComparisons.Compiler

/-- Complete unchanged default-compiler row09 symbols. GCC retains ENDBR64;
its modeled landing-pad behavior requires the recorded CET-off target.
Literal candidates alone establish neither decoding nor behavior. -/
def bytes : Compiler → List Byte
  | .defaultGCC => [0xf3,0x0f,0x1e,0xfa,0x48,0x89,0xf8,0x89,0xf1,0x48,0xd3,0xc0,0xc3]
  | .defaultClang => [0x89,0xf1,0x48,0x89,0xf8,0x48,0xd3,0xc0,0xc3]

abbrev spec := Arithmetic64.rotateLeft

end EDSL.Corpus.V1.RotationCode
