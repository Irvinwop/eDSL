/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Arithmetic64.Average
import EDSL.X86.VCGen.CompilerComparisons

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.AverageCode
open X86

abbrev Compiler := X86.VCGen.CompilerComparisons.Compiler

/-- Complete unchanged row-08 symbols. GCC includes its original ENDBR64.
Literal candidate bytes alone establish neither decoding nor behavior. -/
def bytes : Compiler → List Byte
  | .defaultGCC =>
      [0xf3,0x0f,0x1e,0xfa,0x48,0x89,0xf8,0x48,0x21,0xf7,
       0x48,0x31,0xf0,0x48,0xd1,0xe8,0x48,0x01,0xf8,0xc3]
  | .defaultClang =>
      [0x48,0x89,0xf0,0x48,0x21,0xf8,0x48,0x31,0xfe,
       0x48,0xd1,0xee,0x48,0x01,0xf0,0xc3]

/-- Full64 unsigned floor of the unbounded input sum divided by two. -/
abbrev spec := Arithmetic64.average

end EDSL.Corpus.V1.AverageCode
