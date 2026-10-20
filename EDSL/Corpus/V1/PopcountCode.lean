/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Arithmetic64.Popcount
import EDSL.X86.VCGen.CompilerComparisons

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.PopcountCode
open X86

abbrev Compiler := X86.VCGen.CompilerComparisons.Compiler

/-- Complete unchanged row-11 symbol extents, including GCC's ENDBR64 and both
compilers' original alignment padding. Candidate data alone proves neither
decoding, function behavior, final-file identity nor current OS authority. -/
def bytes : Compiler → List Byte
  | .defaultGCC =>
      [0xf3,0x0f,0x1e,0xfa,0x31,0xd2,0x48,0x85,0xff,0x74,0x11,
       0x0f,0x1f,0x44,0x00,0x00,0x48,0x8d,0x47,0xff,0x83,0xc2,0x01,
       0x48,0x21,0xc7,0x75,0xf4,0x89,0xd0,0xc3]
  | .defaultClang =>
      [0x31,0xc0,0x48,0x85,0xff,0x74,0x14,0x66,0x0f,0x1f,0x84,0x00,
       0x00,0x00,0x00,0x00,0x48,0x8d,0x4f,0xff,0xff,0xc0,0x48,0x21,
       0xcf,0x75,0xf5,0xc3]

/-- Full64 argument cardinality with unsigned low32 return. This independent
specification has no instruction, compiler, execution or graph premise. -/
abbrev spec := Arithmetic64.populationCount

end EDSL.Corpus.V1.PopcountCode
