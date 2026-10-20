/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Scalar32.Spec
import EDSL.Arithmetic64.Spec
import EDSL.X86.VCGen.CompilerComparisons

set_option autoImplicit false
set_option warningAsError true

/-! Candidate code and independent contracts for two frozen scalar clients.
This data establishes neither execution nor complete-file identity. -/
namespace EDSL.Corpus.V1.UnaryCode
open X86

abbrev Compiler := X86.VCGen.CompilerComparisons.Compiler

inductive Operation where
  | absSigned32 | byteSwap64
  deriving DecidableEq, Repr

/-- Complete unmodified GCC/Clang -O2 symbol extents. The original ENDBR64
remains present under the explicitly recorded CET-disabled machine profile. -/
def bytes (compiler : Compiler) (operation : Operation) : List Byte :=
  (match compiler with
    | .defaultGCC => [0xf3, 0x0f, 0x1e, 0xfa]
    | .defaultClang => []) ++
  (match operation with
    | .absSigned32 => [0x89, 0xf8, 0xf7, 0xd8, 0x0f, 0x48, 0xc7, 0xc3]
    | .byteSwap64 => [0x48, 0x89, 0xf8, 0x48, 0x0f, 0xc8, 0xc3])

/-- Mathematical result relations do not depend on the selected compiler,
its instruction sequence, graph, fuel, admission or a desired execution. -/
def spec : Operation → PureCall.Spec
  | .absSigned32 => Scalar32.absoluteSigned
  | .byteSwap64 => Arithmetic64.byteSwap

end EDSL.Corpus.V1.UnaryCode
