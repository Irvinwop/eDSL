/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Scalar32.Signum
import EDSL.X86.VCGen.CompilerComparisons

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Complete candidate bodies for `c_sign_i32` and their independent signed
low32 contract. File authentication and execution require separate proofs. -/

namespace EDSL.Corpus.V1.SignumCode
open X86

abbrev Compiler := X86.VCGen.CompilerComparisons.Compiler

/-- Complete original symbol extents from the frozen default compiler files.
GCC retains ENDBR64, whose interpretation uses the recorded CET-off target.
These literal candidates alone establish neither decoding nor behavior. -/
def bytes : Compiler → List Byte
  | .defaultGCC =>
    [0xf3,0x0f,0x1e,0xfa,0x31,0xc0,0x85,0xff,0x0f,0x9f,0xc0,0xc1,0xef,0x1f,0x29,0xf8,0xc3]
  | .defaultClang =>
    [0x89,0xf9,0xc1,0xf9,0x1f,0x31,0xc0,0x85,0xff,0x0f,0x95,0xc0,0x09,0xc8,0xc3]

/-- Every signed low32 input is admitted, including INT32_MIN. The result
relation depends solely on integer order: negative, zero and positive inputs
produce low32 signed results -1, 0 and 1. Incoming RDI high bits remain free. -/
abbrev spec := Scalar32.signumSigned

theorem domain (input : BitVec 32) : spec.domain input :=
  Scalar32.signum_domain input

/-- Only RDI's low half is bound; all other registers, incoming flags and the
upper half of RDI remain unrestricted at this argument-binding layer. -/
theorem bound_iff (input : BitVec 32) (state : State) :
    PureCall.Bound spec input state ↔ (state.registers .rdi).setWidth 32 = input :=
  Scalar32.signum_bound_iff input state

theorem result_iff (input : BitVec 32) (output : Word) :
    spec.result input output ↔ output.setWidth 32 = WordMath.signum32 input :=
  Scalar32.signum_result_iff input output

/-- The shared callable postcondition observes the signed order result in the
actual final low32 RAX, independently of how those bits were computed. -/
theorem post_result {input : PureCall.Invocation spec} {initial final : State}
    (post : PureCall.Post spec input initial final) :
    WordMath.Signum input.value.toInt ((final.registers .rax).setWidth 32).toInt :=
  post.result

#print axioms domain
#print axioms bound_iff
#print axioms result_iff
#print axioms post_result
end EDSL.Corpus.V1.SignumCode
