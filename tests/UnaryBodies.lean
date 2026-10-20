/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.UnaryBodies
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.UnaryBodies
open X86 X86.Sequential Corpus.V1.UnaryBodies

/- Full decoded routines execute with only code and the original return slot
mapped. Dirty upper argument and scratch halves expose width/CMOV mistakes.
These finite checks complement, rather than replace, universal body theorems. -/
private def memory (code : List Byte) : Memory where
  read address :=
    if 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + code.length then
      code[address.toNat - 0x1000]?
    else if 0x2000 ≤ address.toNat ∧ address.toNat < 0x2008 then
      ([0, 0x30, 0, 0, 0, 0, 0, 0] : List Byte)[address.toNat - 0x2000]?
    else none
  executable address := decide (0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + code.length)

private def initial (code : List Byte) (value : Word) : State where
  registers register :=
    if register = .rsp then 0x2000
    else if register = .rdi then value
    else if register = .r8 then 0xffeeddccbbaa9988
    else 0x13579bdf2468ace0
  rip := 0x1000
  flags := 0xfedcba9876542ad7
  memory := memory code

private def observed (code : List Byte) (value : Word) (af : Bool) :
    Option (Word × Nat × List Read × Word × Word) :=
  (Sequential.run (fun _ => af) 8 (initial code value)).toOption.map
    (fun result => (result.state.registers .rax, result.instructions,
      result.reads, result.state.registers .rsp, result.state.rip))

/-- The mathematical domain includes zero and both nearest signed endpoints;
the sole excluded endpoint cannot produce a representable nonnegative square
root. This checks admission independently of any execution. -/
theorem abs_domain_boundary :
    (spec .absSigned32).domain (0 : BitVec 32) ∧
    (spec .absSigned32).domain (0x7fffffff : BitVec 32) ∧
    (spec .absSigned32).domain (0x80000001 : BitVec 32) ∧
    ¬ (spec .absSigned32).domain (0x80000000 : BitVec 32) := by
  dsimp only [spec, Corpus.V1.UnaryCode.spec, Scalar32.absoluteSigned]
  decide +kernel

/-- Full routines must handle positive, negative and zero inputs despite
arbitrary high argument bits. The negative near-minimum catches off-by-one or
signed-overflow mistakes; full RAX observations catch missing zero extension. -/
theorem absolute_edges (compiler : Compiler) (af : Bool) :
    observed (bytes compiler .absSigned32) 0xfeedface80000001 af =
      some (0x7fffffff, retired compiler .absSigned32,
        [⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) ∧
    observed (bytes compiler .absSigned32) 0xdeadbeef7fffffff af =
      some (0x7fffffff, retired compiler .absSigned32,
        [⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) ∧
    observed (bytes compiler .absSigned32) 0xaaaaaaaa00000000 af =
      some (0, retired compiler .absSigned32,
        [⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) ∧
    observed (bytes compiler .absSigned32) 0x01234567ffffffff af =
      some (1, retired compiler .absSigned32,
        [⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) ∧
    observed (bytes compiler .absSigned32) 0xfedcba9800000001 af =
      some (1, retired compiler .absSigned32,
        [⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Distinct bytes and opposite extreme bits distinguish full64 reversal from
32-bit reversal, a wrong REX bank, an identity operation or reversed lane order. -/
theorem swap_edges (compiler : Compiler) (af : Bool) :
    observed (bytes compiler .byteSwap64) 0x0123456789abcdef af =
      some (0xefcdab8967452301, retired compiler .byteSwap64,
        [⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) ∧
    observed (bytes compiler .byteSwap64) 0x8000000000000000 af =
      some (0x80, retired compiler .byteSwap64,
        [⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) ∧
    observed (bytes compiler .byteSwap64) 1 af =
      some (0x0100000000000000, retired compiler .byteSwap64,
        [⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) := by
  cases compiler <;> cases af <;> refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

private def invertedAbs (compiler : Compiler) : List Byte :=
  (bytes compiler .absSigned32).set
    (match compiler with | .defaultGCC => 9 | .defaultClang => 5) 0x49

/-- A one-byte CMOVS-to-CMOVNS corruption is itself supported ISA code, but
must fail authentication against the original graph and change the result. -/
theorem inverted_condition_rejected (compiler : Compiler) (af : Bool) :
    CFG.check (invertedAbs compiler) (graph compiler .absSigned32) = false ∧
    observed (invertedAbs compiler) 7 af =
      some (0xfffffff9, retired compiler .absSigned32,
        [⟨.stack, 0x2000, 8⟩], 0x2008, 0x3000) ∧
    ¬ (spec .absSigned32).result (7 : BitVec 32) (0xfffffff9 : Word) := by
  cases compiler <;> cases af <;> refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  all_goals change ¬ (0 ≤ (-7 : Int) ∧ (-7 : Int) * (-7) = 7 * 7)
  all_goals decide +kernel

/-- Without a readable current caller slot, a fully decoded register body
cannot return. An invented successful result must not hide the actual fault. -/
theorem missing_return_slot (compiler : Compiler) (operation : Operation) (af : Bool) :
    (Sequential.run (fun _ => af) 8
      { initial (bytes compiler operation) 7 with
        memory := { memory (bytes compiler operation) with
          read := fun address =>
            if address.toNat < 0x2000 then (memory (bytes compiler operation)).read address
            else none } }) = .error (.inaccessibleStack 0x2000) := by
  cases compiler <;> cases operation <;> cases af <;> rfl

end EDSL.Tests.UnaryBodies

#audit_edsl
#print axioms EDSL.Corpus.V1.UnaryBodies.raw_semantics
#print axioms EDSL.Corpus.V1.UnaryBodies.observations
