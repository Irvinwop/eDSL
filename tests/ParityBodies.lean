/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.ParityBodies
import EDSL.Corpus.V1.ParityWindows
import EDSL.ELF.CallerResources.Stack
import EDSL.PureCall.Domain
import EDSL.Audit
import Lean.Util.FoldConsts

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ParityBodies
open X86 X86.Sequential OS Corpus.V1.ParityBodies

/- Only the exact code and original return slot are readable. Dirty scratch
registers and flags challenge initialization, operand widths and ABI framing. -/
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
    else 0xfedcba9876543210
  rip := 0x1000
  flags := 0xfedcba9876542ad7
  memory := memory code

private theorem current_code (compiler : Compiler) :
    CodeAt (memory (bytes compiler)) 0x1000 (bytes compiler) := by
  have finite : ∀ index : Fin (bytes compiler).length,
      (match fetchByte (memory (bytes compiler)) (0x1000 + BitVec.ofNat 64 index.val) with
      | .ok observed => observed == (bytes compiler)[index]
      | .error _ => false) = true := by
    cases compiler <;> decide +kernel
  refine ⟨by cases compiler <;> decide +kernel, ?_⟩
  intro offset byte present
  obtain ⟨inside, same⟩ := List.getElem?_eq_some_iff.mp present
  have checked := finite ⟨offset, inside⟩
  change (match fetchByte (memory (bytes compiler)) (0x1000 + BitVec.ofNat 64 offset) with
    | .ok observed => observed == (bytes compiler)[offset]
    | .error _ => false) = true at checked
  rw [same] at checked
  cases fetched : fetchByte (memory (bytes compiler)) (0x1000 + BitVec.ofNat 64 offset) with
  | error fault => simp only [fetched, Bool.false_eq_true] at checked
  | ok observed =>
    simp only [fetched] at checked
    exact congrArg Except.ok (beq_iff_eq.mp checked)

/-- Actual present entries admit every full64 value, without a result,
execution, useful-input or future-resource premise. -/
theorem all_full64_admitted (compiler : Compiler) (value : Word) :
    PureCall.Pre spec (bytes compiler) ⟨value, 0x3000⟩ (initial (bytes compiler) value) := by
  constructor
  · trivial
  · apply (Arithmetic64.parity64_bound_iff value _).mpr
    rfl
  · exact current_code compiler
  · change readWord (memory (bytes compiler)) 0x2000 = .ok 0x3000
    cases compiler <;> rfl
  · change canonical (0x3000 : Word) = true
    decide +kernel
  · change (0x2000 : Word).toNat + 8 < 2^64
    decide +kernel
  · change canonical ((0x2000 : Word) + 8) = true
    decide +kernel

/-- Observable execution with a literal low32 result and the full scalar
return/ABI/RAM contract. The AF stream is arbitrary. -/
def ReturnsParity (compiler : Compiler) (value : Word) (expected : Nat)
    (choices : Choices) : Prop :=
  ∃ result, Sequential.Executes choices (initial (bytes compiler) value) result ∧
    ((result.state.registers .rax).setWidth 32).toNat = expected ∧
    PureCall.Post spec ⟨value, 0x3000⟩ (initial (bytes compiler) value) result.state

private theorem literal_result (compiler : Compiler) (value : Word) (expected : Nat)
    (mathematics : WordMath.cardinality value % 2 = expected) (choices : Choices) :
    ReturnsParity compiler value expected choices := by
  have claimed := (semantics compiler).machine ⟨value, 0x3000⟩
    (initial (bytes compiler) value) (all_full64_admitted compiler value)
  obtain ⟨result, actual, post⟩ := claimed.1 choices
  have scalar := post.result
  change ((result.state.registers .rax).setWidth 32).toNat = WordMath.cardinality value % 2 at scalar
  exact ⟨result, actual, scalar.trans mathematics, post⟩

/-- Zero takes the entry bypass, independently of the dirty initial RAX. -/
theorem zero (compiler : Compiler) (choices : Choices) : ReturnsParity compiler 0 0 choices :=
  literal_result compiler 0 0 (by simp) choices

/-- Highest-bit-only catches truncation of full64 RDI before the loop. -/
theorem highest_bit (compiler : Compiler) (choices : Choices) :
    ReturnsParity compiler 0x8000000000000000 1 choices :=
  literal_result compiler 0x8000000000000000 1 (by decide +kernel) choices

/-- Sixty-four set positions have even parity; returning the count would fail. -/
theorem all_ones (compiler : Compiler) (choices : Choices) :
    ReturnsParity compiler 0xffffffffffffffff 0 choices := by
  apply literal_result
  change WordMath.cardinality (BitVec.allOnes 64) % 2 = 0
  rw [WordMath.cardinality_allOnes]

/-- Two separated endpoint bits challenge low32 input or byte-parity errors. -/
theorem separated_bits (compiler : Compiler) (choices : Choices) :
    ReturnsParity compiler 0x8000000000000001 0 choices :=
  literal_result compiler 0x8000000000000001 0 (by decide +kernel) choices

theorem three_bits (compiler : Compiler) (choices : Choices) :
    ReturnsParity compiler 0x8000000100000001 1 choices :=
  literal_result compiler 0x8000000100000001 1 (by decide +kernel) choices

/-- Code and a zero argument cannot manufacture a return from an unreadable
original return slot. This runs the production decoder and executor. -/
theorem missing_return_slot (compiler : Compiler) (af : Bool) :
    Sequential.run (fun _ => af) 14
      { initial (bytes compiler) 0 with
        memory := { memory (bytes compiler) with
          read := fun address =>
            if address.toNat < 0x2000 then (memory (bytes compiler)).read address
            else none } } = .error (.inaccessibleStack 0x2000) := by
  cases compiler <;> cases af <;> rfl

/- Actual-address witnesses use the neutral generic stack provider. They do
not import another corpus client's caller facts or a grading registration. -/
private abbrev caller := ELF.CallerResources.Stack.standard

private theorem fresh (compiler : Compiler) :
    ELF.fresh (Corpus.V1.ParityWindows.input compiler).table.image caller.prior = true := by
  apply ELF.CallerResources.Stack.check_sound
  cases compiler <;> decide +kernel

private theorem separate (compiler : Compiler) :
    Ownership.Disjoint ⟨(Corpus.V1.ParityWindows.input compiler).function.window.base,
      (Corpus.V1.ParityWindows.input compiler).bytes.length⟩ caller.region := by
  cases compiler
  · change Ownership.Disjoint ⟨0x402e20, 33⟩ ⟨0x700008, 8⟩
    decide +kernel
  · change Ownership.Disjoint ⟨0x401390, 36⟩ ⟨0x700008, 8⟩
    decide +kernel

private def environment (compiler : Compiler) : CallResources.Domain.Initial :=
  ELF.CallerResources.initial (Corpus.V1.ParityWindows.file compiler)
    (Corpus.V1.ParityWindows.input compiler) caller

private theorem environment_facts (compiler : Compiler) :
    CallResources.Domain.Facts (environment compiler) :=
  ELF.CallerResources.initial_facts (Corpus.V1.ParityWindows.checked compiler) (fresh compiler)
    ELF.CallerResources.Stack.standard_facts (separate compiler)

private def resource (compiler : Compiler) (value : Word) : PureCall.Resources spec :=
  PureCall.Domain.resource (environment compiler) spec value

private def loadedInitial (compiler : Compiler) (value : Word) : State :=
  PureCall.Domain.initial (environment compiler) spec value

/-- Complete frozen-file/name/extent/LOAD authentication and present neutral
stack authority admit every input at the function's real selected address. -/
theorem all_full64_resources (compiler : Compiler) (value : Word) :
    PureCall.ResourcePre spec (bytes compiler)
      (resource compiler value) (loadedInitial compiler value) :=
  PureCall.Domain.resource_pre (environment_facts compiler) spec value rfl trivial

/-- The useful witness inhabits the resource domain without narrowing it. -/
theorem useful_current (compiler : Compiler) :
    Grading.ReadOnlyNonvacuous (PureCall.readOnlyTask spec) (bytes compiler) :=
  PureCall.nonvacuous_of_resource (resource compiler 0x8000000000000001)
    (loadedInitial compiler 0x8000000000000001) Arithmetic64.parity64_useful_separated
    (all_full64_resources compiler 0x8000000000000001)

/-- Return preserves the original caller/code loans, owners and complete RAM.
The every-prefix policy uses actual read origin and original stack authority. -/
theorem original_caller (compiler : Compiler) (value : Word) :
    AllExecutions (loadedInitial compiler value) (fun result =>
      PureCall.Post spec (PureCall.resourceInput (resource compiler value))
        (loadedInitial compiler value) result.state ∧
      CallResources.Current (resource compiler value).call
        (resource compiler value).shared result.state) ∧
    Grading.ReadOnlyPolicy (loadedInitial compiler value)
      (CallResources.Current (resource compiler value).call (resource compiler value).shared)
      (fun _ read => CallResources.ReadAllowed (resource compiler value).call
        (resource compiler value).shared read) :=
  (semantics compiler).resource _ _ (all_full64_resources compiler value)

/-- Equal backing bytes at the original stack address give no DATA-origin
permission. The policy above must retain the actual STACK read origin. -/
theorem data_origin_denied (compiler : Compiler) (value : Word) :
    ¬ CallResources.ReadAllowed (resource compiler value).call
      (resource compiler value).shared ⟨.data, caller.stack, 8⟩ := by
  intro allowed
  cases allowed.1

/- Inspect actual theorem bodies as well as types: a direct theorem for one
binary must not carry the other compiler's loop annotations into its closure. -/
run_cmd do
  let environment ← Lean.getEnv
  for (root, forbidden) in #[
      (``Corpus.V1.ParityBodies.gcc_semantics,
        [``Corpus.V1.ParityBodies.clangAnnotations, ``Corpus.V1.ParityBodies.clang_generated,
          ``Corpus.V1.ParityBodies.clang_semantics]),
      (``Corpus.V1.ParityBodies.clang_semantics,
        [``Corpus.V1.ParityBodies.gccAnnotations, ``Corpus.V1.ParityBodies.gcc_generated,
          ``Corpus.V1.ParityBodies.gcc_semantics])] do
    let mut pending := [root]
    let mut seen : Lean.NameSet := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if !seen.contains name then
        if forbidden.contains name then
          throwError "{root} carries the other compiler's annotation dependency {name}"
        seen := seen.insert name
        let some information := environment.find? name
          | throwError "Missing dependency {name} of {root}"
        pending := information.getUsedConstantsAsSet.toList ++ pending
    Lean.logInfo m!"Checked independent compiler annotation closure for {root}"

#print axioms zero
#print axioms highest_bit
#print axioms all_ones
#print axioms separated_bits
#print axioms three_bits
#print axioms missing_return_slot
#print axioms useful_current
#print axioms original_caller
#print axioms data_origin_denied
end EDSL.Tests.ParityBodies
#audit_edsl
