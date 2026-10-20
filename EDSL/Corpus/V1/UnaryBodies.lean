/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.UnaryCode
import EDSL.X86.VCGen
import EDSL.X86.VCGen.PureCall

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.UnaryBodies
open X86 X86.Sequential X86.VCGen

abbrev Compiler := UnaryCode.Compiler
abbrev Operation := UnaryCode.Operation
abbrev bytes := UnaryCode.bytes
abbrev spec := UnaryCode.spec

/-- Discovery proposes finite graph data; the production decoder/checker
independently authenticates every instruction and successor. -/
def graph : Compiler → Operation → CFG.Graph
  | .defaultGCC, .absSigned32 => vcgen_graph (bytes .defaultGCC .absSigned32)
  | .defaultClang, .absSigned32 => vcgen_graph (bytes .defaultClang .absSigned32)
  | .defaultGCC, .byteSwap64 => vcgen_graph (bytes .defaultGCC .byteSwap64)
  | .defaultClang, .byteSwap64 => vcgen_graph (bytes .defaultClang .byteSwap64)

theorem valid (compiler : Compiler) (operation : Operation) :
    CFG.Valid (bytes compiler operation) (graph compiler operation) :=
  CFG.check_sound (by cases compiler <;> cases operation <;> decide +kernel)

def entry (compiler : Compiler) (operation : Operation) : (graph compiler operation).Index :=
  ⟨0, by cases compiler <;> cases operation <;> decide +kernel⟩

@[simp] theorem entry_offset (compiler : Compiler) (operation : Operation) :
    ((graph compiler operation).node (entry compiler operation)).offset = 0 := by
  cases compiler <;> cases operation <;> rfl

/-- Exact modeled retired counts, including RET and GCC's ENDBR64. These are
independent observations, not task admission, cost minima or CPU timings. -/
def retired : Compiler → Operation → Nat
  | .defaultGCC, .absSigned32 => 5
  | .defaultClang, .absSigned32 => 4
  | .defaultGCC, .byteSwap64 => 4
  | .defaultClang, .byteSwap64 => 3

def stackRead (initial : State) : Read := ⟨.stack, initial.registers .rsp, 8⟩

/-- The independent result/ABI contract, exact count and original-slot read.
Abs additionally observes zero upper RAX; swap preserves all modeled flags. -/
def Observed (compiler : Compiler) (operation : Operation)
    (input : PureCall.Invocation (spec operation)) (initial : State) (result : Result) : Prop :=
  PureCall.Post (spec operation) input initial result.state ∧
    result.instructions = retired compiler operation ∧ result.reads = [stackRead initial] ∧
    match operation with
    | .absSigned32 => (result.state.registers .rax).toNat < 2^32
    | .byteSwap64 => result.state.flags = initial.flags

private theorem neg_sign (old : Word) (value : BitVec 32) :
    Condition.holds .sign (cmpFlags32 old 0 value) = (-value).msb := by
  change (cmpFlags32 old 0 value).getLsbD 7 = (-value).msb
  rw [(cmpFlags32_bits old 0 value).2.2.2.2.1]
  simp

private theorem absolute_selection (value : BitVec 32) (argument old : Word)
    (binding : argument.setWidth 32 = value) (domain : value.toInt ≠ -2147483648) :
    Scalar32.absoluteSigned.result value
      (((if Condition.holds .sign (cmpFlags32 old 0 value) then argument
        else (-value).setWidth 64).setWidth 32).setWidth 64) := by
  have selected :
      (if Condition.holds .sign (cmpFlags32 old 0 value) then argument
        else (-value).setWidth 64).setWidth 32 = WordMath.negSelect32 value := by
    rw [neg_sign]
    cases sign : (-value).msb <;>
      simp [sign, binding, WordMath.negSelect32, WordMath.selectSign32]
  change WordMath.AbsSquare value.toInt _
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, selected]
  exact WordMath.negSelect32_contract value domain

private theorem zero_extended_bound (value : BitVec 32) :
    (value.setWidth 64).toNat < 2^32 := by
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
  exact value.isLt

private theorem generated_abs (compiler : Compiler)
    (input : PureCall.Invocation Scalar32.absoluteSigned) (initial : State)
    (pre : PureCall.Pre Scalar32.absoluteSigned (bytes compiler .absSigned32) input initial) :
    wp (graph compiler .absSigned32) initial.rip (PureCallAllowed initial)
      (retired compiler .absSigned32) (entry compiler .absSigned32) initial
      (Observed compiler .absSigned32 input initial) := by
  change wp (graph compiler .absSigned32) initial.rip (PureCallAllowed initial)
    (retired compiler .absSigned32) (entry compiler .absSigned32) initial
    (fun result => PureCall.Post Scalar32.absoluteSigned input initial result.state ∧
      result.instructions = retired compiler .absSigned32 ∧
      result.reads = [stackRead initial] ∧ (result.state.registers .rax).toNat < 2^32)
  have stack := pre.stack
  have target := pre.returnCanonical
  have argument := (Scalar32.absolute_bound_iff input.value initial).mp pre.arguments
  have domain := pre.domain
  cases compiler <;> simp only [retired, entry] <;>
    vcgen_run graph entry simp [PureCallAllowed, PureCall.RawRead, stack, target,
      BitVec.add_assoc, X86.executeMovEaxEdi]
  all_goals refine ⟨⟨?_, rfl, rfl, rfl, ?_, ?_⟩, rfl, rfl, ?_⟩
  all_goals first
    | (change ∀ register ∈ PureCall.calleeSaved, _
       simp [PureCall.calleeSaved, Result.prepend])
    | exact cmpFlags32_preserves ..
    | exact zero_extended_bound _
    | simpa [Result.prepend, argument] using
        absolute_selection input.value (initial.registers .rdi) initial.flags argument domain

private theorem generated_swap (compiler : Compiler)
    (input : PureCall.Invocation Arithmetic64.byteSwap) (initial : State)
    (pre : PureCall.Pre Arithmetic64.byteSwap (bytes compiler .byteSwap64) input initial) :
    wp (graph compiler .byteSwap64) initial.rip (PureCallAllowed initial)
      (retired compiler .byteSwap64) (entry compiler .byteSwap64) initial
      (Observed compiler .byteSwap64 input initial) := by
  change wp (graph compiler .byteSwap64) initial.rip (PureCallAllowed initial)
    (retired compiler .byteSwap64) (entry compiler .byteSwap64) initial
    (fun result => PureCall.Post Arithmetic64.byteSwap input initial result.state ∧
      result.instructions = retired compiler .byteSwap64 ∧
      result.reads = [stackRead initial] ∧ result.state.flags = initial.flags)
  have stack := pre.stack
  have target := pre.returnCanonical
  have argument := (Arithmetic64.byteSwap_bound_iff input.value initial).mp pre.arguments
  cases compiler <;> simp only [retired, entry] <;>
    vcgen_run graph entry simp [PureCallAllowed, PureCall.RawRead, stack, target,
      BitVec.add_assoc]
  all_goals refine ⟨⟨?_, rfl, rfl, rfl, ?_, rfl⟩, rfl, rfl, rfl⟩
  all_goals first
    | (change ∀ register ∈ PureCall.calleeSaved, _
       simp [PureCall.calleeSaved, Result.prepend])
    | (change WordMath.ByteReverse64 input.value _
       simpa [Result.prepend, argument] using WordMath.byteSwap64_contract input.value)

/-- Generated production WP for all admitted inputs, arbitrary unbound state,
argument upper halves and AF streams. Only signed INT32_MIN is excluded by the
abs contract; byte reversal covers the entire full64 domain. RET and frames
use the shared checker and call bridge, without a client executor. -/
theorem generated_vc (compiler : Compiler) (operation : Operation)
    (input : PureCall.Invocation (spec operation)) (initial : State)
    (pre : PureCall.Pre (spec operation) (bytes compiler operation) input initial) :
    wp (graph compiler operation) initial.rip (PureCallAllowed initial)
      (retired compiler operation) (entry compiler operation) initial
      (Observed compiler operation input initial) := by
  cases operation with
  | absSigned32 => exact generated_abs compiler input initial pre
  | byteSwap64 => exact generated_swap compiler input initial pre

/-- Universal raw and current-resource semantics from the shared PureCall
bridge: original caller authority survives every actual prefix and RET.
The sequential long-mode profile assumes CET/IBT/shadow stacks disabled,
stable ordinary RAM and no asynchronous interference. This proves no native
CPU/OS correspondence, source preservation, concurrent history or whole OS. -/
theorem raw_semantics (compiler : Compiler) (operation : Operation) :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask (spec operation)) (bytes compiler operation) :=
  pureCall_semantics_of_generated (spec operation) (bytes compiler operation) (graph compiler operation)
    (valid compiler operation) (entry compiler operation) (entry_offset compiler operation)
    (retired compiler operation) (Observed compiler operation)
    (fun _ _ _ evidence => evidence.1) (generated_vc compiler operation)

/-- Actual decoded returning execution for every admitted state and AF stream,
including exact observations and permission evidence at each operand origin. -/
theorem executes (compiler : Compiler) (operation : Operation)
    (input : PureCall.Invocation (spec operation)) (initial : State)
    (pre : PureCall.Pre (spec operation) (bytes compiler operation) input initial)
    (choices : Choices) :
    ∃ result, Sequential.run choices (retired compiler operation) initial = .ok result ∧
      Observed compiler operation input initial result ∧
      CheckedTrace (PureCallAllowed initial) choices initial result := by
  obtain ⟨result, actual, observed, _, trace⟩ := run_sound (valid compiler operation) pre.code
    (by simp) (generated_vc compiler operation input initial pre) choices
  exact ⟨result, actual, observed, trace⟩

/-- The same exact observations constrain any actual returning execution;
operand traces exclude instruction fetches. -/
theorem observations (compiler : Compiler) (operation : Operation)
    {input : PureCall.Invocation (spec operation)} {initial : State}
    (pre : PureCall.Pre (spec operation) (bytes compiler operation) input initial)
    {choices : Choices} {result : Result} (execution : Sequential.Executes choices initial result) :
    Observed compiler operation input initial result := by
  obtain ⟨verified, actual, observed, _⟩ := executes compiler operation input initial pre choices
  have same := execution.fixed_choices_unique (Sequential.run_sound actual)
  subst verified
  exact observed

end EDSL.Corpus.V1.UnaryBodies
