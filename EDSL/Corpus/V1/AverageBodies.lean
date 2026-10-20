/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.AverageCode
import EDSL.PureCall.Frame
import EDSL.X86.VCGen.Tactics
import EDSL.X86.VCGen.PureCall

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.AverageBodies
open X86 X86.Sequential X86.VCGen

abbrev Compiler := AverageCode.Compiler
abbrev bytes := AverageCode.bytes
abbrev spec := AverageCode.spec

/-- Discovery proposes finite graph data. The production decoder/checker
authenticates every instruction and successor against the complete window. -/
def gccGraph : CFG.Graph := vcgen_graph (bytes .defaultGCC)
def clangGraph : CFG.Graph := vcgen_graph (bytes .defaultClang)

theorem gcc_valid : CFG.Valid (bytes .defaultGCC) gccGraph :=
  CFG.check_sound (by decide +kernel)

theorem clang_valid : CFG.Valid (bytes .defaultClang) clangGraph :=
  CFG.check_sound (by decide +kernel)

abbrev gccEntry : gccGraph.Index := ⟨0, by decide +kernel⟩
abbrev clangEntry : clangGraph.Index := ⟨0, by decide +kernel⟩

def graph : Compiler → CFG.Graph
  | .defaultGCC => gccGraph
  | .defaultClang => clangGraph

def entry : (compiler : Compiler) → (graph compiler).Index
  | .defaultGCC => gccEntry
  | .defaultClang => clangEntry

theorem valid (compiler : Compiler) : CFG.Valid (bytes compiler) (graph compiler) := by
  cases compiler with
  | defaultGCC => exact gcc_valid
  | defaultClang => exact clang_valid

@[simp] theorem entry_offset (compiler : Compiler) :
    ((graph compiler).node (entry compiler)).offset = 0 := by
  cases compiler <;> rfl

/-- Only these arithmetic scratch registers may change before RET. RET also
advances RSP; the terminal frame includes it explicitly. -/
def scratch : Compiler → List Register
  | .defaultGCC => [.rax, .rdi]
  | .defaultClang => [.rax, .rsi]

/-- Exact modeled instruction observations include RET and GCC's ENDBR64.
They are separate from admission and from any physical or minimum cost claim. -/
def retired : Compiler → Nat
  | .defaultGCC => 7
  | .defaultClang => 6

def stackRead (initial : State) : Read := ⟨.stack, initial.registers .rsp, 8⟩

def Observed (compiler : Compiler) (input : PureCall.Invocation spec)
    (initial : State) (result : Result) : Prop :=
  PureCall.Post spec input initial result.state ∧
    PureCall.ScratchFrame (.rsp :: scratch compiler) initial result.state ∧
    result.instructions = retired compiler ∧ result.reads = [stackRead initial]

private theorem saved_protected (compiler : Compiler) :
    ∀ register ∈ PureCall.calleeSaved, register ≠ .rsp ∧ register ∉ scratch compiler := by
  cases compiler <;> decide +kernel

private theorem observed_of_frame {compiler : Compiler} {input : PureCall.Invocation spec}
    {initial : State} {result : Result}
    (frame : PureCall.ScratchFrame (.rsp :: scratch compiler) initial result.state)
    (correct : spec.result input.value (result.state.registers .rax))
    (returnAddress : result.state.rip = input.returnAddress)
    (stackPointer : result.state.registers .rsp = initial.registers .rsp + 8)
    (count : result.instructions = retired compiler)
    (reads : result.reads = [stackRead initial]) :
    Observed compiler input initial result :=
  ⟨frame.post_return (saved_protected compiler) correct returnAddress stackPointer,
    frame, count, reads⟩

/-- GCC's finite production WP admits every full64 pair, all unbound state
and every independent AF stream. The mathematical sum may overflow a word. -/
theorem gcc_generated_vc (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultGCC) input initial) :
    wp gccGraph initial.rip (PureCallAllowed initial) 7 gccEntry initial
      (Observed .defaultGCC input initial) := by
  obtain ⟨left, right⟩ := (Arithmetic64.average_bound_iff input.value initial).mp pre.arguments
  have stack := pre.stack
  have target := pre.returnCanonical
  vcgen_run gccGraph gccEntry simp [PureCallAllowed, PureCall.RawRead, stack, target,
    BitVec.add_assoc, LogicalOp.eval]
  vcgen_factor =>
    refine observed_of_frame ?_ ?_ rfl rfl rfl rfl
    · constructor
      · rfl
      · simp only [Result.prepend, addFlags64_preserves, shrOneFlags64_preserves,
          logicalFlags64_preserves]
      · intro register untouched
        simp only [scratch, List.mem_cons, not_or] at untouched
        rcases untouched with ⟨notSP, notA, notD⟩
        simp only [Result.prepend, notSP, notA, notD, ite_false]
    · change (((initial.registers .rdi ^^^ initial.registers .rsi) >>> 1) +
        (initial.registers .rdi &&& initial.registers .rsi)).toNat =
          (input.value.1.toNat + input.value.2.toNat) / 2
      rw [left, right, BitVec.add_comm]
      exact WordMath.toNat_and_add_half_xor input.value.1 input.value.2

/-- Clang's independent generated obligation follows its own register order.
It does not import GCC's annotation or semantic proof into an artifact packet. -/
theorem clang_generated_vc (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultClang) input initial) :
    wp clangGraph initial.rip (PureCallAllowed initial) 6 clangEntry initial
      (Observed .defaultClang input initial) := by
  obtain ⟨left, right⟩ := (Arithmetic64.average_bound_iff input.value initial).mp pre.arguments
  have stack := pre.stack
  have target := pre.returnCanonical
  vcgen_run clangGraph clangEntry simp [PureCallAllowed, PureCall.RawRead, stack, target,
    BitVec.add_assoc, LogicalOp.eval]
  vcgen_factor =>
    refine observed_of_frame ?_ ?_ rfl rfl rfl rfl
    · constructor
      · rfl
      · simp only [Result.prepend, addFlags64_preserves, shrOneFlags64_preserves,
          logicalFlags64_preserves]
      · intro register untouched
        simp only [scratch, List.mem_cons, not_or] at untouched
        rcases untouched with ⟨notSP, notA, notS⟩
        simp only [Result.prepend, notSP, notA, notS, ite_false]
    · change ((initial.registers .rsi &&& initial.registers .rdi) +
        ((initial.registers .rsi ^^^ initial.registers .rdi) >>> 1)).toNat =
          (input.value.1.toNat + input.value.2.toNat) / 2
      rw [left, right, Nat.add_comm input.value.1.toNat]
      exact WordMath.toNat_and_add_half_xor input.value.2 input.value.1

theorem gcc_semantics :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask spec) (bytes .defaultGCC) :=
  pureCall_semantics_of_generated spec (bytes .defaultGCC) gccGraph gcc_valid gccEntry rfl
    7 (Observed .defaultGCC) (fun _ _ _ observed => observed.1) gcc_generated_vc

theorem clang_semantics :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask spec) (bytes .defaultClang) :=
  pureCall_semantics_of_generated spec (bytes .defaultClang) clangGraph clang_valid clangEntry rfl
    6 (Observed .defaultClang) (fun _ _ _ observed => observed.1) clang_generated_vc

/-- Universal returning execution and original current caller/code authority
at every prefix and return, with full RAM/permissions, callee-save ABI and
nonarithmetic flags framed. The sequential target assumes stable ordinary RAM,
CET/IBT/shadow stacks disabled, supplied logical authority and no asynchronous
interference. This asserts no native OS/CPU refinement or compiler preservation. -/
theorem semantics (compiler : Compiler) :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask spec) (bytes compiler) := by
  cases compiler with
  | defaultGCC => exact gcc_semantics
  | defaultClang => exact clang_semantics

theorem generated_vc (compiler : Compiler) (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes compiler) input initial) :
    wp (graph compiler) initial.rip (PureCallAllowed initial) (retired compiler)
      (entry compiler) initial (Observed compiler input initial) := by
  cases compiler with
  | defaultGCC => exact gcc_generated_vc input initial pre
  | defaultClang => exact clang_generated_vc input initial pre

/-- Actual decoded returning execution with the exact observations and operand
permissions at their actual origin states. No client evaluator is supplied. -/
theorem executes (compiler : Compiler) (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes compiler) input initial) (choices : Choices) :
    ∃ result, Sequential.run choices (retired compiler) initial = .ok result ∧
      Observed compiler input initial result ∧ CheckedTrace (PureCallAllowed initial) choices initial result := by
  obtain ⟨result, actual, observed, _, trace⟩ := run_sound (valid compiler) pre.code
    (by simp) (generated_vc compiler input initial pre) choices
  exact ⟨result, actual, observed, trace⟩

theorem observations (compiler : Compiler) {input : PureCall.Invocation spec} {initial : State}
    (pre : PureCall.Pre spec (bytes compiler) input initial) {choices : Choices} {result : Result}
    (execution : Sequential.Executes choices initial result) : Observed compiler input initial result := by
  obtain ⟨verified, actual, observed, _⟩ := executes compiler input initial pre choices
  have same := execution.fixed_choices_unique (Sequential.run_sound actual)
  subst verified
  exact observed

end EDSL.Corpus.V1.AverageBodies
