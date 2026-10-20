/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.RotationCode
import EDSL.PureCall.Frame
import EDSL.X86.Sequential.Rotate
import EDSL.X86.VCGen.Tactics
import EDSL.X86.VCGen.ScratchFrame
import EDSL.X86.VCGen.PureCall

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.RotationBodies
open X86 X86.Sequential X86.VCGen

abbrev Compiler := RotationCode.Compiler
abbrev bytes := RotationCode.bytes
abbrev spec := RotationCode.spec

/-- Discovery proposes finite graph data; the shared production checker binds
all decoded instructions and successors to the complete original window. -/
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

/-- Both bodies may overwrite only RAX and RCX before RET. RET's RSP update
is allowed separately in the terminal frame and still proved exactly. -/
def scratch : List Register := [.rax, .rcx]

/-- Exact modeled retirement includes GCC's unchanged ENDBR64 and actual RET.
It is separate from admission and claims neither physical nor minimum cost. -/
def retired : Compiler → Nat
  | .defaultGCC => 5
  | .defaultClang => 4

def stackRead (initial : State) : Read := ⟨.stack, initial.registers .rsp, 8⟩

/-- The flag observation retains every flag for masked zero, defines OF for
one, and permits either independent OF for 2..63, framing every other bit. -/
def Observed (compiler : Compiler) (input : PureCall.Invocation spec)
    (initial : State) (result : Result) : Prop :=
  PureCall.Post spec input initial result.state ∧
    PureCall.ScratchFrame (.rsp :: scratch) initial result.state ∧
    result.instructions = retired compiler ∧ result.reads = [stackRead initial] ∧
    RolFlags64Admissible initial.flags (result.state.registers .rax)
      (input.value.2.toNat % 64) result.state.flags

private theorem saved_protected :
    ∀ register ∈ PureCall.calleeSaved, register ≠ .rsp ∧ register ∉ scratch := by
  decide +kernel

private theorem observed_of_frame {compiler : Compiler} {input : PureCall.Invocation spec}
    {initial : State} {result : Result}
    (frame : PureCall.ScratchFrame (.rsp :: scratch) initial result.state)
    (correct : spec.result input.value (result.state.registers .rax))
    (returnAddress : result.state.rip = input.returnAddress)
    (stackPointer : result.state.registers .rsp = initial.registers .rsp + 8)
    (count : result.instructions = retired compiler)
    (reads : result.reads = [stackRead initial])
    (flags : RolFlags64Admissible initial.flags (result.state.registers .rax)
      (input.value.2.toNat % 64) result.state.flags) :
    Observed compiler input initial result :=
  ⟨frame.post_return saved_protected correct returnAddress stackPointer,
    frame, count, reads, flags⟩

private theorem result_of_bound (input : PureCall.Invocation spec) (initial : State)
    (bound : PureCall.Bound spec input.value initial) :
    spec.result input.value
      ((initial.registers .rdi).rotateLeft
        (rolCount64 (((initial.registers .rsi).setWidth 32).setWidth 64))) := by
  obtain ⟨value, count⟩ := (Arithmetic64.rotateLeft_bound_iff input.value initial).mp bound
  change WordMath.IsRotateLeft64 _ _ _
  rw [value, count, rolCount64_low32, BitVec.rotateLeft_mod_eq_rotateLeft]
  exact WordMath.rotateLeft64_satisfies input.value.1 input.value.2.toNat

/-- Every full64 value and low32 count, arbitrary upper RSI, dirty unbound
state and every independent neutral choice stream satisfy GCC's generated WP. -/
theorem gcc_generated_vc (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultGCC) input initial) :
    wp gccGraph initial.rip (PureCallAllowed initial) 5 gccEntry initial
      (Observed .defaultGCC input initial) := by
  have stack := pre.stack
  have target := pre.returnCanonical
  have count := (Arithmetic64.rotateLeft_bound_iff input.value initial).mp pre.arguments |>.2
  have terminal := (PureCall.ScratchFrame.refl scratch initial).weaken
    (List.subset_cons_self Register.rsp scratch)
  vcgen_run gccGraph gccEntry simp [PureCallAllowed, PureCall.RawRead, stack, target,
    BitVec.add_assoc]
  vcgen_factor =>
    refine observed_of_frame ?_ (result_of_bound input initial pre.arguments) rfl rfl rfl rfl ?_
    · vcgen_scratch_frame terminal with
        simp only [Result.prepend, State.writeRegister, rolFlags64_preserves]
    · simp only [Result.prepend, count, rolCount64_low32]
      exact (rolFlags64_admissible_iff ..).mpr ⟨_, rfl⟩

/-- Clang follows its own instruction ordering and generated graph; its proof
does not import GCC's semantic annotation into a later artifact packet. -/
theorem clang_generated_vc (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultClang) input initial) :
    wp clangGraph initial.rip (PureCallAllowed initial) 4 clangEntry initial
      (Observed .defaultClang input initial) := by
  have stack := pre.stack
  have target := pre.returnCanonical
  have count := (Arithmetic64.rotateLeft_bound_iff input.value initial).mp pre.arguments |>.2
  have terminal := (PureCall.ScratchFrame.refl scratch initial).weaken
    (List.subset_cons_self Register.rsp scratch)
  vcgen_run clangGraph clangEntry simp [PureCallAllowed, PureCall.RawRead, stack, target,
    BitVec.add_assoc]
  vcgen_factor =>
    refine observed_of_frame ?_ (result_of_bound input initial pre.arguments) rfl rfl rfl rfl ?_
    · vcgen_scratch_frame terminal with
        simp only [Result.prepend, State.writeRegister, rolFlags64_preserves]
    · simp only [Result.prepend, count, rolCount64_low32]
      exact (rolFlags64_admissible_iff ..).mpr ⟨_, rfl⟩

theorem gcc_semantics :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask spec) (bytes .defaultGCC) :=
  pureCall_semantics_of_generated spec (bytes .defaultGCC) gccGraph gcc_valid gccEntry rfl
    5 (Observed .defaultGCC) (fun _ _ _ observed => observed.1) gcc_generated_vc

theorem clang_semantics :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask spec) (bytes .defaultClang) :=
  pureCall_semantics_of_generated spec (bytes .defaultClang) clangGraph clang_valid clangEntry rfl
    4 (Observed .defaultClang) (fun _ _ _ observed => observed.1) clang_generated_vc

/-- Universal returning execution and original current caller/code authority
at every actual prefix and return. The sequential model assumes stable ordinary
RAM, CET/IBT/shadow stacks disabled, supplied ownership and caller loans, and no
asynchronous interference. No physical CPU/Linux refinement, compiler
preservation, corpus certificate or concurrent guarantee follows. -/
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

/-- Actual decoded execution, exact accounting and operand permission at its
actual origin state use the shared engine, never a client evaluator. -/
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

end EDSL.Corpus.V1.RotationBodies
