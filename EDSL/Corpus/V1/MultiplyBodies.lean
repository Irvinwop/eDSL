/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.MultiplyCode
import EDSL.PureCall.Frame
import EDSL.X86.VCGen.TacticsWith
import EDSL.X86.VCGen.PureCall
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Corpus.V1.MultiplyBodies
open X86 X86.Sequential X86.VCGen

abbrev Compiler := MultiplyCode.Compiler
abbrev bytes := MultiplyCode.bytes
abbrev spec := MultiplyCode.spec

/-- Finite graph proposals for the complete original GCC 12-byte and Clang
8-byte windows. Their instruction, extent and successor hints carry no trust;
the production checker authenticates them against the exact bytes below. -/
def gccGraph : CFG.Graph :=
  ⟨[⟨0,.endbr64IbtDisabled,true,4⟩, ⟨4,.movReg64 .rax .rdi,false,3⟩,
    ⟨7,.imulReg64 .rax .rsi,false,2⟩, ⟨11,.legacy .ret,false,1⟩],4⟩
def clangGraph : CFG.Graph :=
  ⟨[⟨0,.movReg64 .rax .rdi,true,3⟩, ⟨3,.imulReg64 .rax .rsi,false,2⟩,
    ⟨7,.legacy .ret,false,1⟩],3⟩

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

/-- Both bodies capture the original RDI and RSI operands and write only
RAX before RET. The terminal frame separately includes RET's RSP update. -/
def scratch : List Register := [.rax]

/-- Exact modeled retirement includes actual RET and GCC's original ENDBR64.
This is an instruction count, with no physical or minimum-cost claim. -/
def retired : Compiler → Nat
  | .defaultGCC => 4
  | .defaultClang => 3

def stackRead (initial : State) : Read := ⟨.stack, initial.registers .rsp, 8⟩

/-- The complete scalar postcondition, a stronger all-other-GPR frame, exact
retirement and the sole original return-slot read. All nonarithmetic flag bits
and the complete RAM and permission maps are preserved by the frame. -/
def Observed (compiler : Compiler) (input : PureCall.Invocation spec)
    (initial : State) (result : Result) : Prop :=
  PureCall.Post spec input initial result.state ∧
    PureCall.ScratchFrame (.rsp :: scratch) initial result.state ∧
    result.instructions = retired compiler ∧ result.reads = [stackRead initial]

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
    (reads : result.reads = [stackRead initial]) :
    Observed compiler input initial result :=
  ⟨frame.post_return saved_protected correct returnAddress stackPointer,
    frame, count, reads⟩

private theorem result_of_bound (input : PureCall.Invocation spec) (initial : State)
    (bound : PureCall.Bound spec input.value initial) :
    spec.result input.value (initial.registers .rdi * initial.registers .rsi) := by
  obtain ⟨left, right⟩ := (MultiplyCode.bound_iff input.value initial).mp bound
  change WordMath.MulModulo input.value.1 input.value.2
    (initial.registers .rdi * initial.registers .rsi)
  rw [left, right]
  exact WordMath.mulModulo_mul input.value.1 input.value.2

/-- Every full64 pair, arbitrary unbound state and every complete undefined
flag vector satisfy GCC's generated production WP. Overflow is admitted. -/
theorem gcc_generated_vc (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultGCC) input initial) :
    wpWith gccGraph initial.rip (PureCallAllowed initial) 4 gccEntry initial
      (Observed .defaultGCC input initial) := by
  have stack := pre.stack
  have target := pre.returnCanonical
  vcgen_runWith gccGraph gccEntry simp [PureCallAllowed, PureCall.RawRead, stack, target,
    BitVec.add_assoc]
  vcgen_factor =>
    refine observed_of_frame ?_ (result_of_bound input initial pre.arguments) rfl rfl rfl rfl
    · constructor
      · rfl
      · simp only [Result.prepend, imulFlags64_preserves]
      · intro register untouched
        simp only [scratch, List.mem_cons, not_or] at untouched
        rcases untouched with ⟨notSP, notA⟩
        simp only [Result.prepend, notSP, notA, ite_false]

/-- Clang's own checked graph and production vector obligations establish
the same universal contract with its original three-instruction body. -/
theorem clang_generated_vc (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultClang) input initial) :
    wpWith clangGraph initial.rip (PureCallAllowed initial) 3 clangEntry initial
      (Observed .defaultClang input initial) := by
  have stack := pre.stack
  have target := pre.returnCanonical
  vcgen_runWith clangGraph clangEntry simp [PureCallAllowed, PureCall.RawRead, stack, target,
    BitVec.add_assoc]
  vcgen_factor =>
    refine observed_of_frame ?_ (result_of_bound input initial pre.arguments) rfl rfl rfl rfl
    · constructor
      · rfl
      · simp only [Result.prepend, imulFlags64_preserves]
      · intro register untouched
        simp only [scratch, List.mem_cons, not_or] at untouched
        rcases untouched with ⟨notSP, notA⟩
        simp only [Result.prepend, notSP, notA, ite_false]

theorem generated_vc (compiler : Compiler) (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes compiler) input initial) :
    wpWith (graph compiler) initial.rip (PureCallAllowed initial) (retired compiler)
      (entry compiler) initial (Observed compiler input initial) := by
  cases compiler with
  | defaultGCC => exact gcc_generated_vc input initial pre
  | defaultClang => exact clang_generated_vc input initial pre

/-- Actual decoded vector execution has the complete postcondition and exact
observations. The checked trace ties every operand read to its successful
production memory access and permission in the actual pre-instruction state. -/
theorem executes (compiler : Compiler) (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes compiler) input initial)
    (choices : ChoiceStream FlagChoices) :
    ∃ result, runWith choices (retired compiler) initial = .ok result ∧
      Observed compiler input initial result ∧
      CheckedTraceWith (PureCallAllowed initial) choices initial result := by
  obtain ⟨result, actual, observed, _, trace⟩ := run_soundWith (valid compiler) pre.code
    (by simp) (generated_vc compiler input initial pre) choices
  exact ⟨result, actual, observed, trace⟩

/-- Universal returning machine-body semantics over all independent flag
vectors. The sequential target assumes stable ordinary RAM, 64-bit mode,
CET/IBT/shadow stacks disabled and no asynchronous interference. The theorem
establishes body/post/read/cost behavior; current-resource and registry bridges
are separate work. -/
theorem semantics (compiler : Compiler) (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes compiler) input initial) :
    AllExecutionsWith initial (Observed compiler input initial) := by
  intro choices
  obtain ⟨result, actual, observed, _⟩ := executes compiler input initial pre choices
  exact ⟨result, Engine.run_sound stepWith actual, observed⟩

/-- Any actual returning execution for an admitted invocation has these
observations, by uniqueness after fixing the complete vector stream. -/
theorem observations (compiler : Compiler) {input : PureCall.Invocation spec} {initial : State}
    (pre : PureCall.Pre spec (bytes compiler) input initial)
    {choices : ChoiceStream FlagChoices} {result : Result}
    (execution : ExecutesWith choices initial result) :
    Observed compiler input initial result := by
  obtain ⟨verified, actual, observed, _⟩ := executes compiler input initial pre choices
  have same := Engine.Executes.fixed_choices_unique stepWith execution
    (Engine.run_sound stepWith actual)
  subst verified
  exact observed

#print axioms gcc_valid
#print axioms clang_valid
#print axioms gcc_generated_vc
#print axioms clang_generated_vc
#print axioms executes
#print axioms semantics
#print axioms observations
end EDSL.Corpus.V1.MultiplyBodies
#audit_edsl
