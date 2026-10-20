/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Arithmetic64.Spec
import EDSL.X86.VCGen.PureCall
import EDSL.X86.VCGen.CompilerComparisons

set_option warningAsError true

namespace EDSL.X86.VCGen.CompilerArithmetic
open Sequential
open CompilerComparisons (Compiler)

/-- Complete frozen ordinary body windows, without recompilation or changed
flags. Actual ELF identity, offsets, addresses and native mapping are separate
obligations. GCC's ENDBR64 retires under the existing IBT-disabled profile. -/
def bytes : Compiler → List Byte
  | .defaultGCC => [0xf3,0x0f,0x1e,0xfa,0x48,0x8d,0x04,0x37,0xc3]
  | .defaultClang => [0x48,0x8d,0x04,0x37,0xc3]

/-- Proposed data only; the production checker independently decodes every
node and validates the complete window, successors and depth certificate. -/
def graph : Compiler → CFG.Graph
  | .defaultGCC =>
      ⟨[⟨0, .endbr64IbtDisabled, true, 3⟩,
        ⟨4, .lea64 .rax (.indexed .rdi .rsi 0), false, 2⟩,
        ⟨8, .legacy .ret, false, 1⟩], 3⟩
  | .defaultClang =>
      ⟨[⟨0, .lea64 .rax (.indexed .rdi .rsi 0), true, 2⟩,
        ⟨4, .legacy .ret, false, 1⟩], 2⟩

theorem checked (compiler : Compiler) : CFG.check (bytes compiler) (graph compiler) = true := by
  cases compiler <;> decide +kernel

theorem valid (compiler : Compiler) : CFG.Valid (bytes compiler) (graph compiler) :=
  CFG.check_sound (checked compiler)

def entry (compiler : Compiler) : (graph compiler).Index :=
  ⟨0, by cases compiler <;> decide⟩

@[simp] theorem entry_offset (compiler : Compiler) :
    ((graph compiler).node (entry compiler)).offset = 0 := by
  cases compiler <;> rfl

private def returnEntry (compiler : Compiler) : (graph compiler).Index :=
  match compiler with
  | .defaultGCC => ⟨2, by decide⟩
  | .defaultClang => ⟨1, by decide⟩

/-- Independent exact observations, including RET and the GCC prefix. This
count is neither a task admission condition nor an operation-cost minimum. -/
def retired : Compiler → Nat
  | .defaultGCC => 3
  | .defaultClang => 2

def stackRead (initial : State) : Read := ⟨.stack, initial.registers .rsp, 8⟩

/-- Stronger evidence projects to the generic independent mathematical/ABI
postcondition. Count, ordered operand reads and ALL flags are separate from
the fixed arithmetic spec and present-only resource admission. -/
def Observed (compiler : Compiler) (input : PureCall.Invocation Arithmetic64.addition)
    (initial : State) (result : Result) : Prop :=
  PureCall.Post Arithmetic64.addition input initial result.state ∧
    result.instructions = retired compiler ∧ result.reads = [stackRead initial] ∧
    result.state.flags = initial.flags

/-- One generated production-WP proof for both compiler profiles, with no
local instruction interpreter, per-step proof chain or successor search.
All registers, flags, arguments and AF streams remain universal. LEA computes
an integer without accessing it, so no canonicality restriction is added. -/
theorem generated_vc (compiler : Compiler) (input : PureCall.Invocation Arithmetic64.addition)
    (initial : State) (pre : PureCall.Pre Arithmetic64.addition (bytes compiler) input initial) :
    wp (graph compiler) initial.rip (PureCallAllowed initial) (retired compiler)
      (entry compiler) initial (Observed compiler input initial) := by
  obtain ⟨left, right⟩ := (Arithmetic64.bound_iff input.value initial).mp pre.arguments
  have stack := pre.stack
  have target := pre.returnCanonical
  let ret := returnEntry compiler
  cases compiler <;> simp only [retired, entry]
  case' defaultGCC =>
    rw [wp]
    intro af
    conv in (CFG.Graph.node _ _).instruction =>
      simp [graph, CFG.Graph.node]
    simp only [execute, Instruction.operandReads, Instruction.length]
    refine ⟨by simp, ⟨⟨1, by decide⟩, rfl, ?_⟩⟩
  all_goals
    rw [wp]
    intro af
    conv in (CFG.Graph.node _ _).instruction =>
      simp [graph, CFG.Graph.node]
    simp only [execute, Instruction.operandReads, Instruction.length, Address.eval]
    refine ⟨by simp, ⟨ret, ?_, ?_⟩⟩
    · simp [ret, returnEntry, graph, CFG.Graph.node, BitVec.add_assoc]
    · rw [wp.eq_def]
      intro af'
      simp [ret, returnEntry, graph, CFG.Graph.node, execute, Instruction.operandReads,
        X86.executeInstruction, X86.executeRet, State.writeRegister, stack, target,
        PureCallAllowed, PureCall.RawRead]
      refine ⟨?_, rfl, rfl, rfl⟩
      refine ⟨?_, rfl, rfl, rfl, ?_, rfl⟩
      · change (initial.registers .rdi + initial.registers .rsi).toNat =
          (input.value.1.toNat + input.value.2.toNat) % 2^64
        rw [left, right]
        exact BitVec.toNat_add input.value.1 input.value.2
      · simp [PureCall.calleeSaved, Result.prepend]

/-- The existing generic bridge establishes universal raw and current-resource
semantics with every-prefix original caller authority. The present PureCall
precondition, stable ordinary RAM and Sequential.targetProfile are inherited
exactly; there is no native loading, CPU or concurrent-refinement claim. -/
theorem raw_semantics (compiler : Compiler) :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask Arithmetic64.addition) (bytes compiler) :=
  pureCall_semantics_of_generated Arithmetic64.addition (bytes compiler) (graph compiler)
    (valid compiler) (entry compiler) (entry_offset compiler) (retired compiler)
    (Observed compiler) (fun _ _ _ evidence => evidence.1) (generated_vc compiler)

/-- Actual production decoded execution for every admitted caller and AF stream. -/
theorem executes (compiler : Compiler) (input : PureCall.Invocation Arithmetic64.addition)
    (initial : State) (pre : PureCall.Pre Arithmetic64.addition (bytes compiler) input initial)
    (choices : Choices) :
    ∃ result, Sequential.run choices (retired compiler) initial = .ok result ∧
      Observed compiler input initial result ∧ CheckedTrace (PureCallAllowed initial) choices initial result := by
  obtain ⟨result, actual, observed, _, trace⟩ := run_sound (valid compiler) pre.code
    (by simp) (generated_vc compiler input initial pre) choices
  exact ⟨result, actual, observed, trace⟩

/-- Exact observations for any actual execution, independent of task/domain
selection. Instruction fetches are excluded from the operand-read trace. -/
theorem observations (compiler : Compiler) {input : PureCall.Invocation Arithmetic64.addition}
    {initial : State} (pre : PureCall.Pre Arithmetic64.addition (bytes compiler) input initial)
    {choices : Choices} {result : Result} (execution : Sequential.Executes choices initial result) :
    result.instructions = retired compiler ∧ result.reads = [stackRead initial] ∧
      result.state.flags = initial.flags := by
  obtain ⟨verified, actual, observed, _⟩ := executes compiler input initial pre choices
  have same := execution.fixed_choices_unique (Sequential.run_sound actual)
  subst verified
  exact observed.2

end EDSL.X86.VCGen.CompilerArithmetic
