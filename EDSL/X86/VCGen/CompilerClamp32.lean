/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Scalar32.Spec
import EDSL.X86.VCGen.PureCall
import EDSL.X86.VCGen.CompilerComparisons

set_option warningAsError true

namespace EDSL.X86.VCGen.CompilerClamp32
open Sequential
open CompilerComparisons (Compiler)

/-- The existing long-mode sequential profile, with IBT and shadow stacks
disabled. In particular GCC's ENDBR64 is an actual retired instruction.
Decoding does not establish these environmental CPU/feature assumptions. -/
abbrev targetProfile : TargetProfile := CompilerComparisons.targetProfile

/-- Complete frozen signed-clamp windows, without recompilation or changed
compiler flags. ELF identity, symbol offsets, addresses and native mappings
require separate binding; these literals establish none of those claims. -/
def bytes : Compiler → List Byte
  | .defaultGCC =>
      [0xf3,0x0f,0x1e,0xfa,0x39,0xd7,0x89,0xf0,0x0f,0x4e,0xd7,
        0x39,0xf7,0x0f,0x4d,0xc2,0xc3]
  | .defaultClang =>
      [0x89,0xd0,0x39,0xd7,0x0f,0x4c,0xc7,0x39,0xf7,0x0f,0x4c,0xc6,0xc3]

/-- Proposed graph data, independently authenticated by the production
decoder/checker. The legacy decoder takes precedence for GCC's MOV EAX,ESI;
Clang's MOV EAX,EDX uses the sequential MOV32 constructor. All CMOVs here are
unprefixed r32 operations, including zero-extension on the false outcome. -/
def graph : Compiler → CFG.Graph
  | .defaultGCC =>
      ⟨[⟨0, .endbr64IbtDisabled, true, 7⟩,
        ⟨4, .cmp32 .rdi .rdx false, false, 6⟩,
        ⟨6, .legacy .movEaxEsi, false, 5⟩,
        ⟨8, .cmovReg32 .lessEqual .rdx .rdi false, false, 4⟩,
        ⟨11, .cmp32 .rdi .rsi false, false, 3⟩,
        ⟨13, .cmovReg32 .greaterEqual .rax .rdx false, false, 2⟩,
        ⟨16, .legacy .ret, false, 1⟩], 7⟩
  | .defaultClang =>
      ⟨[⟨0, .movReg32 .rax .rdx, true, 6⟩,
        ⟨2, .cmp32 .rdi .rdx false, false, 5⟩,
        ⟨4, .cmovReg32 .less .rax .rdi false, false, 4⟩,
        ⟨7, .cmp32 .rdi .rsi false, false, 3⟩,
        ⟨9, .cmovReg32 .less .rax .rsi false, false, 2⟩,
        ⟨12, .legacy .ret, false, 1⟩], 6⟩

theorem checked (compiler : Compiler) : CFG.check (bytes compiler) (graph compiler) = true := by
  cases compiler <;> decide +kernel

theorem valid (compiler : Compiler) : CFG.Valid (bytes compiler) (graph compiler) :=
  CFG.check_sound (checked compiler)

def entry (compiler : Compiler) : (graph compiler).Index :=
  ⟨0, by cases compiler <;> decide⟩

@[simp] theorem entry_offset (compiler : Compiler) :
    ((graph compiler).node (entry compiler)).offset = 0 := by
  cases compiler <;> rfl

/-- Independent exact modeled retired counts, including RET and GCC's
ENDBR64. These are not graph-derived counts, cost minima or physical timings. -/
def retired : Compiler → Nat
  | .defaultGCC => 7
  | .defaultClang => 6

def stackRead (initial : State) : Read := ⟨.stack, initial.registers .rsp, 8⟩

/-- The independent signed relational/ABI contract, plus exact observations.
Complete memory equality includes all read, write and execute permissions.
The separate RAX bound observes the r32 zero-extension beyond C's low32 result. -/
def Observed (compiler : Compiler) (input : PureCall.Invocation Scalar32.clampSigned)
    (initial : State) (result : Result) : Prop :=
  PureCall.Post Scalar32.clampSigned input initial result.state ∧
    result.instructions = retired compiler ∧ result.reads = [stackRead initial] ∧
    (result.state.registers .rax).toNat < 2^32

/- Reduce the shared production WP/executor, as in CompilerComparisons.
Successor selection only matches the generated RIP against checked offsets;
there is no local interpreter, instruction proof chain or localVC callback. -/
local macro "reduce_generated" stack:ident target:ident : tactic => `(tactic|
  (rw [wp]
   intro af
   conv in (CFG.Graph.node _ _).instruction =>
     simp [graph, CFG.Graph.node]
   simp only [Sequential.execute, Sequential.Instruction.operandReads,
     Sequential.Instruction.length, X86.executeInstruction, X86.executeMovEaxEsi,
     X86.executeRet, State.writeRegister, ok_bind, pure_ok]
   simp [PureCallAllowed, PureCall.RawRead, State.writeRegister,
     $stack:ident, $target:ident]))

local macro "next_generated_at" index:num : tactic => `(tactic|
  (refine ⟨⟨$index:num, ?_⟩, ?_, ?_⟩
   · decide
   · solve | simp [graph, CFG.Graph.node, Sequential.Instruction.length, BitVec.add_assoc]))

local macro "next_generated" : tactic => `(tactic|
  first
  | next_generated_at 0
  | next_generated_at 1
  | next_generated_at 2
  | next_generated_at 3
  | next_generated_at 4
  | next_generated_at 5
  | next_generated_at 6)

/-- One generated-WP proof for both exact compiler windows. Admission is the
existing present-only PureCall precondition: signed lo ≤ hi, three low32 ABI
bindings, executable current bytes and the original caller slot. Argument high
halves, other registers, incoming flags and every AF choice remain universal.
The result is Scalar32.Clamped, independently defined over signed integers. -/
theorem generated_vc (compiler : Compiler) (input : PureCall.Invocation Scalar32.clampSigned)
    (initial : State) (pre : PureCall.Pre Scalar32.clampSigned (bytes compiler) input initial) :
    wp (graph compiler) initial.rip (PureCallAllowed initial) (retired compiler)
      (entry compiler) initial (Observed compiler input initial) := by
  obtain ⟨value, lower, upper⟩ := (Scalar32.clamp_bound_iff input.value initial).mp pre.arguments
  have ordered : input.value.lower.toInt ≤ input.value.upper.toInt := pre.domain
  have stack := pre.stack
  have target := pre.returnCanonical
  cases compiler <;> simp only [retired, entry] <;>
    repeat' (reduce_generated stack target; first | next_generated | skip)
  all_goals refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals simp [-BitVec.toInt_setWidth, Scalar32.clampSigned, Scalar32.Clamped,
    PureCall.calleeSaved, stackRead, Result.prepend, retired,
    Condition.cmp32_less, Condition.cmp32_lessEqual, Condition.cmp32_greaterEqual,
    cmpFlags32_preserves, value, lower, upper]
  all_goals repeat' split
  all_goals (try simp_all [-BitVec.toInt_setWidth]) <;> omega

/-- The shared PureCall adapter supplies universal raw and current-resource
semantics, retaining the original caller authority at every actual prefix and
after the actual RET. Stable ordinary RAM, no asynchronous interference and
targetProfile are inherited environmental assumptions. This establishes no
hardware, native loading, OS authority, source preservation or concurrency claim. -/
theorem raw_semantics (compiler : Compiler) :
    Grading.ReadOnlySemanticClaim (PureCall.readOnlyTask Scalar32.clampSigned) (bytes compiler) :=
  pureCall_semantics_of_generated Scalar32.clampSigned (bytes compiler) (graph compiler)
    (valid compiler) (entry compiler) (entry_offset compiler) (retired compiler)
    (Observed compiler) (fun _ _ _ evidence => evidence.1) (generated_vc compiler)

/-- Actual production decoded execution of current executable RAM, for every
admitted caller and AF stream, with read permissions at actual operand origins. -/
theorem executes (compiler : Compiler) (input : PureCall.Invocation Scalar32.clampSigned)
    (initial : State) (pre : PureCall.Pre Scalar32.clampSigned (bytes compiler) input initial)
    (choices : Choices) :
    ∃ result, Sequential.run choices (retired compiler) initial = .ok result ∧
      Observed compiler input initial result ∧ CheckedTrace (PureCallAllowed initial) choices initial result := by
  obtain ⟨result, actual, observed, _, trace⟩ := run_sound (valid compiler) pre.code
    (by simp) (generated_vc compiler input initial pre) choices
  exact ⟨result, actual, observed, trace⟩

/-- Exact count, ordered original-slot read and zero upper RAX for any actual
returning execution on admitted inputs. Instruction fetches are not operands. -/
theorem observations (compiler : Compiler) {input : PureCall.Invocation Scalar32.clampSigned}
    {initial : State} (pre : PureCall.Pre Scalar32.clampSigned (bytes compiler) input initial)
    {choices : Choices} {result : Result} (execution : Sequential.Executes choices initial result) :
    result.instructions = retired compiler ∧ result.reads = [stackRead initial] ∧
      (result.state.registers .rax).toNat < 2^32 := by
  obtain ⟨verified, actual, observed, _⟩ := executes compiler input initial pre choices
  have same := execution.fixed_choices_unique (Sequential.run_sound actual)
  subst verified
  exact observed.2

end EDSL.X86.VCGen.CompilerClamp32
