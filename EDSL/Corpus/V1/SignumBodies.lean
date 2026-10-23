/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.SignumCode
import EDSL.PureCall.Frame
import EDSL.X86.Sequential.LogicalConditions32
import EDSL.X86.VCGen.TacticsWith
import EDSL.X86.VCGen.PureCall
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Corpus.V1.SignumBodies
open X86 X86.Sequential X86.VCGen

abbrev Compiler := SignumCode.Compiler
abbrev bytes := SignumCode.bytes
abbrev spec := SignumCode.spec

/-- Untrusted complete graph proposals. The production checker authenticates
all instruction bytes, extents and successors, including GCC's original ENDBR. -/
def gccGraph : CFG.Graph :=
  ⟨[⟨0,.endbr64IbtDisabled,true,7⟩, ⟨4,.xorSelf32 .rax,false,6⟩,
    ⟨6,.test32 .rdi .rdi false,false,5⟩, ⟨8,.setcc .greater .rax false,false,4⟩,
    ⟨11,.shiftRightImm32 .logical .rdi 31 false,false,3⟩,
    ⟨14,.subReg32 .rax .rdi false,false,2⟩, ⟨16,.legacy .ret,false,1⟩],7⟩
def clangGraph : CFG.Graph :=
  ⟨[⟨0,.movReg32 .rcx .rdi,true,7⟩,
    ⟨2,.shiftRightImm32 .arithmetic .rcx 31 false,false,6⟩,
    ⟨5,.xorSelf32 .rax,false,5⟩, ⟨7,.test32 .rdi .rdi false,false,4⟩,
    ⟨9,.setcc .notEqual .rax false,false,3⟩,
    ⟨12,.logicalReg32 .bor .rax .rcx false,false,2⟩, ⟨14,.legacy .ret,false,1⟩],7⟩

theorem gcc_valid : CFG.Valid (bytes .defaultGCC) gccGraph :=
  CFG.check_sound (by decide +kernel)
theorem clang_valid : CFG.Valid (bytes .defaultClang) clangGraph :=
  CFG.check_sound (by decide +kernel)

abbrev gccEntry : gccGraph.Index := ⟨0, by decide +kernel⟩
abbrev clangEntry : clangGraph.Index := ⟨0, by decide +kernel⟩

def graph : Compiler → CFG.Graph
  | .defaultGCC => gccGraph | .defaultClang => clangGraph

def entry : (compiler : Compiler) → (graph compiler).Index
  | .defaultGCC => gccEntry | .defaultClang => clangEntry

theorem valid (compiler : Compiler) : CFG.Valid (bytes compiler) (graph compiler) := by
  cases compiler with
  | defaultGCC => exact gcc_valid
  | defaultClang => exact clang_valid

@[simp] theorem entry_offset (compiler : Compiler) :
    ((graph compiler).node (entry compiler)).offset = 0 := by
  cases compiler <;> rfl

def scratch : Compiler → List Register
  | .defaultGCC => [.rax,.rdi] | .defaultClang => [.rax,.rcx]

/-- Exact local modeled count, including RET. This is no optimality or physical
cycle claim. Input sign, argument upper halves and flag choices do not affect it. -/
def retired (_ : Compiler) : Nat := 7

def stackRead (initial : State) : Read := ⟨.stack,initial.registers .rsp,8⟩

/-- Stronger observations include zero-extended RAX, complete RAM and permission
maps, every nonscratch register, actual return target, RSP+8 and the sole read. -/
def Observed (compiler : Compiler) (input : PureCall.Invocation spec)
    (initial : State) (result : Result) : Prop :=
  PureCall.Post spec input initial result.state ∧
    PureCall.ScratchFrame (.rsp :: scratch compiler) initial result.state ∧
    result.instructions = retired compiler ∧ result.reads = [stackRead initial] ∧
    (result.state.registers .rax).toNat < 2^32

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
    (reads : result.reads = [stackRead initial])
    (upperClear : (result.state.registers .rax).toNat < 2^32) :
    Observed compiler input initial result :=
  ⟨frame.post_return (saved_protected compiler) correct returnAddress stackPointer,
    frame,count,reads,upperClear⟩

private theorem zero_extended_bound (value : BitVec 32) :
    (value.setWidth 64).toNat < 2^32 := by
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
  exact value.isLt

private theorem low8_positive (old : Word) (value : BitVec 32) (af : Bool) :
    replaceLow8 (0#64)
      (if Condition.greater.holds (logicalFlags32 old value af) = true then 1#8 else 0#8) =
      (if 0 < value.toInt then (1 : Word) else 0) := by
  rw [Condition.logical32_greater_zero]
  by_cases positive : 0 < value.toInt <;> simp [positive, replaceLow8]

private theorem low8_nonzero (old : Word) (value : BitVec 32) (af : Bool) :
    replaceLow8 (0#64)
      (if Condition.notEqual.holds (logicalFlags32 old value af) = true then 1#8 else 0#8) =
      (if value.toInt ≠ 0 then (1 : Word) else 0) := by
  rw [Condition.logical32_notEqual_int]
  by_cases zero : value.toInt = 0 <;> simp [zero, replaceLow8]

private theorem low32_zero_extended_shift (value : BitVec 32) (count : Nat) :
    ((value.setWidth 64) >>> count).setWidth 32 = value >>> count := by
  rw [← BitVec.setWidth_ushiftRight (by decide : 32 ≤ 64)]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

/-- Both algebraic forms satisfy the independent order relation. -/
private theorem gcc_result (value : BitVec 32) :
    spec.result value
      (((if 0 < value.toInt then (1 : BitVec 32) else 0) - (value >>> 31)).setWidth 64) := by
  change WordMath.Signum value.toInt _
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  exact WordMath.positive_sub_signBit_contract value

private theorem clang_result (value : BitVec 32) :
    spec.result value
      (((if value.toInt ≠ 0 then (1 : BitVec 32) else 0) ||| value.sshiftRight 31).setWidth 64) := by
  change WordMath.Signum value.toInt _
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  exact WordMath.nonzero_or_signMask_contract value

/-- The original GCC body meets the generated production WP for every low32
input, including INT32_MIN, every unbound register/high half and flag vector. -/
theorem gcc_generated_vc (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultGCC) input initial) :
    wpWith gccGraph initial.rip (PureCallAllowed initial) 7 gccEntry initial
      (Observed .defaultGCC input initial) := by
  have stack := pre.stack
  have target := pre.returnCanonical
  have argument := (SignumCode.bound_iff input.value initial).mp pre.arguments
  vcgen_runWith gccGraph gccEntry simp [PureCallAllowed, PureCall.RawRead,stack,target,
    BitVec.add_assoc, shiftCount32, shiftRightResult32]
  vcgen_factor =>
    refine observed_of_frame ?_ ?_ rfl rfl rfl rfl (zero_extended_bound _)
    · constructor
      · rfl
      · simp only [Result.prepend, cmpFlags32_preserves, shiftRightFlags32_preserves,
          logicalFlags32_preserves]
      · intro register untouched
        simp only [scratch,List.mem_cons,not_or] at untouched
        rcases untouched with ⟨notSP,notA,notDI⟩
        simp only [Result.prepend,notSP,notA,notDI,ite_false]
    · simp only [Result.prepend, reduceCtorEq, ite_true, ite_false]
      rw [low8_positive]
      simp only [argument]
      rw [low32_zero_extended_shift (input.value : BitVec 32) 31]
      by_cases positive : 0 < input.value.toInt <;>
        simpa [positive] using gcc_result input.value

/-- Clang's distinct graph uses the same result specification and shared
vector semantics. Undefined AF and OF are never constrained to agree. -/
theorem clang_generated_vc (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes .defaultClang) input initial) :
    wpWith clangGraph initial.rip (PureCallAllowed initial) 7 clangEntry initial
      (Observed .defaultClang input initial) := by
  have stack := pre.stack
  have target := pre.returnCanonical
  have argument := (SignumCode.bound_iff input.value initial).mp pre.arguments
  vcgen_runWith clangGraph clangEntry simp [PureCallAllowed,PureCall.RawRead,stack,target,
    BitVec.add_assoc, shiftCount32, shiftRightResult32]
  vcgen_factor =>
    refine observed_of_frame ?_ ?_ rfl rfl rfl rfl (zero_extended_bound _)
    · constructor
      · rfl
      · simp only [Result.prepend, logicalFlags32_preserves, shiftRightFlags32_preserves]
      · intro register untouched
        simp only [scratch,List.mem_cons,not_or] at untouched
        rcases untouched with ⟨notSP,notA,notC⟩
        simp only [Result.prepend,notSP,notA,notC,ite_false]
    · simp only [Result.prepend, reduceCtorEq, ite_true, ite_false]
      rw [low8_nonzero]
      simp only [argument, LogicalOp.eval]
      by_cases zero : input.value.toInt = 0 <;>
        simpa [zero] using clang_result input.value

theorem generated_vc (compiler : Compiler) (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes compiler) input initial) :
    wpWith (graph compiler) initial.rip (PureCallAllowed initial) (retired compiler)
      (entry compiler) initial (Observed compiler input initial) := by
  cases compiler with
  | defaultGCC => exact gcc_generated_vc input initial pre
  | defaultClang => exact clang_generated_vc input initial pre

theorem executes (compiler : Compiler) (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes compiler) input initial)
    (choices : ChoiceStream FlagChoices) :
    ∃ result, runWith choices (retired compiler) initial = .ok result ∧
      Observed compiler input initial result ∧
      CheckedTraceWith (PureCallAllowed initial) choices initial result := by
  obtain ⟨result,actual,observed,_,trace⟩ := run_soundWith (valid compiler) pre.code
    (by simp) (generated_vc compiler input initial pre) choices
  exact ⟨result,actual,observed,trace⟩

theorem semantics (compiler : Compiler) (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec (bytes compiler) input initial) :
    AllExecutionsWith initial (Observed compiler input initial) := by
  intro choices
  obtain ⟨result,actual,observed,_⟩ := executes compiler input initial pre choices
  exact ⟨result,Engine.run_sound stepWith actual,observed⟩

theorem observations (compiler : Compiler) {input : PureCall.Invocation spec} {initial : State}
    (pre : PureCall.Pre spec (bytes compiler) input initial)
    {choices : ChoiceStream FlagChoices} {result : Result}
    (execution : ExecutesWith choices initial result) : Observed compiler input initial result := by
  obtain ⟨verified,actual,observed,_⟩ := executes compiler input initial pre choices
  have same := Engine.Executes.fixed_choices_unique stepWith execution
    (Engine.run_sound stepWith actual)
  subst verified
  exact observed

#print axioms gcc_generated_vc
#print axioms clang_generated_vc
#print axioms executes
#print axioms semantics
#print axioms observations
end EDSL.Corpus.V1.SignumBodies
#audit_edsl
