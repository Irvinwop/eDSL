/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.RotationBodies
import EDSL.Corpus.V1.RotationWindows
import EDSL.Corpus.Scalar
import EDSL.ELF.CallerResources.Stack

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.RotationBodies
open X86 X86.Sequential OS Corpus.V1

abbrev Compiler := RotationCode.Compiler
abbrev spec := RotationCode.spec
abbrev bytes := RotationCode.bytes
private abbrev caller := ELF.CallerResources.Stack.standard

private theorem fresh (compiler : Compiler) :
    ELF.fresh (RotationWindows.input compiler).table.image caller.prior = true := by
  apply ELF.CallerResources.Stack.check_sound _ 0x700008 0x654321
  cases compiler <;> decide +kernel

private theorem separate (compiler : Compiler) :
    Ownership.Disjoint ⟨(RotationWindows.input compiler).function.window.base,
      (RotationWindows.input compiler).bytes.length⟩ caller.region := by
  cases compiler
  · change Ownership.Disjoint ⟨4206048,13⟩ ⟨0x700008,8⟩
    decide +kernel
  · change Ownership.Disjoint ⟨4199248,9⟩ ⟨0x700008,8⟩
    decide +kernel

private def environment (compiler : Compiler) : CallResources.Domain.Initial :=
  Corpus.ELFResources.initial (RotationWindows.file compiler)
    (RotationWindows.input compiler) caller

private theorem environment_facts (compiler : Compiler) :
    CallResources.Domain.Facts (environment compiler) :=
  Corpus.ELFResources.initial_facts (RotationWindows.checked compiler) (fresh compiler)
    ELF.CallerResources.Stack.standard_facts (separate compiler)

private def resource (compiler : Compiler) (value : Word × BitVec 32) : PureCall.Resources spec :=
  Corpus.Scalar.resource (environment compiler) spec value

private theorem resource_value (compiler : Compiler) (value : Word × BitVec 32) :
    (PureCall.resourceInput (resource compiler value)).value = value := rfl

private def initial (compiler : Compiler) (value : Word × BitVec 32) : State :=
  Corpus.Scalar.initial (environment compiler) spec value

private theorem pre (compiler : Compiler) (value : Word × BitVec 32) :
    PureCall.ResourcePre spec (bytes compiler) (resource compiler value) (initial compiler value) :=
  Corpus.Scalar.resource_pre (environment_facts compiler) spec value rfl trivial

/-- All high RSI bits and all incoming flags are independently arbitrary.
The unrelated canary registers include old RAX and RCX, catching omitted or
misordered MOVs when the actual decoded program is used. -/
private def dirty (compiler : Compiler) (value : Word × BitVec 32)
    (high : BitVec 32) (flags : Word) : State :=
  { initial compiler value with
    registers := fun register =>
      if register = .rdi ∨ register = .rsp then (initial compiler value).registers register
      else if register = .rsi then high ++ value.2 else 0xfedcba9876543210
    flags := flags }

private theorem dirty_pre (compiler : Compiler) (value : Word × BitVec 32)
    (high : BitVec 32) (flags : Word) :
    PureCall.ResourcePre spec (bytes compiler) (resource compiler value)
      (dirty compiler value high flags) := by
  have present := pre compiler value
  refine ⟨present.current.sameMemory rfl, present.code, present.entry, ?_, trivial, ?_⟩
  · exact present.stack
  · apply (Arithmetic64.rotateLeft_bound_iff value _).mpr
    have bound := (Arithmetic64.rotateLeft_bound_iff value _).mp present.arguments
    exact ⟨bound.1, BitVec.setWidth_append_eq_right⟩

/-- Independent literal wraparound result on actual full frozen windows,
including dirty unbound registers, arbitrary upper RSI/flags and all independent
OF choices. Return/frame/accounting follow from the shared production engine. -/
theorem dirty_wraparound (compiler : Compiler) (high : BitVec 32)
    (flags : Word) (choices : Choices) :
    ∃ result, Sequential.run choices (Corpus.V1.RotationBodies.retired compiler)
        (dirty compiler (0x8123456789abcdef,4) high flags) = .ok result ∧
      result.state.registers .rax = 0x123456789abcdef8 ∧
      result.state.rip = caller.returnAddress ∧
      result.state.registers .rsp = caller.stack + 8 ∧
      result.reads = [⟨.stack,caller.stack,8⟩] ∧
      PureCall.ScratchFrame (.rsp :: Corpus.V1.RotationBodies.scratch)
        (dirty compiler (0x8123456789abcdef,4) high flags) result.state := by
  have present := (dirty_pre compiler (0x8123456789abcdef,4) high flags).machine
  obtain ⟨result, actual, observed, _⟩ := Corpus.V1.RotationBodies.executes compiler _ _ present choices
  refine ⟨result,actual,?_,observed.1.returnAddress,observed.1.stackPointer,
    observed.2.2.2.1,observed.2.1⟩
  have literal : WordMath.IsRotateLeft64 (0x8123456789abcdef : Word) 4
      (0x123456789abcdef8 : Word) :=
    (WordMath.isRotateLeft_iff_eq_rotateLeft _ _ _).mpr (by decide +kernel)
  have math := observed.1.result
  rw [resource_value] at math
  exact WordMath.isRotateLeft_unique math literal

/-- The public contract also admits the maximal uint32 count. Its low six bits
are 63, making a high-bit wraparound result distinct from a 32-bit rotation. -/
theorem maximal_count (compiler : Compiler) (high : BitVec 32)
    (flags : Word) (choices : Choices) :
    ∃ result, Sequential.run choices (Corpus.V1.RotationBodies.retired compiler)
        (dirty compiler (0x8000000000000001,0xffffffff) high flags) = .ok result ∧
      result.state.registers .rax = 0xc000000000000000 := by
  have present := (dirty_pre compiler (0x8000000000000001,0xffffffff) high flags).machine
  obtain ⟨result,actual,observed,_⟩ := Corpus.V1.RotationBodies.executes compiler _ _ present choices
  have literal : WordMath.IsRotateLeft64 (0x8000000000000001 : Word) 0xffffffff
      (0xc000000000000000 : Word) :=
    (WordMath.isRotateLeft_iff_eq_rotateLeft _ _ _).mpr (by decide +kernel)
  have math := observed.1.result
  rw [resource_value] at math
  exact ⟨result,actual,WordMath.isRotateLeft_unique math literal⟩

/-- A multiple of 64 must preserve the COMPLETE flags word, despite dirty
incoming flags and both independently quantified neutral schedule outcomes. -/
theorem zero_count_preserves_all_flags (compiler : Compiler) (high : BitVec 32)
    (flags : Word) (choices : Choices) :
    ∃ result, Sequential.run choices (Corpus.V1.RotationBodies.retired compiler)
        (dirty compiler (0x8000000000000001,128) high flags) = .ok result ∧
      result.state.registers .rax = 0x8000000000000001 ∧ result.state.flags = flags := by
  have present := (dirty_pre compiler (0x8000000000000001,128) high flags).machine
  obtain ⟨result,actual,observed,_⟩ := Corpus.V1.RotationBodies.executes compiler _ _ present choices
  have literal : WordMath.IsRotateLeft64 (0x8000000000000001 : Word) 128
      (0x8000000000000001 : Word) :=
    (WordMath.isRotateLeft_iff_eq_rotateLeft _ _ _).mpr (by decide +kernel)
  have math := observed.1.result
  rw [resource_value] at math
  refine ⟨result,actual,WordMath.isRotateLeft_unique math literal,?_⟩
  have rules := observed.2.2.2.2
  rw [resource_value] at rules
  exact rules

/-- A count of 65 is effectively one: OF must be the defined XOR of the
result boundary bits, independently of the supplied neutral schedule. -/
theorem one_count_defines_overflow (compiler : Compiler) (high : BitVec 32)
    (flags : Word) (choices : Choices) :
    ∃ result, Sequential.run choices (Corpus.V1.RotationBodies.retired compiler)
        (dirty compiler (0x8000000000000001,65) high flags) = .ok result ∧
      result.state.registers .rax = 3 ∧ result.state.flags.getLsbD 11 = true := by
  have present := (dirty_pre compiler (0x8000000000000001,65) high flags).machine
  obtain ⟨result,actual,observed,_⟩ := Corpus.V1.RotationBodies.executes compiler _ _ present choices
  have literal : WordMath.IsRotateLeft64 (0x8000000000000001 : Word) 65 (3 : Word) :=
    (WordMath.isRotateLeft_iff_eq_rotateLeft _ _ _).mpr (by decide +kernel)
  have math := observed.1.result
  rw [resource_value] at math
  have correct : result.state.registers .rax = 3 := WordMath.isRotateLeft_unique math literal
  refine ⟨result,actual,correct,?_⟩
  have rules := observed.2.2.2.2
  rw [resource_value] at rules
  change RolFlags64Admissible flags (result.state.registers .rax) 1 result.state.flags at rules
  have defined := rules.2.2 rfl
  simpa [correct] using defined

/-- Every prefix retains the SAME current caller/code loans and original
return-slot permission, even with dirty registers, flags and high argument bits.
This exercises the shared resource bridge rather than a client OS model. -/
theorem current_resources (compiler : Compiler) (value : Word × BitVec 32)
    (high : BitVec 32) (flags : Word) :
    Grading.ReadOnlyPolicy (dirty compiler value high flags)
      (CallResources.Current (resource compiler value).call (resource compiler value).shared)
      (fun _ read => CallResources.ReadAllowed (resource compiler value).call
        (resource compiler value).shared read) :=
  ((Corpus.V1.RotationBodies.semantics compiler).resource _ _
    (dirty_pre compiler value high flags)).2

#print axioms dirty_wraparound
#print axioms maximal_count
#print axioms zero_count_preserves_all_flags
#print axioms one_count_defines_overflow
#print axioms current_resources
end EDSL.Tests.RotationBodies
#audit_edsl
