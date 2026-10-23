/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.SignumRegistered
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Stored acceptance assertions for the two original named signum artifacts.
These declarations retain the complete files, independent mathematical task,
actual installed caller input, universal vector semantics and resource policy.
They establish no corpus score, native authority or CPU/Linux correspondence.
-/

namespace EDSL.Tests.SignumCertificates
open X86 X86.Sequential OS Corpus.V1

/-- The exact complete frozen GCC file and literal requested byte name index
this certificate. An extracted body or another named function has a different type. -/
def gcc : Corpus.CertificateFor .signumSigned32 (FrozenFunction.file .defaultGCC)
    [99,95,115,105,103,110,95,105,51,50] :=
  SignumRegistered.certificate .defaultGCC

/-- Clang's distinct complete file uses the same independent registered task. -/
def clang : Corpus.CertificateFor .signumSigned32 (FrozenFunction.file .defaultClang)
    [99,95,115,105,103,110,95,105,51,50] :=
  SignumRegistered.certificate .defaultClang

/-- Both original full-file/name certificate obligations are inhabited. -/
theorem files :
    Nonempty (Corpus.CertificateFor .signumSigned32 (FrozenFunction.file .defaultGCC)
      [99,95,115,105,103,110,95,105,51,50]) ∧
    Nonempty (Corpus.CertificateFor .signumSigned32 (FrozenFunction.file .defaultClang)
      [99,95,115,105,103,110,95,105,51,50]) :=
  ⟨⟨gcc⟩,⟨clang⟩⟩

/-- Registration fixes the entire mathematical/resource task and full-vector
executor together, rather than merely checking the result predicate's name. -/
theorem registration : Grading.registry .signumSigned32 =
    ⟨.flags, Grading.ofReadOnlyFor .flags (PureCall.readOnlyTask Scalar32.signumSigned)⟩ :=
  SignumRegistered.registration

/-- The registered claim retains both universal admission domains and their
separate useful witnesses for each exact original instruction sequence. -/
theorem claim (compiler : SignumCode.Compiler) :
    Grading.RegisteredClaim .signumSigned32 (SignumCode.bytes compiler) :=
  SignumRegistered.claim compiler

/-- Useful-domain inhabitation is separate from universal correctness; zero,
one, minus one and every other low32 input remain in the raw/resource domains. -/
theorem nonvacuous (compiler : SignumCode.Compiler) :
    Grading.ReadOnlyNonvacuous (PureCall.readOnlyTask Scalar32.signumSigned)
      (SignumCode.bytes compiler) :=
  SignumResources.nonvacuous compiler

/-- The actual selected-address installed constructor binds the independently
supplied value to RDI's low32 bits, rather than only storing it in a resource field. -/
theorem initial_binding (compiler : SignumCode.Compiler) (value : BitVec 32) :
    ((SignumResources.loadedCall compiler value).initial.registers .rdi).setWidth 32 = value :=
  SignumResources.initial_binding compiler value

/-- Every supplied low32 value satisfies the independent integer-order relation
through that actual installed call, with the original memory, caller and resources. -/
theorem allInputsResult (compiler : SignumCode.Compiler) (value : BitVec 32) :
    AllExecutionsWith (SignumResources.loadedCall compiler value).initial (fun result =>
      WordMath.Signum value.toInt ((result.state.registers .rax).setWidth 32).toInt ∧
      result.state.memory = AddressSpace.toMemory (SignumResources.installed compiler).space ∧
      result.state.rip = SignumResources.caller.returnAddress ∧
      result.state.registers .rsp = SignumResources.caller.stack + 8 ∧
      CallResources.Current (SignumResources.loadedCall compiler value).resource.call
        (SignumResources.loadedCall compiler value).resource.shared result.state) :=
  SignumResources.allInputsResult compiler value

/-- Arbitrary admitted prestates, including arbitrary RDI high32 bits, retain
the complete postcondition and current authority at return and at every prefix. -/
theorem resources (compiler : SignumCode.Compiler)
    (resource : PureCall.Resources Scalar32.signumSigned) (initial : State)
    (pre : PureCall.ResourcePre Scalar32.signumSigned (SignumCode.bytes compiler)
      resource initial) :
    AllExecutionsWith initial (fun result =>
      PureCall.Post Scalar32.signumSigned (PureCall.resourceInput resource) initial result.state ∧
      CallResources.Current resource.call resource.shared result.state) ∧
    Grading.ReadOnlyPolicyFor .flags initial
      (CallResources.Current resource.call resource.shared)
      (fun _ read => CallResources.ReadAllowed resource.call resource.shared read) :=
  SignumResources.resource_semantics compiler resource initial pre

/-- Stronger raw observations cover every admitted input and flag stream:
full memory/nonarithmetic flags, nonscratch registers, exactly seven modeled
instructions including RET, the sole original STACK8 read and full64 RAX zero extension. -/
theorem observations (compiler : SignumCode.Compiler)
    (input : PureCall.Invocation Scalar32.signumSigned) (initial : State)
    (pre : PureCall.Pre Scalar32.signumSigned (SignumCode.bytes compiler) input initial) :
    AllExecutionsWith initial (fun result =>
      PureCall.Post Scalar32.signumSigned input initial result.state ∧
      PureCall.ScratchFrame (.rsp :: SignumBodies.scratch compiler) initial result.state ∧
      result.instructions = 7 ∧ result.reads = [⟨.stack,initial.registers .rsp,8⟩] ∧
      (result.state.registers .rax).toNat < 2^32) :=
  SignumBodies.semantics compiler input initial pre

/-- Correct file, selected row and code do not authenticate another requested
name. A checker that ignores the requested byte name would violate this assertion. -/
theorem wrong_name_rejected (compiler : SignumCode.Compiler) :
    (SignumWindows.input compiler).check (FrozenFunction.file compiler)
      [0x6f,0x74,0x68,0x65,0x72] = false := by
  cases accepted : (SignumWindows.input compiler).check (FrozenFunction.file compiler)
      [0x6f,0x74,0x68,0x65,0x72] with
  | false => rfl
  | true =>
    have contract := (ELF.FunctionSymbol.checked_sound accepted).2.1
    have absent : (SignumWindows.input compiler).metadata.matches
        [0x6f,0x74,0x68,0x65,0x72] = [] := by
      cases compiler <;> decide +kernel
    have unique := contract.2.2.1
    rw [absent] at unique
    cases unique

/-- The authentic executable prefix without RET cannot replace the complete
named symbol extent, even though all of its retained bytes are original. -/
theorem short_extent_rejected (compiler : SignumCode.Compiler) :
    ({ SignumWindows.input compiler with bytes := (SignumCode.bytes compiler).dropLast } :
      ELF.FunctionInput).check (FrozenFunction.file compiler) SignumWindows.name = false := by
  cases accepted :
      ({ SignumWindows.input compiler with bytes := (SignumCode.bytes compiler).dropLast } :
        ELF.FunctionInput).check (FrozenFunction.file compiler) SignumWindows.name with
  | false => rfl
  | true =>
    have original := (ELF.FunctionSymbol.checked_mapping (SignumWindows.checked compiler)).2.1
    have wrong := (ELF.FunctionSymbol.checked_mapping accepted).2.1
    have different : (SignumCode.bytes compiler).dropLast.length ≠
        (SignumCode.bytes compiler).length := by
      cases compiler <;> decide +kernel
    exact False.elim (different (wrong.symm.trans original))

/-- A same-length RET-to-NOP mutation cannot borrow the original complete-file
binding. Metadata, name and length alone are insufficient to establish byte identity. -/
theorem changed_ret_rejected (compiler : SignumCode.Compiler) :
    ({ SignumWindows.input compiler with
      bytes := (SignumCode.bytes compiler).set ((SignumCode.bytes compiler).length - 1) 0x90 } :
      ELF.FunctionInput).check (FrozenFunction.file compiler) SignumWindows.name = false := by
  cases accepted :
      ({ SignumWindows.input compiler with
        bytes := (SignumCode.bytes compiler).set ((SignumCode.bytes compiler).length - 1) 0x90 } :
        ELF.FunctionInput).check (FrozenFunction.file compiler) SignumWindows.name with
  | false => rfl
  | true =>
    have original := (ELF.FunctionSymbol.checked_sound (SignumWindows.checked compiler)).2.2.2.source
    have changed := (ELF.FunctionSymbol.checked_sound accepted).2.2.2.source
    change ((FrozenFunction.file compiler).drop (SignumWindows.function compiler).window.offset).take
      (SignumCode.bytes compiler).length = SignumCode.bytes compiler at original
    change ((FrozenFunction.file compiler).drop (SignumWindows.function compiler).window.offset).take
      ((SignumCode.bytes compiler).set ((SignumCode.bytes compiler).length - 1) 0x90).length = _
      at changed
    rw [List.length_set, original] at changed
    have last := congrArg List.getLast? changed
    have different : (SignumCode.bytes compiler).getLast? ≠
        ((SignumCode.bytes compiler).set ((SignumCode.bytes compiler).length - 1) 0x90).getLast? := by
      cases compiler <;> decide +kernel
    exact False.elim (different last)

#print axioms files
#print axioms registration
#print axioms claim
#print axioms nonvacuous
#print axioms initial_binding
#print axioms allInputsResult
#print axioms resources
#print axioms observations
#print axioms wrong_name_rejected
#print axioms short_extent_rejected
#print axioms changed_ret_rejected
end EDSL.Tests.SignumCertificates
#audit_edsl
