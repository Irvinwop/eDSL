/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.SignumBodies
import EDSL.Corpus.V1.SignumWindows
import EDSL.Corpus.ELFResources
import EDSL.ELF.CallerResources.Stack
import EDSL.PureCall.Domain
import EDSL.PureCall.ELFCertificate
import EDSL.X86.VCGen.ChoicesPureCall
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-! Universal vector/resource semantics and present loaded witnesses for the
unchanged frozen `c_sign_i32` functions. The independent contract admits every
signed low32 input. Native authority, CPU/Linux correspondence and compiler/
source preservation remain external obligations of the sequential target. -/

namespace EDSL.Corpus.V1.SignumResources
open X86 X86.Sequential OS

abbrev Compiler := SignumCode.Compiler
abbrev spec := SignumCode.spec
abbrev bytes := SignumCode.bytes
abbrev file := SignumWindows.file
abbrev name := SignumWindows.name
abbrev input := SignumWindows.input
abbrev caller := ELF.CallerResources.Stack.standard

/-- The standard vector VCG/resource bridge retains both universal admission
domains, signed low32 output, complete memory, callee-saved registers and
nonarithmetic flags. The same supplied code/caller authority holds at every
actual continuing prefix and at return, for every complete flag vector stream.
Retirement/read observations remain separate in `SignumBodies.Observed` and
place no instruction-count or trace restriction on admission. -/
theorem semantics (compiler : Compiler) :
    Grading.ReadOnlySemanticClaimFor .flags (PureCall.readOnlyTask spec) (bytes compiler) :=
  X86.VCGen.pureCall_semantics_of_generatedWith spec (bytes compiler)
    (SignumBodies.graph compiler) (SignumBodies.valid compiler)
    (SignumBodies.entry compiler) (SignumBodies.entry_offset compiler)
    (SignumBodies.retired compiler) (SignumBodies.Observed compiler)
    (fun _ _ _ evidence => evidence.1) (SignumBodies.generated_vc compiler)

/-- The standard caller slot is outside every rounded LOAD-page interval. -/
theorem fresh (compiler : Compiler) :
    ELF.fresh (input compiler).table.image caller.prior = true := by
  apply ELF.CallerResources.Stack.check_sound _ 0x700008 0x654321
  cases compiler <;> decide +kernel

theorem separate (compiler : Compiler) :
    Ownership.Disjoint ⟨(input compiler).function.window.base,
      (input compiler).bytes.length⟩ caller.region := by
  cases compiler <;> decide +kernel

def installed (compiler : Compiler) : ELF.Loaded :=
  ELFResources.loaded (file compiler) (input compiler) caller

/-- Admission reuses the complete-file/name/window checker and fresh
installation into the original caller mappings, with no execution premise. -/
theorem admitted (compiler : Compiler) :
    (input compiler).admit (file compiler) name caller.prior = .ok (installed compiler) :=
  ELFResources.admitted (SignumWindows.checked compiler) (fresh compiler)

def environment (compiler : Compiler) : CallResources.Domain.Initial :=
  ELFResources.initial (file compiler) (input compiler) caller

theorem environment_facts (compiler : Compiler) :
    CallResources.Domain.Facts (environment compiler) :=
  ELFResources.initial_facts (SignumWindows.checked compiler) (fresh compiler)
    ELF.CallerResources.Stack.standard_facts (separate compiler)

/-- All low32 inputs share the actual installed ELF memory and selected entry.
This declares a new modeled ownership world; it authenticates no native
authority. Neither usefulness nor future outcomes are admission premises. -/
def resource (compiler : Compiler) (value : BitVec 32) : PureCall.Resources spec :=
  PureCall.Domain.resource (environment compiler) spec value

def initial (compiler : Compiler) (value : BitVec 32) : State :=
  PureCall.Domain.initial (environment compiler) spec value

theorem pre (compiler : Compiler) (value : BitVec 32) :
    PureCall.ResourcePre spec (bytes compiler)
      (resource compiler value) (initial compiler value) :=
  PureCall.Domain.resource_pre (environment_facts compiler) spec value rfl
    (SignumCode.domain value)

theorem initial_entry (compiler : Compiler) (value : BitVec 32) :
    (initial compiler value).rip = (input compiler).function.window.base := rfl

theorem text (compiler : Compiler) (value : BitVec 32) :
    ELF.FunctionWindow.TextUnchanged (AddressSpace.toMemory (installed compiler).space)
      (initial compiler value).memory (input compiler).function.window
      (input compiler).bytes.length := by
  intro _ _
  exact ⟨rfl, rfl⟩

/-- Admission, current resources, text and entry refer to the same selected
function in the complete shared frozen artifact. -/
def loadedCall (compiler : Compiler) (value : BitVec 32) :
    PureCall.ELFLoadedCall spec (file compiler) name (input compiler) where
  prior := caller.prior
  loaded := installed compiler
  admitted := admitted compiler
  resource := resource compiler value
  initial := initial compiler value
  pre := pre compiler value
  entry := initial_entry compiler value
  text := text compiler value

/-- Executable bytes at the selected address follow from the admitted
installation and retained text, without a separate copied-byte mapping. -/
theorem initial_code (compiler : Compiler) (value : BitVec 32) :
    CodeAt (initial compiler value).memory (initial compiler value).rip (bytes compiler) :=
  (loadedCall compiler value).code

/-- Bind the independently supplied argument through the actual installed
constructor. This checks its RDI bits rather than trusting its value field. -/
theorem initial_binding (compiler : Compiler) (value : BitVec 32) :
    ((loadedCall compiler value).initial.registers .rdi).setWidth 32 = value := by
  change (value.setWidth 64).setWidth 32 = value
  rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
  exact BitVec.setWidth_eq value

/-- The signed minimum changes from -2147483648 to -1 under signum. This
selects an existential witness without narrowing the all-inputs domain. -/
def usefulValue : BitVec 32 := BitVec.intMin 32

theorem useful_value : spec.useful usefulValue := by
  change (BitVec.intMin 32).toInt < -1 ∨ 1 < (BitVec.intMin 32).toInt
  rw [WordMath.intMin32_toInt]
  decide +kernel

/-- Usefulness means that a correct result changes the mathematical value. -/
theorem useful_changes (value : BitVec 32) (output : Word)
    (useful : spec.useful value) (satisfies : spec.result value output) :
    (output.setWidth 32).toInt ≠ value.toInt := by
  intro same
  exact Scalar32.signum_useful_changes value output useful satisfies
    (BitVec.eq_of_toInt_eq same)

/-- Each compiler selection has a useful loaded resource at its own selected
address. All premises describe present bytes, resources and arguments. -/
theorem useful_loaded (compiler : Compiler) :
    ∃ call : PureCall.ELFLoadedCall spec (file compiler) name (input compiler),
      spec.useful call.resource.value ∧
      CodeAt call.initial.memory call.initial.rip (bytes compiler) :=
  ⟨loadedCall compiler usefulValue, useful_value, initial_code compiler usefulValue⟩

/-- The unchanged raw and resource domains are both usefully inhabited. -/
theorem nonvacuous (compiler : Compiler) :
    Grading.ReadOnlyNonvacuous (PureCall.readOnlyTask spec) (bytes compiler) :=
  PureCall.nonvacuous_of_resource (resource compiler usefulValue)
    (initial compiler usefulValue) useful_value (pre compiler usefulValue)

/-- Every admitted resource/state has the original postcondition and current
resources at return. At every actual continuing prefix the policy retains
the original code/caller world and original caller read authority. Complete
RAM is stable, with no asynchronous interference. The callable target assumes
alignment checking disabled, four-level canonical addresses and CET/IBT/shadow
stacks disabled. Native loading/authority and CPU/OS refinement remain open. -/
theorem resource_semantics (compiler : Compiler) (resource : PureCall.Resources spec)
    (initial : State) (pre : PureCall.ResourcePre spec (bytes compiler) resource initial) :
    AllExecutionsWith initial (fun result =>
      PureCall.Post spec (PureCall.resourceInput resource) initial result.state ∧
      CallResources.Current resource.call resource.shared result.state) ∧
    Grading.ReadOnlyPolicyFor .flags initial
      (CallResources.Current resource.call resource.shared)
      (fun _ read => CallResources.ReadAllowed resource.call resource.shared read) :=
  (semantics compiler).resource resource initial pre

/-- A returning production vector execution for each stream and every admitted
resource. Neither usefulness nor a modeled instruction count is an input. -/
theorem executes (compiler : Compiler) {resource : PureCall.Resources spec} {initial : State}
    (pre : PureCall.ResourcePre spec (bytes compiler) resource initial)
    (choices : ChoiceStream FlagChoices) :
    ∃ result, ExecutesWith choices initial result ∧
      PureCall.Post spec (PureCall.resourceInput resource) initial result.state ∧
      CallResources.Current resource.call resource.shared result.state :=
  (resource_semantics compiler resource initial pre).1 choices

/-- Every independently supplied low32 value reaches the mathematical signum
contract through this installed caller constructor, for every flag stream.
The result retains the entire installed memory, returns to the original caller,
advances its RSP by eight and retains its original current resources. Arbitrary
admitted prestates and upper RDI halves are covered separately by `semantics`.
The argument equality is derived from actual RDI binding in the proof, so a
constructor that ignores the supplied value cannot discharge this theorem. -/
theorem allInputsResult (compiler : Compiler) (value : BitVec 32) :
    AllExecutionsWith (loadedCall compiler value).initial (fun result =>
      WordMath.Signum value.toInt ((result.state.registers .rax).setWidth 32).toInt ∧
      result.state.memory = AddressSpace.toMemory (installed compiler).space ∧
      result.state.rip = caller.returnAddress ∧
      result.state.registers .rsp = caller.stack + 8 ∧
      CallResources.Current (loadedCall compiler value).resource.call
        (loadedCall compiler value).resource.shared result.state) := by
  let call := loadedCall compiler value
  have supplied : (call.initial.registers .rdi).setWidth 32 = value :=
    initial_binding compiler value
  have argument : (call.initial.registers .rdi).setWidth 32 = call.resource.value :=
    (SignumCode.bound_iff call.resource.value call.initial).mp call.pre.arguments
  have bound : call.resource.value = value := argument.symm.trans supplied
  intro choices
  obtain ⟨result, execution, post, current⟩ := executes compiler call.pre choices
  have correct : WordMath.Signum call.resource.value.toInt
      ((result.state.registers .rax).setWidth 32).toInt :=
    SignumCode.post_result post
  rw [bound] at correct
  exact ⟨result, execution, correct, post.memory, post.returnAddress, post.stackPointer, current⟩

#print axioms semantics
#print axioms admitted
#print axioms environment_facts
#print axioms pre
#print axioms initial_code
#print axioms initial_binding
#print axioms useful_value
#print axioms useful_changes
#print axioms useful_loaded
#print axioms nonvacuous
#print axioms resource_semantics
#print axioms executes
#print axioms allInputsResult
end EDSL.Corpus.V1.SignumResources
#audit_edsl
