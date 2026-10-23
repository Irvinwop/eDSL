/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.MultiplyBodies
import EDSL.Corpus.V1.MultiplyWindows
import EDSL.Corpus.ELFResources
import EDSL.ELF.CallerResources.Stack
import EDSL.PureCall.Domain
import EDSL.PureCall.ELFCertificate
import EDSL.X86.VCGen.ChoicesPureCall

set_option autoImplicit false
set_option warningAsError true

/-! Universal vector/resource semantics and present loaded witnesses for the
unchanged frozen `c_mul_mod64` functions. No registration or certificate is
constructed. Native authority, CPU/Linux correspondence and compiler/source
preservation remain external obligations of the sequential target model. -/

namespace EDSL.Corpus.V1.MultiplyResources
open X86 X86.Sequential OS

abbrev Compiler := MultiplyCode.Compiler
abbrev spec := MultiplyCode.spec
abbrev bytes := MultiplyCode.bytes
abbrev file := MultiplyWindows.file
abbrev name := MultiplyWindows.name
abbrev input := MultiplyWindows.input
abbrev caller := ELF.CallerResources.Stack.standard

/-- The shared vector VCG/resource bridge retains both original universal
admission domains, full64 output, complete memory, callee-saved registers and
nonarithmetic flags. The same supplied code/caller authority holds at every
actual continuing prefix and at return, for every complete flag vector stream.
Retirement/read observations remain in `MultiplyBodies.Observed`; they impose
no instruction-count or trace restriction on admission. -/
theorem semantics (compiler : Compiler) :
    Grading.ReadOnlySemanticClaimFor .flags (PureCall.readOnlyTask spec) (bytes compiler) :=
  X86.VCGen.pureCall_semantics_of_generatedWith spec (bytes compiler)
    (MultiplyBodies.graph compiler) (MultiplyBodies.valid compiler)
    (MultiplyBodies.entry compiler) (MultiplyBodies.entry_offset compiler)
    (MultiplyBodies.retired compiler) (MultiplyBodies.Observed compiler)
    (fun _ _ _ evidence => evidence.1) (MultiplyBodies.generated_vc compiler)

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

/-- Admission uses the existing complete-file/name/window checker and fresh
installation into the original caller mappings, with no execution premise. -/
theorem admitted (compiler : Compiler) :
    (input compiler).admit (file compiler) name caller.prior = .ok (installed compiler) :=
  ELFResources.admitted (MultiplyWindows.checked compiler) (fresh compiler)

def environment (compiler : Compiler) : CallResources.Domain.Initial :=
  ELFResources.initial (file compiler) (input compiler) caller

theorem environment_facts (compiler : Compiler) :
    CallResources.Domain.Facts (environment compiler) :=
  ELFResources.initial_facts (MultiplyWindows.checked compiler) (fresh compiler)
    ELF.CallerResources.Stack.standard_facts (separate compiler)

/-- All full64 pairs share the actual installed ELF memory and selected entry.
The shared domain declares a new modeled ownership world; it authenticates no
native authority. Usefulness and future outcomes are absent from admission. -/
def resource (compiler : Compiler) (value : Word × Word) : PureCall.Resources spec :=
  PureCall.Domain.resource (environment compiler) spec value

def initial (compiler : Compiler) (value : Word × Word) : State :=
  PureCall.Domain.initial (environment compiler) spec value

theorem pre (compiler : Compiler) (value : Word × Word) :
    PureCall.ResourcePre spec (bytes compiler)
      (resource compiler value) (initial compiler value) :=
  PureCall.Domain.resource_pre (environment_facts compiler) spec value rfl
    (MultiplyCode.domain value)

theorem initial_entry (compiler : Compiler) (value : Word × Word) :
    (initial compiler value).rip = (input compiler).function.window.base := rfl

theorem text (compiler : Compiler) (value : Word × Word) :
    ELF.FunctionWindow.TextUnchanged (AddressSpace.toMemory (installed compiler).space)
      (initial compiler value).memory (input compiler).function.window
      (input compiler).bytes.length := by
  intro _ _
  exact ⟨rfl, rfl⟩

/-- The neutral loaded-call record ties admission, resources, current text and
entry to this same selected function in the complete frozen artifact. This
uses no Bool semantic-claim or certificate constructor. -/
def loadedCall (compiler : Compiler) (value : Word × Word) :
    PureCall.ELFLoadedCall spec (file compiler) name (input compiler) where
  prior := caller.prior
  loaded := installed compiler
  admitted := admitted compiler
  resource := resource compiler value
  initial := initial compiler value
  pre := pre compiler value
  entry := initial_entry compiler value
  text := text compiler value

/-- Executable bytes at the actual selected address follow from the admitted
installation and retained text, rather than a separate copied-byte mapping. -/
theorem initial_code (compiler : Compiler) (value : Word × Word) :
    CodeAt (initial compiler value).memory (initial compiler value).rip (bytes compiler) :=
  (loadedCall compiler value).code

/-- Nonzero unsigned operands with an unbounded natural product above 2^64.
This selects an existential witness without narrowing the all-pairs domain. -/
def usefulValue : Word × Word := (0xffffffffffffffff, 2)

theorem useful_value : spec.useful usefulValue := by
  change (0xffffffffffffffff : Word) ≠ 0 ∧ (2 : Word) ≠ 0 ∧
    2^64 ≤ (0xffffffffffffffff : Word).toNat * (2 : Word).toNat
  decide +kernel

/-- Both compiler selections have a useful loaded resource at their own
selected address. All premises describe present bytes/resources/arguments. -/
theorem useful_loaded (compiler : Compiler) :
    ∃ call : PureCall.ELFLoadedCall spec (file compiler) name (input compiler),
      spec.useful call.resource.value ∧
      CodeAt call.initial.memory call.initial.rip (bytes compiler) :=
  ⟨loadedCall compiler usefulValue, useful_value, initial_code compiler usefulValue⟩

/-- The unchanged raw and resource domains are both usefully inhabited. This
model-independent admission statement supplies no registry or score claim. -/
theorem nonvacuous (compiler : Compiler) :
    Grading.ReadOnlyNonvacuous (PureCall.readOnlyTask spec) (bytes compiler) :=
  PureCall.nonvacuous_of_resource (resource compiler usefulValue)
    (initial compiler usefulValue) useful_value (pre compiler usefulValue)

/-- Every admitted resource/state, including callers other than the witness,
has the original postcondition and current resources at return. At every
actual continuing prefix the policy retains the original code/caller world
and permits reads only through its original caller authority. Complete RAM
is stable, with no asynchronous interference; the callable target assumes
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

#print axioms semantics
#print axioms admitted
#print axioms environment_facts
#print axioms pre
#print axioms initial_code
#print axioms useful_value
#print axioms useful_loaded
#print axioms nonvacuous
#print axioms resource_semantics
#print axioms executes
end EDSL.Corpus.V1.MultiplyResources
#audit_edsl
