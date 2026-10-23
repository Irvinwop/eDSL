/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.UnaryBodies
import EDSL.Corpus.V1.RotationBodies
import EDSL.Corpus.V1.UnaryWindows
import EDSL.Corpus.V1.RotationWindows
import EDSL.OS.TSO64.EffectSimulation.Resumable.CallerOnly
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Reusable OS adapters for the existing frozen absSigned32 and rotateLeft64
windows, derived from their independent specifications and generated body proofs.

The common bridge fixes reference RAM to the actual admitted initial localCPU,
including any well-formed incoming FIFO. It constructs the original PureCall.Pre
from present inputs and resource admission, and passes the exported generated
WP, original graph, Bool choices and fuel to rwp_of_callerOnly_wp unchanged.

CompleteContext retains the entire reference Result evidence and equates its
complete context with the actual returned context. CallContext projects the
independent mathematical/ABI contract without asserting current RAM equality.
The reference witness's memory frame is not a frame for peer-modified RAM.

The static finite facts below check CallerOnly, guarded native Node admission
and absence of edges into cutpoints against the original graphs and bytes.
Clients supply no instruction facts, desired successor or successful future
execution. The two adapters also retain the existing frozen-window checks;
their site types select those exact ELF symbol addresses and byte extents.

These are bounded Resumable blocks with impossible cutpoint exits, not a new
evaluator or WP. Existing rwp pause/resume and historical Response/Done rules
apply. No whole-schedule termination, fairness, exact cost, corpus credit,
hardware refinement or additional target-feature support is asserted.
-/

namespace EDSL.Corpus.V1.CallerOnlyAdapters
open X86 X86.Sequential X86.VCGen
open OS OS.TSO64
open OS.TSO64.EffectSimulation
open OS.TSO64.EffectSimulation.Resumable

/-- Present resource selection. Actual authority, executable bytes and the
original caller word are separately required by Admission at the fixed state. -/
structure CallSite (bytes : List Byte) (base : Word) where
  profile : OS.TSO64.Profile
  tid : Nat
  original : Worker
  codeLoan : Borrowing.Subregion ⟨base, bytes.length⟩ original.resources.code.loan.region

/-- The policy uses current original-resource authority, exact original STACK8
identity and the production finite effect classification. It freezes no RAM. -/
def CallSite.descriptor {bytes : List Byte} {base : Word} (site : CallSite bytes base)
    (graph : CFG.Graph) (valid : CFG.Valid bytes graph) (returnAddress : Word) : Descriptor where
  profile := site.profile
  tid := site.tid
  bytes := bytes
  base := base
  graph := graph
  graphProfile := CFG.defaultProfile
  structural := CFG.Structural.Valid.ofReadOnly valid
  original := site.original
  codeLoan := site.codeLoan
  callerValue := returnAddress
  policy state :=
    { Current _ := ResourcesValid state.world site.original.resources
      AllowedRead _ read := read.kind = .stack ∧
        read.address = site.original.resources.callerAddress ∧ read.bytes = 8
      AllowedEffect _ instruction _ := Sequential.CallerOnly instruction }

/-- Original invocation assumptions, with code and caller-read success obtained
from actual Admission instead of being requested as execution assumptions. -/
structure CallInputs {bytes : List Byte} {base : Word} (site : CallSite bytes base)
    (spec : PureCall.Spec) (input : PureCall.Invocation spec) (initial : S) : Prop where
  entry : site.original.context.rip = base
  stack : site.original.context.registers .rsp = site.original.resources.callerAddress
  domain : spec.domain input.value
  arguments : PureCall.Bound spec input.value (localCPU initial site.original)
  returnCanonical : canonical input.returnAddress = true
  stackBound : (site.original.context.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : canonical (site.original.context.registers .rsp + 8) = true

theorem CallInputs.pre {bytes : List Byte} {base : Word} {site : CallSite bytes base}
    {spec : PureCall.Spec} {input : PureCall.Invocation spec} {initial : S}
    {graph : CFG.Graph} {valid : CFG.Valid bytes graph}
    (inputs : CallInputs site spec input initial)
    (admitted : Admission (site.descriptor graph valid input.returnAddress) initial) :
    PureCall.Pre spec bytes input (localCPU initial site.original) := by
  refine ⟨inputs.domain, inputs.arguments, ?_, ?_, inputs.returnCanonical,
    inputs.stackBound, inputs.postStackCanonical⟩
  · change CodeAt (localCPU initial site.original).memory site.original.context.rip bytes
    rw [inputs.entry]
    exact admitted.reference_code
  · change readWord (localCPU initial site.original).memory
      (site.original.context.registers .rsp) = .ok input.returnAddress
    rw [inputs.stack]
    exact admitted.reference_caller

theorem CallInputs.binding {bytes : List Byte} {base : Word} {site : CallSite bytes base}
    {spec : PureCall.Spec} {input : PureCall.Invocation spec} {initial : S}
    {graph : CFG.Graph} {valid : CFG.Valid bytes graph}
    (inputs : CallInputs site spec input initial)
    (admitted : Admission (site.descriptor graph valid input.returnAddress) initial)
    (entry : graph.Index) (entryOffset : (graph.node entry).offset = 0) :
    Binding (site.descriptor graph valid input.returnAddress) entry initial site.original := by
  refine ⟨admitted.live, rfl, admitted.running, ?_⟩
  change site.original.context.rip = base + BitVec.ofNat 64 (graph.node entry).offset
  simpa [entryOffset] using inputs.entry

/-- A complete generated reference result, with every context component equal
to the actual returned context. Its memory is only the reference witness's RAM. -/
def CompleteContext (Evidence : Sequential.Result → Prop) (context : Context) : Prop :=
  ∃ result, Evidence result ∧ Context.ofCPU result.state = context

/-- The mathematical result and original PureCall ABI fields on a context.
The original Post's whole-memory equality is confined to the reference proof. -/
structure CallContext (spec : PureCall.Spec) (input : PureCall.Invocation spec)
    (initial : X86.State) (context : Context) : Prop where
  result : spec.result input.value (context.registers .rax)
  returnAddress : context.rip = input.returnAddress
  stackPointer : context.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register ∈ PureCall.calleeSaved,
    context.registers register = initial.registers register
  flags : context.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem CallContext.ofPost {spec : PureCall.Spec} {input : PureCall.Invocation spec}
    {initial final : X86.State} (post : PureCall.Post spec input initial final) :
    CallContext spec input initial (Context.ofCPU final) :=
  ⟨post.result, post.returnAddress, post.stackPointer, post.preserved, post.flags⟩

/-- Static proof data only; this defines no instruction evaluator or WP. -/
structure FiniteBody (bytes : List Byte) (graph : CFG.Graph) : Prop where
  only : ∀ node : graph.Index, Sequential.CallerOnly (graph.node node).instruction
  native : ∀ node : graph.Index, AtomicMethods.Node bytes (graph.node node).offset
    (.ordinary (graph.node node).instruction)
  noCut : ∀ source destination : graph.Index,
    graph.Edge source destination → graph.cutpoint destination = false

/-- Shared initial bridge. The generated argument is a reusable source proof;
the concrete adapters below supply the exported body theorem, not a caller
hypothesis about a future execution or a desired return value. -/
theorem CallSite.lift_generated {bytes : List Byte} {base : Word} {spec : PureCall.Spec}
    (site : CallSite bytes base) (graph : CFG.Graph) (valid : CFG.Valid bytes graph)
    (finite : FiniteBody bytes graph) (entry : graph.Index)
    (entryOffset : (graph.node entry).offset = 0) (fuel : Nat)
    (Evidence : PureCall.Invocation spec → X86.State → Sequential.Result → Prop)
    (generated : ∀ input initial, PureCall.Pre spec bytes input initial →
      VCGen.wp graph initial.rip (PureCallAllowed initial) fuel entry initial (Evidence input initial))
    (input : PureCall.Invocation spec) (initial : S)
    (admitted : Admission (site.descriptor graph valid input.returnAddress) initial)
    (inputs : CallInputs site spec input initial) :
    rwp (site.descriptor graph valid input.returnAddress)
      (returnedContext (site.descriptor graph valid input.returnAddress)
        (CompleteContext (Evidence input (localCPU initial site.original))))
      (fun _ _ _ => False) fuel entry initial [] := by
  have safe : CallerOnlyGraph (site.descriptor graph valid input.returnAddress) :=
    ⟨finite.only, finite.native, valid.byteBound⟩
  have source := generated input (localCPU initial site.original) (inputs.pre admitted)
  have pc : (localCPU initial site.original).rip = base := inputs.entry
  rw [pc] at source
  apply rwp_of_callerOnly_wp (site.descriptor graph valid input.returnAddress) safe
    (localCPU initial site.original).memory (fun _ => rfl)
    admitted.reference_code admitted.reference_caller finite.noCut
    (CompleteContext (Evidence input (localCPU initial site.original)))
    (Evidence input (localCPU initial site.original)) (fun result evidence => ⟨result, evidence, rfl⟩)
    (PureCallAllowed (localCPU initial site.original)) ?_
    fuel entry initial [] site.original admitted.frame (inputs.binding admitted entry entryOffset) source
  intro before read allowed
  change read.kind = .stack ∧ read.address = site.original.resources.callerAddress ∧ read.bytes = 8
  have originalSlot := allowed.2
  change read.kind = .stack ∧
    read.address = site.original.context.registers .rsp ∧ read.bytes = 8 at originalSlot
  simpa only [inputs.stack] using originalSlot

/-- Kernel-reduced finite facts about both actual abs graphs, including the
native guarded decoder and all graph edges. No per-instruction execute cases. -/
theorem abs_finite (compiler : UnaryBodies.Compiler) :
    FiniteBody (UnaryBodies.bytes compiler .absSigned32)
      (UnaryBodies.graph compiler .absSigned32) := by
  refine ⟨?_, ?_, ?_⟩
  · cases compiler <;> decide +kernel
  · cases compiler <;> decide +kernel
  · cases compiler <;> decide +kernel

/-- The same checks use rotation's own GCC/Clang graphs and complete bytes. -/
theorem rotation_finite (compiler : RotationBodies.Compiler) :
    FiniteBody (RotationBodies.bytes compiler) (RotationBodies.graph compiler) := by
  refine ⟨?_, ?_, ?_⟩
  · cases compiler <;> decide +kernel
  · cases compiler <;> decide +kernel
  · cases compiler <;> decide +kernel

abbrev AbsSite (compiler : UnaryBodies.Compiler) :=
  CallSite (UnaryBodies.bytes compiler .absSigned32)
    (UnaryWindows.function compiler .absSigned32).window.base

abbrev RotationSite (compiler : RotationBodies.Compiler) :=
  CallSite (RotationBodies.bytes compiler) (RotationWindows.function compiler).window.base

def absDescriptor (compiler : UnaryBodies.Compiler) (site : AbsSite compiler)
    (input : PureCall.Invocation Scalar32.absoluteSigned) : Descriptor :=
  site.descriptor (UnaryBodies.graph compiler .absSigned32)
    (UnaryBodies.valid compiler .absSigned32) input.returnAddress

def rotationDescriptor (compiler : RotationBodies.Compiler) (site : RotationSite compiler)
    (input : PureCall.Invocation RotationBodies.spec) : Descriptor :=
  site.descriptor (RotationBodies.graph compiler) (RotationBodies.valid compiler) input.returnAddress

abbrev AbsResult (compiler : UnaryBodies.Compiler)
    (input : PureCall.Invocation Scalar32.absoluteSigned) (initial : X86.State) :=
  CompleteContext (UnaryBodies.Observed compiler .absSigned32 input initial)

abbrev RotationResult (compiler : RotationBodies.Compiler)
    (input : PureCall.Invocation RotationBodies.spec) (initial : X86.State) :=
  CompleteContext (RotationBodies.Observed compiler input initial)

/-- Both frozen abs windows reuse the exported generated_vc and its original
fuel, with low32 arguments, arbitrary upper RDI and the original signed domain.
The initial current code and STACK8 authority come from actual Admission. -/
theorem absSigned32 (compiler : UnaryBodies.Compiler) (site : AbsSite compiler)
    (input : PureCall.Invocation Scalar32.absoluteSigned) (initial : S)
    (admitted : Admission (absDescriptor compiler site input) initial)
    (inputs : CallInputs site Scalar32.absoluteSigned input initial) :
    (UnaryWindows.input compiler .absSigned32).check (UnaryWindows.file compiler)
        (UnaryWindows.name .absSigned32) = true ∧
      rwp (absDescriptor compiler site input)
        (returnedContext (absDescriptor compiler site input)
          (AbsResult compiler input (localCPU initial site.original)))
        (fun _ _ _ => False) (UnaryBodies.retired compiler .absSigned32)
        (UnaryBodies.entry compiler .absSigned32) initial [] := by
  refine ⟨UnaryWindows.checked compiler .absSigned32, ?_⟩
  exact site.lift_generated (UnaryBodies.graph compiler .absSigned32)
    (UnaryBodies.valid compiler .absSigned32) (abs_finite compiler)
    (UnaryBodies.entry compiler .absSigned32) (UnaryBodies.entry_offset compiler .absSigned32)
    (UnaryBodies.retired compiler .absSigned32) (UnaryBodies.Observed compiler .absSigned32)
    (UnaryBodies.generated_vc compiler .absSigned32) input initial admitted inputs

/-- Both frozen rotation windows reuse their own exported generated_vc, graph
and fuel. The full64 value, low32 count and arbitrary upper RSI are unchanged. -/
theorem rotateLeft64 (compiler : RotationBodies.Compiler) (site : RotationSite compiler)
    (input : PureCall.Invocation RotationBodies.spec) (initial : S)
    (admitted : Admission (rotationDescriptor compiler site input) initial)
    (inputs : CallInputs site RotationBodies.spec input initial) :
    (RotationWindows.input compiler).check (RotationWindows.file compiler) RotationWindows.name = true ∧
      rwp (rotationDescriptor compiler site input)
        (returnedContext (rotationDescriptor compiler site input)
          (RotationResult compiler input (localCPU initial site.original)))
        (fun _ _ _ => False) (RotationBodies.retired compiler) (RotationBodies.entry compiler)
        initial [] := by
  refine ⟨RotationWindows.checked compiler, ?_⟩
  exact site.lift_generated (RotationBodies.graph compiler) (RotationBodies.valid compiler)
    (rotation_finite compiler) (RotationBodies.entry compiler) (RotationBodies.entry_offset compiler)
    (RotationBodies.retired compiler) (RotationBodies.Observed compiler)
    (RotationBodies.generated_vc compiler) input initial admitted inputs

/-- Independent abs mathematics, actual caller RIP/RSP, callee-saved registers,
nonarithmetic flags and zero upper RAX, projected from the complete witness. -/
theorem absSigned32_context {compiler : UnaryBodies.Compiler}
    {input : PureCall.Invocation Scalar32.absoluteSigned} {initial : X86.State} {context : Context}
    (observed : AbsResult compiler input initial context) :
    CallContext Scalar32.absoluteSigned input initial context ∧
      (context.registers .rax).toNat < 2^32 := by
  obtain ⟨result, evidence, same⟩ := observed
  subst context
  exact ⟨CallContext.ofPost evidence.1, evidence.2.2.2⟩

/-- Independent rotation mathematics/ABI, every nonscratch GPR and the original
masked-count flag relation, including the source proof's independent OF choice. -/
theorem rotateLeft64_context {compiler : RotationBodies.Compiler}
    {input : PureCall.Invocation RotationBodies.spec} {initial : X86.State} {context : Context}
    (observed : RotationResult compiler input initial context) :
    CallContext RotationBodies.spec input initial context ∧
      (∀ register, register ∉ (.rsp :: RotationBodies.scratch) →
        context.registers register = initial.registers register) ∧
      RolFlags64Admissible initial.flags (context.registers .rax)
        (input.value.2.toNat % 64) context.flags := by
  obtain ⟨result, evidence, same⟩ := observed
  subst context
  exact ⟨CallContext.ofPost evidence.1, evidence.2.1.registers, evidence.2.2.2.2⟩

#print axioms CallSite.descriptor
#print axioms CallInputs.pre
#print axioms CallInputs.binding
#print axioms CallContext.ofPost
#print axioms CallSite.lift_generated
#print axioms abs_finite
#print axioms rotation_finite
#print axioms absSigned32
#print axioms rotateLeft64
#print axioms absSigned32_context
#print axioms rotateLeft64_context

end EDSL.Corpus.V1.CallerOnlyAdapters

#audit_edsl
