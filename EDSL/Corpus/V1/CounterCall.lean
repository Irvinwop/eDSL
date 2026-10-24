/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterMixedGraphs
import EDSL.OS.TSO64.EffectSimulation.Mixed.Authority
import EDSL.OS.TSO64.EffectSimulation.Mixed.CallerOnly
import EDSL.PureCall.Contract
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Shared current call data for the complete frozen counter workers. The site
fixes the compiler's original byte window, graph, caps and absolute symbol
address. Admission separately requires actual current code, resources and the
protected caller word. The argument count binds only low32 RSI; upper bits,
initial flags and a well-formed incoming FIFO remain unrestricted.

The current selector is the scheduler's first matching authorized handle at
the independently named address, linked to the independently named target.
Its actor is the original resource actor, with no equality to scheduler tid
assumed. Idle transport preserves the saved context and metadata selection,
without freezing current RAM or the pending FIFO.

Imported long-mode/CET-off, coherent scalar WB RAM, translation/no-alias and
protected-resource assumptions remain. These definitions add no execution,
count, return, progress, hardware/compiler refinement or corpus-credit claim.
No RAX result, post-stack nonwrapping/canonicality, or no-other-writes contract
is asserted here.
-/

namespace EDSL.Corpus.V1.CounterCommon
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation

abbrev Compiler := CounterMixedGraphs.Compiler

/-- The frozen symbol address, rather than an independently chosen rebase. -/
def base (compiler : Compiler) : Word :=
  BitVec.ofNat 64 (CounterMixedGraphs.function compiler).window.address

/-- Independent pointer, uint32 iteration count, atomic object and caller. -/
structure Call where
  address : Word
  iterations : BitVec 32
  target : Atomics64.CellId64
  returnAddress : Word

/-- Fixed native subject and original code-loan containment. Actual current
resource and code authenticity belong to `Mixed.Admission`. -/
structure Site (compiler : Compiler) where
  profile : Profile
  tid : Nat
  original : Worker
  codeLoan : Borrowing.Subregion
    ⟨base compiler, (CounterMixedGraphs.bytes compiler).length⟩
    original.resources.code.loan.region

/-- Reuse each complete checked mixed graph with the current caller-only
ordinary policy. The locked family remains definitionally arithmetic. -/
def descriptor {compiler : Compiler} (site : Site compiler) (call : Call) :
    Mixed.Descriptor where
  family := .arithmetic
  profile := site.profile
  tid := site.tid
  bytes := CounterMixedGraphs.bytes compiler
  base := base compiler
  graph := CounterMixedGraphs.graph compiler
  caps := CounterMixedGraphs.caps compiler
  structural := CounterMixedGraphs.structural compiler
  original := site.original
  codeLoan := site.codeLoan
  callerValue := call.returnAddress
  policy state := {
    Current _ := ResourcesValid state.world site.original.resources
    AllowedRead _ read := read.kind = .stack ∧
      read.address = site.original.resources.callerAddress ∧ read.bytes = 8
    AllowedEffect _ instruction _ := Sequential.CallerOnly instruction }

/-- Policy identity needed by the existing current ordinary-head bridge. -/
theorem descriptor_policy {compiler : Compiler} (site : Site compiler) (call : Call)
    (state : S) :
    (descriptor site call).policy state =
      Mixed.authorityCallerPolicy (descriptor site call) state := rfl

/-- Retain the actual ordered first selector and its target identity. Its
checked authority and cell address follow from `atomicFor_sound`. -/
def Selected {compiler : Compiler} (site : Site compiler) (call : Call) (state : S) : Prop :=
  ∃ identifier handle cell,
    atomicFor state.world site.original.resources call.address =
      some (identifier, handle, cell) ∧ handle.cell = call.target

/-- Void-call frame on the saved context. Arithmetic flags and RAX are free. -/
def Saved {compiler : Compiler} (site : Site compiler) (context : Context) : Prop :=
  (∀ register ∈ PureCall.calleeSaved,
    context.registers register = site.original.context.registers register) ∧
  context.flags &&& ~~~arithmeticFlagMask =
    site.original.context.flags &&& ~~~arithmeticFlagMask

/-- Admission uses only present inputs and protected resources. No schedule,
future enabledness, old-value oracle or empty-FIFO premise is included. -/
structure Pre {compiler : Compiler} (site : Site compiler) (call : Call) (state : S) : Prop where
  admitted : Mixed.Admission (descriptor site call) state
  pc : site.original.context.rip = (descriptor site call).base
  pointer : site.original.context.registers .rdi = call.address
  count : (site.original.context.registers .rsi).setWidth 32 = call.iterations
  stack : site.original.context.registers .rsp = site.original.resources.callerAddress
  callerCanonical : canonical call.returnAddress = true
  selected : Selected site call state

/-- Shared running data, independent of compiler-local loop arithmetic and
history predicates. Binding and Frame remain the existing separate assertions. -/
structure LiveData {compiler : Compiler} (site : Site compiler) (call : Call)
    (state : S) (context : Context) : Prop where
  pointer : context.registers .rdi = call.address
  stack : context.registers .rsp = site.original.resources.callerAddress
  saved : Saved site context
  selected : Selected site call state

/-- The original context satisfies its own void-call frame. -/
theorem Saved.refl {compiler : Compiler} (site : Site compiler) :
    Saved site site.original.context :=
  ⟨fun _register _member => rfl, rfl⟩

/-- Current metadata stability preserves the exact original-resource selector. -/
theorem Selected.stable {compiler : Compiler} {site : Site compiler} {call : Call}
    {before after : S} (selected : Selected site call before)
    (stable : Stable before.world after.world) : Selected site call after := by
  obtain ⟨identifier, handle, cell, chosen, target⟩ := selected
  exact ⟨identifier, handle, cell,
    (stable.atomicFor site.original.resources call.address).trans chosen, target⟩

/-- Transport metadata through an authenticated native origin; data values are
not part of this assertion. -/
theorem Selected.origin {compiler : Compiler} {site : Site compiler} {call : Call}
    {before : S} {action : Action} {result : S × O}
    (selected : Selected site call before)
    (origin : Origin before action result site.profile .arithmetic) :
    Selected site call result.1 :=
  selected.stable (origin_stable origin)

/-- Peer positions, drains and exact own blocked attempts retain selection. -/
theorem Selected.idle {compiler : Compiler} {site : Site compiler} {call : Call}
    {before after : S} {history extended : Log} (selected : Selected site call before)
    (idle : Mixed.Idle site.profile site.tid (before, history) (after, extended) .arithmetic) :
    Selected site call after :=
  selected.stable idle.stable

/-- Establish shared live data directly from current call inputs. -/
theorem Pre.liveData {compiler : Compiler} {site : Site compiler} {call : Call} {state : S}
    (pre : Pre site call state) : LiveData site call state site.original.context :=
  ⟨pre.pointer, pre.stack, Saved.refl site, pre.selected⟩

/-- Any authenticated offset-zero node binds the admitted original worker.
No future issue or compiler annotation is used. -/
theorem Pre.binding {compiler : Compiler} {site : Site compiler} {call : Call} {state : S}
    {node : (descriptor site call).graph.Index} (pre : Pre site call state)
    (offset : ((descriptor site call).graph.node node).offset = 0) :
    Mixed.Binding (descriptor site call) node state site.original := by
  refine ⟨pre.admitted.live, rfl, pre.admitted.running, ?_⟩
  simpa [offset] using pre.pc

/-- Existing saved-frame transport preserves a mixed binding and the entire
saved context at this node. Pending entries and RAM may change. -/
theorem binding_idle {d : Mixed.Descriptor} {node : d.graph.Index} {before after : S}
    {history extended : Log} {worker : Worker} (binding : Mixed.Binding d node before worker)
    (idle : Mixed.Idle d.profile d.tid (before, history) (after, extended) d.family) :
    ∃ current, Mixed.Binding d node after current ∧ current.context = worker.context := by
  obtain ⟨current, live, saved⟩ := idle.saved binding.live
  exact ⟨current,
    ⟨live, saved.resources.trans binding.resources, saved.phase.trans binding.running,
      (congrArg Context.rip saved.context).trans binding.pc⟩,
    saved.context⟩

/-- Shared data at an unchanged saved context is stable under every actual
idle extension, irrespective of the resulting FIFO or shared word. -/
theorem LiveData.idle {compiler : Compiler} {site : Site compiler} {call : Call}
    {before after : S} {history extended : Log} {context : Context}
    (data : LiveData site call before context)
    (idle : Mixed.Idle site.profile site.tid (before, history) (after, extended) .arithmetic) :
    LiveData site call after context :=
  ⟨data.pointer, data.stack, data.saved, data.selected.idle idle⟩

/-- Simultaneously recover the current bound worker and its shared live data.
Compiler-local assertions can use the returned complete-context equality. -/
theorem binding_liveData_idle {compiler : Compiler} {site : Site compiler} {call : Call}
    {node : (descriptor site call).graph.Index} {before after : S}
    {history extended : Log} {worker : Worker}
    (binding : Mixed.Binding (descriptor site call) node before worker)
    (data : LiveData site call before worker.context)
    (idle : Mixed.Idle site.profile site.tid (before, history) (after, extended) .arithmetic) :
    ∃ current, Mixed.Binding (descriptor site call) node after current ∧
      LiveData site call after current.context ∧ current.context = worker.context := by
  obtain ⟨current, currentBinding, context⟩ := binding_idle binding idle
  refine ⟨current, currentBinding, ?_, context⟩
  simpa only [context] using data.idle idle

#print axioms Compiler
#print axioms base
#print axioms Call
#print axioms Site
#print axioms descriptor
#print axioms descriptor_policy
#print axioms Selected
#print axioms Saved
#print axioms Pre
#print axioms LiveData
#print axioms Saved.refl
#print axioms Selected.stable
#print axioms Selected.origin
#print axioms Selected.idle
#print axioms Pre.liveData
#print axioms Pre.binding
#print axioms binding_idle
#print axioms LiveData.idle
#print axioms binding_liveData_idle

end EDSL.Corpus.V1.CounterCommon

#audit_edsl
