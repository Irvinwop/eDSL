/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Admission
import EDSL.X86.VCGen.PlainMethods.Batch
import EDSL.Audit

/-!
Proof-side admission from the independent current-only Plain64 contract into
the production plain-method engine. Static checking depends only on each
registered site's kind, complete bytes and padding. Actual registers, selected
managed references, caller continuation and FIFO/counter come from the actual
entry state. No method, cutpoint, expected reply or successful future action is
accepted by the independent precondition.

This bridge applies to every initial worker slot of arbitrary mixed catalogs.
It constructs initial invocations only; whole-cohort frames, completed outcomes,
exact loaded-resource inhabitants and corpus certificates remain separate work.
Physical/source correspondence retains the independent contract's boundaries.
-/

set_option autoImplicit false

namespace EDSL.OS.PlainCallAdmission64
open X86 TSO64 Grading.ConcurrentTask.Plain64
open X86.VCGen

/-- The trusted interface kind fixes the exact operand direction and width.
The catalog supplies no arbitrary operation or source/destination registers. -/
def fixedOperation : Kind → PlainMethods.Operation
  | .loadAcquire => .load (.base .rdi)
  | .storeRelease => .store (.base .rdi) .rsi

/-- Static candidate evidence, deliberately separate from independent `Pre`.
The same site proof serves all full64 data values, resources and worker slots. -/
structure StaticShapes (catalog : Catalog) where
  padding : Site → List PlainMethods.Padding
  checked : ∀ site ∈ catalog,
    PlainMethods.check site.image.bytes (fixedOperation site.kind) (padding site) = true

theorem StaticShapes.sound {catalog : Catalog} (static : StaticShapes catalog)
    {site : Site} (member : site ∈ catalog) :
    site.image.bytes.length ≤ 64 ∧
      PlainMethods.Shape site.image.bytes (fixedOperation site.kind) 0 (static.padding site) :=
  PlainMethods.check_sound (static.checked site member)

theorem fixedOperation_address (kind : Kind) (state : X86.State) :
    (fixedOperation kind).address.eval state = state.registers .rdi := by
  cases kind <;> rfl

/-- Source request equality uses current full-width argument bindings and the
selected persistent identity. It does not use any observed or desired word. -/
theorem fixedOperation_request {input : Input} {worker : Worker}
    {reference : Queue.ManagedRef} (arguments : Arguments input worker)
    (target : reference.handle.cell = input.target) :
    (fixedOperation input.site.kind).request reference.handle.cell worker.context.registers =
      input.request := by
  cases input with
  | loadAcquire image object cell occurrence =>
      change (Concurrency.AtomicCalls.Request.loadAcquire reference.handle.cell :
        Concurrency.AtomicCalls.Request Atomics64.CellId64 Word) = .loadAcquire object
      rw [target]
      rfl
  | storeRelease image object cell value occurrence =>
      change Concurrency.AtomicCalls.Request.storeRelease reference.handle.cell
        (worker.context.registers .rsi) =
        Concurrency.AtomicCalls.Request.storeRelease object value
      rw [arguments.store_rsi, target]
      rfl

/-- Proof output connecting the engine's actual invocation to its independently
selected input. The initial queue is the complete actual FIFO and arbitrary
counter, rather than a fabricated empty/zero boundary. -/
structure Admitted (input : Input) (before : TSO64.State) (tid : Nat) where
  invocation : PlainMethods.Invocation before tid
  entryFacts : Entry input before invocation.initial
  bytes : invocation.method.bytes = input.site.image.bytes
  base : invocation.method.base = input.site.image.base
  operation : invocation.method.operation = fixedOperation input.site.kind
  address : invocation.method.address = input.cell.address
  descriptor : invocation.method.reference.cell = input.cell
  target : invocation.method.reference.handle.cell = input.target
  authority : Queue.Current before.world invocation.initial.resources invocation.method.reference
  initialQueue : invocation.method.initialQueue =
    ⟨invocation.initial.pending, invocation.initial.nextStore⟩
  request : invocation.method.request = input.request
  occurrence : invocation.occurrence = input.occurrence

/-- Construct all method obligations from actual data, CodeAt and the separate
static checker theorem. Current and the entry cutpoint are conclusions here. -/
theorem admit_entry {catalog : Catalog} (static : StaticShapes catalog)
    {input : Input} (member : input.site ∈ catalog)
    {before : TSO64.State} {tid : Nat} {worker : Worker}
    (valid : WellFormed before .sharedCell) (live : before.workers[tid]? = some worker)
    (facts : Entry input before worker) : Nonempty (Admitted input before tid) := by
  obtain ⟨identifier, handle, selected, linked⟩ := facts.selected
  obtain ⟨continuation, caller, returnCanonical⟩ := facts.caller
  have checked := static.sound member
  let reference : Queue.ManagedRef := ⟨identifier, handle, input.cell⟩
  let method : PlainMethods.Method := {
    bytes := input.site.image.bytes
    operation := fixedOperation input.site.kind
    base := input.site.image.base
    entry := worker.context.registers
    entryFlags := worker.context.flags
    resources := worker.resources
    reference := reference
    returnAddress := continuation
    initialQueue := ⟨worker.pending, worker.nextStore⟩
    size := checked.1
    codeNoWrap := facts.code.1
    originalRsp := facts.originalRsp
    returnCanonical := returnCanonical
    stackNoWrap := facts.scalar.stackBound }
  have address : method.address = input.cell.address := by
    change (fixedOperation input.site.kind).address.eval method.entryCPU = input.cell.address
    rw [fixedOperation_address]
    exact facts.arguments.rdi
  have current : PlainMethods.Current method before := by
    refine ⟨valid, facts.code, facts.fits, caller, ?_⟩
    change atomicFor before.world worker.resources method.address =
      some (identifier, handle, input.cell)
    rw [address]
    exact selected
  have entryAt : PlainMethods.At method (.preamble 0 (static.padding input.site)) worker := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · change PlainMethods.QueueFrame ⟨worker.pending, worker.nextStore⟩
        ⟨worker.pending, worker.nextStore⟩
      exact PlainMethods.QueueFrame.refl _
    · refine ⟨facts.running, ?_, rfl, checked.2⟩
      change worker.context.rip = input.site.image.base + BitVec.ofNat 64 0
      simpa using facts.pc
  let invocation : PlainMethods.Invocation before tid :=
    ⟨method, static.padding input.site, input.occurrence, worker, current, live, entryAt⟩
  have authorized := atomicFor_sound selected
  refine ⟨{
    invocation := invocation
    entryFacts := facts
    bytes := rfl
    base := rfl
    operation := rfl
    address := address
    descriptor := rfl
    target := linked
    authority := ⟨authorized.1, authorized.2.1⟩
    initialQueue := rfl
    request := ?_
    occurrence := rfl }⟩
  exact fixedOperation_request facts.arguments (reference := reference) linked

/-- Cover the actual selected worker in every initial slot. Catalogs can mix
load/store sites, images, padding, cells, actors and incoming FIFO contents. -/
theorem admit_slot {catalog : Catalog} (static : StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) (tid : Fin before.workers.length) :
    Nonempty (Admitted (inputs tid) before tid.val) := by
  obtain ⟨worker, live, facts⟩ := pre.entry tid
  exact admit_entry static (pre.selected tid) pre.valid live facts

/-- Choice selects an already proved initial invocation, never a future run. -/
noncomputable def admission {catalog : Catalog} (static : StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) (tid : Fin before.workers.length) :
    Admitted (inputs tid) before tid.val :=
  Classical.choice (admit_slot static pre tid)

noncomputable def invocations {catalog : Catalog} (static : StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) :
    (tid : Fin before.workers.length) → PlainMethods.Invocation before tid.val :=
  fun tid => (admission static pre tid).invocation

theorem Admitted.scalar {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) : ScalarCall64.Entry admitted.invocation.initial :=
  admitted.entryFacts.scalar

theorem Admitted.selected {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) :
    atomicFor before.world admitted.invocation.initial.resources input.cell.address =
      some (admitted.invocation.method.reference.identifier,
        admitted.invocation.method.reference.handle, admitted.invocation.method.reference.cell) := by
  rw [← admitted.address, admitted.invocation.entry.resources]
  exact admitted.invocation.current.selected

theorem Admitted.registers {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) :
    admitted.invocation.method.entry = admitted.invocation.initial.context.registers :=
  admitted.invocation.entry.location.2.2.1.symm

theorem Admitted.flags {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) :
    admitted.invocation.method.entryFlags = admitted.invocation.initial.context.flags :=
  admitted.invocation.entry.flags.symm

theorem Admitted.resources {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) :
    admitted.invocation.method.resources = admitted.invocation.initial.resources :=
  admitted.invocation.entry.resources.symm

theorem Admitted.initial_eq {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) {worker : Worker}
    (live : before.workers[tid]? = some worker) : admitted.invocation.initial = worker :=
  Option.some.inj (admitted.invocation.live.symm.trans live)

theorem Admitted.counter {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) :
    admitted.invocation.method.initialQueue.nextStore = admitted.invocation.initial.nextStore :=
  congrArg Queue.Cursor.nextStore admitted.initialQueue

theorem Admitted.pending {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : Admitted input before tid) :
    admitted.invocation.method.initialQueue.pending = admitted.invocation.initial.pending :=
  congrArg Queue.Cursor.pending admitted.initialQueue

theorem invocations_request {catalog : Catalog} (static : StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) (tid : Fin before.workers.length) :
    (invocations static pre tid).method.request = (inputs tid).request :=
  (admission static pre tid).request

theorem invocations_occurrence {catalog : Catalog} (static : StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) (tid : Fin before.workers.length) :
    (invocations static pre tid).occurrence = (inputs tid).occurrence :=
  (admission static pre tid).occurrence

theorem invocations_scalar {catalog : Catalog} (static : StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) (tid : Fin before.workers.length) :
    ScalarCall64.Entry (invocations static pre tid).initial :=
  (admission static pre tid).scalar

theorem invocations_initialQueue {catalog : Catalog} (static : StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) (tid : Fin before.workers.length) :
    (invocations static pre tid).method.initialQueue =
      ⟨(invocations static pre tid).initial.pending, (invocations static pre tid).initial.nextStore⟩ :=
  (admission static pre tid).initialQueue

end EDSL.OS.PlainCallAdmission64

#audit_edsl
