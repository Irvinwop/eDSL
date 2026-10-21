/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.ManagedRules

/-!
Constructive MOV64 issue rules for the production shared-cell TSO64 profile.
Operands use the actual prestate, including destination/base/index aliases and
RSP. Current authority and the current mixed-FIFO invariant supply enabledness;
neither a loaded value nor a successful future action is an input.

These are primitive instruction rules. In particular, changing RSP does not
replace the original caller loan or promise that a later RET can use it. The
existing scalar RAM, address, translation/alias and target-profile assumptions
of Sequential, Atomics64 and TSO64 remain the environmental contract.
-/

set_option autoImplicit false

namespace EDSL.X86.VCGen.ManagedAccess
open OS OS.TSO64 AtomicMethods

/-- Recover the complete descriptor actually selected at the operand address.
Membership, reauthorization and address binding all come from production lookup. -/
theorem selected_current {world : World} {resources : Resources} {address : Word}
    {reference : Queue.ManagedRef}
    (selected : atomicFor world resources address =
      some (reference.identifier, reference.handle, reference.cell)) :
    Queue.Current world resources reference ∧ reference.cell.address = address := by
  obtain ⟨member, authorized, operand⟩ := atomicFor_sound selected
  exact ⟨⟨member, authorized⟩, operand⟩

/-- Ordinary grants cannot coexist at a current managed operand in a
well-formed world. Reservation plus allocation separation gives disjointness;
the zero-offset byte contradicts an ordinary grant at this same qword. -/
theorem grantFor_managed_none {world : World} {resources : Resources}
    {reference : Queue.ManagedRef} (valid : Atomics64.WellFormed world)
    (current : Queue.Current world resources reference) (value : Word) :
    grantFor world resources ⟨reference.cell.address, .qword value⟩ = none := by
  cases grant : grantFor world resources ⟨reference.cell.address, .qword value⟩ with
  | none => rfl
  | some ticket =>
    have separate := (grantFor_sound grant).2.managed_disjoint valid current
    have impossible := separate 0 (by decide)
    simp [StoreBuffer.Mixed.Store.width] at impossible

private theorem view_readable (memory : Memory) (pending : StoreBuffer.Mixed.Buffer)
    (query : Word) (readable : (memory.read query).isSome = true) :
    ((StoreBuffer.Mixed.view memory pending).read query).isSome = true := by
  rw [StoreBuffer.Mixed.view_read]
  cases StoreBuffer.Mixed.forward pending query with
  | none => exact readable
  | some byte => rfl

/-- A mixed overlay preserves write permissions and cannot erase readable
bytes. This supplies the real sequential store preflight, without executing a
speculative store or requiring an empty FIFO. -/
theorem view_canStoreQWord (memory : Memory) (pending : StoreBuffer.Mixed.Buffer)
    (address : Word) (writable : canStoreQWord memory address = true) :
    canStoreQWord (StoreBuffer.Mixed.view memory pending) address = true := by
  simp only [canStoreQWord, qwordWritable, StoreBuffer.Mixed.view_writable,
    Bool.and_eq_true] at writable ⊢
  rcases writable with ⟨addressable, permissions,
    ⟨⟨⟨⟨⟨⟨⟨r0, r1⟩, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩, r7⟩⟩
  exact ⟨addressable, permissions,
    ⟨⟨⟨⟨⟨⟨⟨view_readable _ _ _ r0, view_readable _ _ _ r1⟩,
      view_readable _ _ _ r2⟩, view_readable _ _ _ r3⟩,
      view_readable _ _ _ r4⟩, view_readable _ _ _ r5⟩,
      view_readable _ _ _ r6⟩, view_readable _ _ _ r7⟩⟩

/-- Derive a real local load value. Whole-qword compatibility comes from WF
and the current queue authority. The fallback value exists in CURRENT published
RAM by current managed authority, rather than an invocation-memory snapshot.
An own-forwarded result is not advertised as an Atomics64.load event. -/
theorem managed_load_enabled {state : OS.TSO64.State} {worker : Worker}
    {profile : Profile} {reference : Queue.ManagedRef}
    (valid : WellFormed state profile)
    (workerValid : WorkerValid state.world worker profile)
    (current : Queue.Current state.world worker.resources reference) :
    ∃ value,
      loadQWord (localCPU state worker).memory reference.cell.address = .ok value ∧
      (match StoreBuffer.Mixed.newestQWord (payload worker.pending) reference.cell.address with
      | some origin => Except.ok origin.value
      | none => loadQWord (published state.world) reference.cell.address) = .ok value := by
  have source := local_managed_load valid workerValid current
  cases found : StoreBuffer.Mixed.newestQWord (payload worker.pending) reference.cell.address with
  | none =>
    obtain ⟨value, publishedRead⟩ := current.validCell.1.load_exists
    rw [found] at source
    exact ⟨value, source.trans publishedRead, publishedRead⟩
  | some origin =>
    exact ⟨origin.value, by simpa only [found] using source, rfl⟩

/-- The actual read admission uses the same complete selected reference.
The ordinary-priority branch is excluded by the current invariant. -/
theorem checkRead_managed {state : OS.TSO64.State} {worker : Worker} {address : Word}
    {reference : Queue.ManagedRef} (valid : Atomics64.WellFormed state.world)
    (selected : atomicFor state.world worker.resources address =
      some (reference.identifier, reference.handle, reference.cell)) :
    checkRead state worker ⟨.data, address, 8⟩ .sharedCell = .ok () := by
  obtain ⟨current, operand⟩ := selected_current (reference := reference) selected
  have absent : grantFor state.world worker.resources ⟨address, .qword 0⟩ = none := by
    rw [← operand]
    exact grantFor_managed_none valid current 0
  simp only [checkRead, pure_ok, ok_bind]
  rw [absent, selected]

theorem queue_loadMem64 (state : OS.TSO64.State) (worker : Worker)
    (destination : Register) (address : Sequential.Address) :
    QueueEffect state worker (.loadMem64 destination address)
      ⟨worker.pending, worker.nextStore⟩ .sharedCell := .unchanged rfl

/-- Production managed admission captures the original full source value and
complete reference, allocating the occurrence from nextStore, never FIFO length.
Both effective address and source are evaluated before any context update. -/
theorem queue_storeMem64 {state : OS.TSO64.State} {worker : Worker}
    {address : Sequential.Address} {source : Register} {reference : Queue.ManagedRef}
    (valid : Atomics64.WellFormed state.world)
    (selected : atomicFor state.world worker.resources (address.eval (localCPU state worker)) =
      some (reference.identifier, reference.handle, reference.cell)) :
    QueueEffect state worker (.storeMem64 address source)
      ⟨worker.pending ++ [.managed reference (worker.context.registers source) worker.nextStore],
        worker.nextStore + 1⟩ .sharedCell := by
  obtain ⟨current, operand⟩ := selected_current (reference := reference) selected
  have absent : grantFor state.world worker.resources
      ⟨address.eval (localCPU state worker), .qword (worker.context.registers source)⟩ = none := by
    rw [← operand]
    exact grantFor_managed_none valid current (worker.context.registers source)
  exact .enqueued (store :=
    ⟨address.eval (localCPU state worker), .qword (worker.context.registers source)⟩)
    rfl (.managed reference (worker.context.registers source) absent rfl rfl selected)

/-- Every actual queue effect at this selected store has exactly this original
reference and occurrence. Equal addresses or values cannot substitute another
handle. This follows from the production prepareQueue result's uniqueness. -/
theorem queue_storeMem64_identity {state : OS.TSO64.State} {worker : Worker}
    {address : Sequential.Address} {source : Register} {reference : Queue.ManagedRef}
    {update : Queue.Cursor} (valid : Atomics64.WellFormed state.world)
    (selected : atomicFor state.world worker.resources (address.eval (localCPU state worker)) =
      some (reference.identifier, reference.handle, reference.cell))
    (effect : QueueEffect state worker (.storeMem64 address source) update .sharedCell) :
    update = ⟨worker.pending ++ [.managed reference (worker.context.registers source) worker.nextStore],
      worker.nextStore + 1⟩ := by
  exact Except.ok.inj ((ManagedRules.queue_checked effect).symm.trans
    (ManagedRules.queue_checked (queue_storeMem64 (state := state) (worker := worker)
      (address := address) (source := source) (reference := reference) valid selected)))

/-- Complete primitive context and resource frame. The full destination write
permits RSP and address-register aliases; it carries no later RET obligation. -/
structure LoadFrame (before after : Worker) (destination : Register)
    (address : Sequential.Address) (value : Word) : Prop where
  context : after.context =
    ⟨(fun register => if register = destination then value else before.context.registers register),
      before.context.rip + BitVec.ofNat 64
        (Sequential.Instruction.loadMem64 destination address).length, before.context.flags⟩
  resources : after.resources = before.resources
  phase : after.phase = before.phase
  pending : after.pending = before.pending
  nextStore : after.nextStore = before.nextStore

/-- A store changes only RIP and its own FIFO/counter. Published RAM belongs
to the enclosing issue result's unchanged world, never the sequential scratch
memory used to validate and execute this instruction. -/
structure StoreFrame (before after : Worker) (address : Sequential.Address)
    (source : Register) (reference : Queue.ManagedRef) : Prop where
  context : after.context = { before.context with
    rip := before.context.rip + BitVec.ofNat 64
      (Sequential.Instruction.storeMem64 address source).length }
  resources : after.resources = before.resources
  phase : after.phase = before.phase
  pending : after.pending = before.pending ++
    [.managed reference (before.context.registers source) before.nextStore]
  nextStore : after.nextStore = before.nextStore + 1

theorem LoadFrame.destination {before after : Worker} {destination : Register}
    {address : Sequential.Address} {value : Word}
    (frame : LoadFrame before after destination address value) :
    after.context.registers destination = value := by
  rw [frame.context]
  simp

theorem LoadFrame.other {before after : Worker} {destination register : Register}
    {address : Sequential.Address} {value : Word}
    (frame : LoadFrame before after destination address value) (different : register ≠ destination) :
    after.context.registers register = before.context.registers register := by
  rw [frame.context]
  simp only [different, ↓reduceIte]

theorem LoadFrame.rip {before after : Worker} {destination : Register}
    {address : Sequential.Address} {value : Word}
    (frame : LoadFrame before after destination address value) :
    after.context.rip = before.context.rip + BitVec.ofNat 64
      (Sequential.Instruction.loadMem64 destination address).length :=
  congrArg Context.rip frame.context

theorem LoadFrame.flags {before after : Worker} {destination : Register}
    {address : Sequential.Address} {value : Word}
    (frame : LoadFrame before after destination address value) :
    after.context.flags = before.context.flags := by rw [frame.context]

theorem StoreFrame.registers {before after : Worker} {address : Sequential.Address}
    {source : Register} {reference : Queue.ManagedRef}
    (frame : StoreFrame before after address source reference) :
    after.context.registers = before.context.registers := by rw [frame.context]

theorem StoreFrame.rip {before after : Worker} {address : Sequential.Address}
    {source : Register} {reference : Queue.ManagedRef}
    (frame : StoreFrame before after address source reference) :
    after.context.rip = before.context.rip + BitVec.ofNat 64
      (Sequential.Instruction.storeMem64 address source).length :=
  congrArg Context.rip frame.context

theorem StoreFrame.flags {before after : Worker} {address : Sequential.Address}
    {source : Register} {reference : Queue.ManagedRef}
    (frame : StoreFrame before after address source reference) :
    after.context.flags = before.context.flags := by rw [frame.context]

/-- A checked decoder node, current resources and selected authority derive
the actual successful production issue, its actual OrdinaryEffect and a real
loaded value. No empty-queue, desired-value or execution-success premise occurs.
The fixed world and ordinary observation exclude instruction publication. -/
theorem issue_loadMem64 {bytes : List Byte} {offset : Nat} {destination : Register}
    {address : Sequential.Address}
    (node : Node bytes offset (.ordinary (.loadMem64 destination address)))
    (size : bytes.length ≤ 64)
    {state : OS.TSO64.State} {worker : Worker} {tid : Nat} {base : Word}
    {reference : Queue.ManagedRef}
    (valid : WellFormed state .sharedCell) (live : state.workers[tid]? = some worker)
    (running : worker.phase = .running)
    (code : CodeAt (published state.world) base bytes)
    (fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region)
    (pc : worker.context.rip = base + BitVec.ofNat 64 offset)
    (selected : atomicFor state.world worker.resources (address.eval (localCPU state worker)) =
      some (reference.identifier, reference.handle, reference.cell)) (af : Bool) :
    ∃ value after,
      issue state tid af .sharedCell =
        .ok (install state tid state.world after, .ordinary tid) ∧
      OrdinaryEffect state tid worker (.loadMem64 destination address) af
        (install state tid state.world after, .ordinary tid) .sharedCell ∧
      Queue.Current state.world worker.resources reference ∧
      loadQWord (localCPU state worker).memory reference.cell.address = .ok value ∧
      (match StoreBuffer.Mixed.newestQWord (payload worker.pending) reference.cell.address with
      | some origin => Except.ok origin.value
      | none => loadQWord (published state.world) reference.cell.address) = .ok value ∧
      LoadFrame worker after destination address value := by
  have workerValid := valid.2 worker (List.mem_of_getElem? live)
  obtain ⟨current, operand⟩ := selected_current (reference := reference) selected
  obtain ⟨value, loaded, source⟩ := managed_load_enabled valid workerValid current
  let output : X86.State := { (localCPU state worker).writeRegister destination value with
    rip := worker.context.rip + BitVec.ofNat 64
      (Sequential.Instruction.loadMem64 destination address).length }
  let observation : Sequential.Observation :=
    ⟨.next output, [⟨.data, address.eval (localCPU state worker), 8⟩]⟩
  let after : Worker := { worker with context := .ofCPU output }
  have executed : Sequential.execute (localCPU state worker)
      (.loadMem64 destination address) af = .ok observation := by
    apply Sequential.execute_loadMem64_success_iff.mpr
    exact ⟨value, by rw [← operand]; exact loaded, rfl⟩
  have checked : checkRead state worker
      ⟨.data, address.eval (localCPU state worker), 8⟩ .sharedCell = .ok () :=
    checkRead_managed (state := state) (worker := worker) (reference := reference) valid.1 selected
  have reads : ∃ units, ((Sequential.Instruction.loadMem64 destination address).operandReads
      (localCPU state worker)).mapM
        (fun read => checkRead state worker read .sharedCell) = .ok units := by
    refine ⟨[()], ?_⟩
    simp only [Sequential.Instruction.operandReads, List.mapM_cons, checked,
      ok_bind, List.mapM_nil, pure_ok]
  have queue := queue_loadMem64 state worker destination address
  have finish : FinishEffect state tid worker worker.pending observation
      (install state tid state.world after, .ordinary tid) worker.nextStore := .next rfl
  have actual : issue state tid af .sharedCell =
      .ok (install state tid state.world after, .ordinary tid) := by
    rw [ManagedRules.issue_ordinary node size valid live running code fits pc rfl reads queue executed]
    exact ManagedRules.finish_checked finish
  have decoded : Sequential.decodeAt (localCPU state worker) =
      .ok (.loadMem64 destination address) :=
    decode_ordinary (node.decoded size (ManagedRules.local_code valid workerValid code fits)
      (localCPU state worker) rfl pc)
  have effect : OrdinaryEffect state tid worker (.loadMem64 destination address) af
      (install state tid state.world after, .ordinary tid) .sharedCell :=
    .intro rfl (node.codeFits code fits pc) decoded reads queue
      (by rw [Sequential.step_eq_execute af decoded]; exact executed) finish
  exact ⟨value, after, actual, effect, current, loaded, source, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Actual MOV64 store issue executes the existing checked sequential store
and commits the production QueueEffect together. Its original source, complete
selected reference and actual nextStore survive into the literal appended tag.
No world update or publication event accompanies this instruction. -/
theorem issue_storeMem64 {bytes : List Byte} {offset : Nat} {address : Sequential.Address}
    {source : Register}
    (node : Node bytes offset (.ordinary (.storeMem64 address source)))
    (size : bytes.length ≤ 64)
    {state : OS.TSO64.State} {worker : Worker} {tid : Nat} {base : Word}
    {reference : Queue.ManagedRef}
    (valid : WellFormed state .sharedCell) (live : state.workers[tid]? = some worker)
    (running : worker.phase = .running)
    (code : CodeAt (published state.world) base bytes)
    (fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region)
    (pc : worker.context.rip = base + BitVec.ofNat 64 offset)
    (selected : atomicFor state.world worker.resources (address.eval (localCPU state worker)) =
      some (reference.identifier, reference.handle, reference.cell)) (af : Bool) :
    ∃ after,
      issue state tid af .sharedCell =
        .ok (install state tid state.world after, .ordinary tid) ∧
      OrdinaryEffect state tid worker (.storeMem64 address source) af
        (install state tid state.world after, .ordinary tid) .sharedCell ∧
      QueueEffect state worker (.storeMem64 address source)
        ⟨worker.pending ++ [.managed reference (worker.context.registers source) worker.nextStore],
          worker.nextStore + 1⟩ .sharedCell ∧
      Queue.Current state.world worker.resources reference ∧
      StoreFrame worker after address source reference := by
  have workerValid := valid.2 worker (List.mem_of_getElem? live)
  obtain ⟨current, operand⟩ := selected_current (reference := reference) selected
  have writable : canStoreQWord (localCPU state worker).memory
      (address.eval (localCPU state worker)) = true := by
    rw [← operand]
    exact view_canStoreQWord (published state.world) (payload worker.pending)
      reference.cell.address current.validCell.1.writable
  have stored := (qword_store_sound (localCPU state worker).memory
    (address.eval (localCPU state worker)) ((localCPU state worker).registers source) writable).1
  let output : X86.State := { localCPU state worker with
    memory := writeQWordUnchecked (localCPU state worker).memory
      (address.eval (localCPU state worker)) ((localCPU state worker).registers source)
    rip := worker.context.rip + BitVec.ofNat 64
      (Sequential.Instruction.storeMem64 address source).length }
  let observation : Sequential.Observation := ⟨.next output, []⟩
  let after : Worker := { worker with
    context := .ofCPU output
    pending := worker.pending ++ [.managed reference (worker.context.registers source) worker.nextStore]
    nextStore := worker.nextStore + 1 }
  have executed : Sequential.execute (localCPU state worker)
      (.storeMem64 address source) af = .ok observation := by
    simp only [Sequential.execute_storeMem64, stored, ok_bind, pure_ok]
    rfl
  have reads : ∃ units, ((Sequential.Instruction.storeMem64 address source).operandReads
      (localCPU state worker)).mapM
        (fun read => checkRead state worker read .sharedCell) = .ok units := ⟨[], rfl⟩
  have queue := queue_storeMem64 (state := state) (worker := worker) (address := address)
    (source := source) (reference := reference) valid.1 selected
  have finish : FinishEffect state tid worker
      (worker.pending ++ [.managed reference (worker.context.registers source) worker.nextStore])
      observation (install state tid state.world after, .ordinary tid)
      (worker.nextStore + 1) := .next rfl
  have actual : issue state tid af .sharedCell =
      .ok (install state tid state.world after, .ordinary tid) := by
    rw [ManagedRules.issue_ordinary node size valid live running code fits pc rfl reads queue executed]
    exact ManagedRules.finish_checked finish
  have decoded : Sequential.decodeAt (localCPU state worker) =
      .ok (.storeMem64 address source) :=
    decode_ordinary (node.decoded size (ManagedRules.local_code valid workerValid code fits)
      (localCPU state worker) rfl pc)
  have effect : OrdinaryEffect state tid worker (.storeMem64 address source) af
      (install state tid state.world after, .ordinary tid) .sharedCell :=
    .intro rfl (node.codeFits code fits pc) decoded reads queue
      (by rw [Sequential.step_eq_execute af decoded]; exact executed) finish
  exact ⟨after, actual, effect, queue, current, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

end EDSL.X86.VCGen.ManagedAccess

#audit_edsl
