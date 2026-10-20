/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Access
import EDSL.OS.TSO64.Occurrences

set_option autoImplicit false

namespace EDSL.OS.TSO64
open X86

/-- A successful managed whole-word load names either the exact newest pending
managed occurrence or the current published read. The queue position is a
snapshot position; `occurrence` is the worker's persistent issue number. This
predicate alone does not authenticate an earlier instruction issue or identify
the last published writer. -/
inductive ManagedReadSource (state : State) (worker : Worker)
    (reference : Queue.ManagedRef) (value : Word) : Prop where
  | forwarded (origin : StoreBuffer.Mixed.QWordOrigin) (writer : Queue.ManagedRef)
      (occurrence : Nat)
      (newest : StoreBuffer.Mixed.newestQWord (payload worker.pending)
        reference.cell.address = some origin)
      (entry : worker.pending[origin.index]? = some (.managed writer value occurrence))
      (payload : origin.value = value)
      (address : writer.cell.address = reference.cell.address)
      (current : Queue.Current state.world worker.resources writer)
      (below : occurrence < worker.nextStore) : ManagedReadSource state worker reference value
  | published
      (absent : StoreBuffer.Mixed.newestQWord (payload worker.pending)
        reference.cell.address = none)
      (read : loadQWord (published state.world) reference.cell.address = .ok value) :
      ManagedReadSource state worker reference value

/-- Current managed authority excludes ordinary stores at the selected word.
Thus a production newest-qword position recovers a managed descriptor and
persistent occurrence, including when several writes have equal payloads. -/
theorem newest_managed_entry {state : State} {worker : Worker} {profile : Profile}
    {resources : Resources} {reference : Queue.ManagedRef}
    {origin : StoreBuffer.Mixed.QWordOrigin}
    (valid : WellFormed state profile) (workerValid : WorkerValid state.world worker profile)
    (ordered : worker.storeCursor.Ordered)
    (current : Queue.Current state.world resources reference)
    (found : StoreBuffer.Mixed.newestQWord (payload worker.pending)
      reference.cell.address = some origin) :
    ∃ writer occurrence,
      worker.pending[origin.index]? = some (.managed writer origin.value occurrence) ∧
      writer.cell.address = reference.cell.address ∧
      Queue.Current state.world worker.resources writer ∧ occurrence < worker.nextStore := by
  rcases worker.storeCursor.newestQWord_tag ordered reference.cell.address origin found with
    ordinary | managed
  · obtain ⟨ticket, entry⟩ := ordinary
    have gate := (workerValid.2 _ (List.mem_of_getElem? entry)).2
    have separate := gate.managed_disjoint valid.1 current
    have impossible := separate 0 (by decide)
    simp [StoreBuffer.Mixed.Store.width] at impossible
  · obtain ⟨writer, occurrence, entry, address, below⟩ := managed
    exact ⟨writer, occurrence, entry, address,
      (workerValid.2 _ (List.mem_of_getElem? entry)).2, below⟩

/-- The real local byte load determines its tagged source. Whole-qword
compatibility is derived from the current resource invariant, rather than
accepted as replacement authority. -/
theorem managed_read_source {state : State} {worker : Worker} {profile : Profile}
    {resources : Resources} {reference : Queue.ManagedRef} {value : Word}
    (valid : WellFormed state profile) (workerValid : WorkerValid state.world worker profile)
    (ordered : worker.storeCursor.Ordered)
    (current : Queue.Current state.world resources reference)
    (loaded : loadQWord (localCPU state worker).memory reference.cell.address = .ok value) :
    ManagedReadSource state worker reference value := by
  have source := local_managed_load valid workerValid current
  cases found : StoreBuffer.Mixed.newestQWord (payload worker.pending) reference.cell.address with
  | none =>
    rw [found] at source
    exact .published found (source.symm.trans loaded)
  | some origin =>
    obtain ⟨writer, occurrence, entry, address, authority, below⟩ :=
      newest_managed_entry valid workerValid ordered current found
    rw [found] at source
    have same : origin.value = value := Except.ok.inj (source.symm.trans loaded)
    subst value
    exact .forwarded origin writer occurrence found entry rfl address authority below

/-- An actual retiring MOV64 has the source above and installs the exact loaded
word in its destination. The source register may alias the address or stack
register; operands come from the pre-execution local CPU. -/
theorem OrdinaryEffect.managed_read_source {state : State} {tid : Nat} {worker : Worker}
    {destination : Register} {address : Sequential.Address} {af : Bool}
    {result : State × Observation} {profile : Profile} {reference : Queue.ManagedRef}
    (effect : OrdinaryEffect state tid worker (.loadMem64 destination address) af result profile)
    (valid : WellFormed state profile) (sequenced : Sequenced state)
    (live : state.workers[tid]? = some worker)
    (current : Queue.Current state.world worker.resources reference)
    (operand : reference.cell.address = address.eval (localCPU state worker)) :
    ∃ value, ManagedReadSource state worker reference value ∧
      loadQWord (localCPU state worker).memory reference.cell.address = .ok value ∧
      result = (install state tid state.world
        { worker with context := .ofCPU (
          { (localCPU state worker).writeRegister destination value with
            rip := (localCPU state worker).rip +
              BitVec.ofNat 64 (Sequential.Instruction.loadMem64 destination address).length }) },
        .ordinary tid) := by
  obtain ⟨value, loaded, _, installed⟩ := effect.managed_loadMem64 valid live current operand
  exact ⟨value, EDSL.OS.TSO64.managed_read_source valid (valid.2 worker (List.mem_of_getElem? live))
    (sequenced worker (List.mem_of_getElem? live)) current loaded, loaded, installed⟩

end EDSL.OS.TSO64
