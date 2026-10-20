/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.ReadSource
import EDSL.OS.TSO64.StoreHistory

set_option autoImplicit false

namespace EDSL.OS.TSO64
open X86

/-- Extract a fixed ordinary instruction's effect from actual successful issue
and the guarded decode. Clients need not repeat worker/instruction equality
arguments before applying the load-history theorem. -/
theorem issue_ordinary_effect {state : State} {tid : Nat} {af : Bool}
    {worker : Worker} {instruction : Sequential.Instruction}
    {result : State × Observation} {profile : Profile}
    (live : state.workers[tid]? = some worker)
    (fetched : decode (fetchCPU state worker) = .ok (.ordinary instruction))
    (success : step state (.issue tid af) profile = .ok result) :
    OrdinaryEffect state tid worker instruction af result profile := by
  obtain ⟨actual, actualLive, _, _, _, selected, actualFetch, effect⟩ :=
    issue_effect (profile := profile) success
  have workerEq : actual = worker := Option.some.inj (actualLive.symm.trans live)
  subst actual
  have instructionEq : selected = .ordinary instruction :=
    Except.ok.inj (actualFetch.symm.trans fetched)
  subst selected
  exact effect

/-- The actual whole-qword source together with exact same-thread issue
provenance for a forwarded tag. Published RAM is identified as current memory;
a separate last-published-writer history is still required to name its writer.
Arbitrary nonempty initial queues retain their original boundary alternative. -/
inductive ManagedReadHistory (initial : State) (actions : List Action)
    (result : State × List Observation) (profile : Profile) (tid : Nat)
    (worker : Worker) (reference : Queue.ManagedRef) (value : Word) : Prop where
  | forwarded (position : StoreBuffer.Mixed.QWordOrigin) (writer : Queue.ManagedRef)
      (occurrence : Nat)
      (newest : StoreBuffer.Mixed.newestQWord (payload worker.pending)
        reference.cell.address = some position)
      (entry : worker.pending[position.index]? = some (.managed writer value occurrence))
      (payload : position.value = value)
      (address : writer.cell.address = reference.cell.address)
      (current : Queue.Current result.1.world worker.resources writer)
      (below : occurrence < worker.nextStore)
      (origin : StoreHistory.Origin initial actions result profile tid (.managed writer value occurrence)) :
      ManagedReadHistory initial actions result profile tid worker reference value
  | published
      (absent : StoreBuffer.Mixed.newestQWord (payload worker.pending)
        reference.cell.address = none)
      (read : loadQWord (published result.1.world) reference.cell.address = .ok value) :
      ManagedReadHistory initial actions result profile tid worker reference value

/-- A forwarded source from a real prefix run is an exact initial entry or a
real store issue by the same scheduler thread. Equal-valued writes and peers'
occurrence numbers are never used as substitute identities. -/
theorem ManagedReadSource.history {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid : Nat}
    {worker : Worker} {reference : Queue.ManagedRef} {value : Word}
    (source : ManagedReadSource result.1 worker reference value)
    (success : schedule initial actions profile = .ok result)
    (live : result.1.workers[tid]? = some worker) :
    ManagedReadHistory initial actions result profile tid worker reference value := by
  cases source with
  | forwarded position writer occurrence newest entry payload address current below =>
    exact .forwarded position writer occurrence newest entry payload address current below
      (StoreHistory.schedule_pending_origin success
        ⟨worker, live, List.mem_of_getElem? entry⟩)
  | published absent read => exact .published absent read

/-- Empty setup supplies a real issue for any indexed managed entry. Actual
newest-source selection is supplied separately by `ManagedReadSource.history`.
This result does not manufacture an origin for nonempty initial queues. -/
theorem indexed_managed_issue_after_schedule {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid : Nat}
    {worker : Worker} {reference : Queue.ManagedRef} {value : Word} {occurrence : Nat}
    {position : StoreBuffer.Mixed.QWordOrigin}
    (empty : Quiescent initial)
    (success : schedule initial actions profile = .ok result)
    (live : result.1.workers[tid]? = some worker)
    (entry : worker.pending[position.index]? = some (.managed reference value occurrence)) :
    StoreHistory.IssuedIn profile tid (.managed reference value occurrence) initial actions result :=
  StoreHistory.schedule_pending_issued empty success ⟨worker, live, List.mem_of_getElem? entry⟩

/-- The next actual MOV64 after a successful prefix has both exact destination
installation and the history-backed source. Prefix validity/numbering are
proved by schedule preservation, not assumed for the successor state. -/
theorem schedule_loadMem64_history {initial : State} {actions : List Action}
    {priorRun : State × List Observation} {profile : Profile} {tid : Nat}
    {worker : Worker} {reference : Queue.ManagedRef}
    {destination : Register} {address : Sequential.Address} {af : Bool}
    {result : State × Observation}
    (valid : WellFormed initial profile) (sequenced : Sequenced initial)
    (success : schedule initial actions profile = .ok priorRun)
    (live : priorRun.1.workers[tid]? = some worker)
    (current : Queue.Current priorRun.1.world worker.resources reference)
    (operand : reference.cell.address = address.eval (localCPU priorRun.1 worker))
    (effect : OrdinaryEffect priorRun.1 tid worker (.loadMem64 destination address) af result profile) :
    ∃ value, ManagedReadHistory initial actions priorRun profile tid worker reference value ∧
      loadQWord (localCPU priorRun.1 worker).memory reference.cell.address = .ok value ∧
      result = (install priorRun.1 tid priorRun.1.world
        { worker with context := .ofCPU (
          { (localCPU priorRun.1 worker).writeRegister destination value with
            rip := (localCPU priorRun.1 worker).rip +
              BitVec.ofNat 64 (Sequential.Instruction.loadMem64 destination address).length }) },
        .ordinary tid) := by
  obtain ⟨value, source, loaded, installed⟩ := effect.managed_read_source
    (schedule_wellFormed valid success) (schedule_sequenced sequenced success) live current operand
  exact ⟨value, source.history success live, loaded, installed⟩

end EDSL.OS.TSO64
