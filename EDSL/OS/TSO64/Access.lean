/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Frames

namespace EDSL.OS.TSO64
open X86 AddressSpace

private theorem fetched_byte {memory : Memory} {address : Word} {byte : Byte}
    (success : fetchByte memory address = .ok byte) :
    canonical address = true ∧ memory.executable address = true ∧ memory.read address = some byte := by
  unfold fetchByte at success
  split at success
  next allowed =>
    have gates := Bool.and_eq_true_iff.mp allowed
    cases stored : memory.read address with
    | none => simp [stored] at success
    | some actual =>
      simp only [stored, Except.ok.injEq] at success
      subst byte
      exact ⟨gates.1, gates.2, rfl⟩
  next => cases success

/-- Guarded dispatch fetches only actual executable bytes inside the current
original code loan; loan validity itself is supplied by issue_effect. -/
theorem fetchCPU_fetch {state : State} {worker : Worker} {address : Word} {byte : Byte}
    (success : fetchByte (fetchCPU state worker).memory address = .ok byte) :
    worker.resources.code.loan.region.Contains address ∧
      fetchByte (published state.world) address = .ok byte := by
  have fetched := fetched_byte success
  have executable : ((published state.world).executable address &&
      decide (worker.resources.code.loan.region.Contains address)) = true := fetched.2.1
  have gates := Bool.and_eq_true_iff.mp executable
  have stored : (published state.world).read address = some byte := fetched.2.2
  exact ⟨of_decide_eq_true gates.2, by simp [fetchByte, fetched.1, gates.1, stored]⟩

def ReadCurrent (state : State) (worker : Worker) (read : Sequential.Read)
    (profile : Profile := .ownedOnly) : Prop :=
  match read.kind with
  | .stack => read.address = worker.resources.callerAddress ∧ read.bytes = 8 ∧
      ∃ value, Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
        worker.resources.caller.identifier read.address = .ok value
  | .data =>
    let ordinary :=
      (read.bytes = 4 ∧ ∃ ticket, ticket ∈ worker.resources.grants ∧
        StoreGate state.world worker.resources.actor ticket ⟨read.address, .dword 0⟩) ∨
      (read.bytes = 8 ∧ ∃ ticket, ticket ∈ worker.resources.grants ∧
        StoreGate state.world worker.resources.actor ticket ⟨read.address, .qword 0⟩)
    match profile with
    | .ownedOnly => ordinary
    | .sharedCell => ordinary ∨
        (read.bytes = 8 ∧ ∃ reference : Queue.ManagedRef,
          Queue.Current state.world worker.resources reference ∧ reference.cell.address = read.address)

theorem checkRead_current {state : State} {worker : Worker} {read : Sequential.Read}
    {profile : Profile} (success : checkRead state worker read profile = .ok ()) :
    ReadCurrent state worker read profile := by
  cases read with
  | mk kind address width =>
    cases kind with
    | stack => exact checkRead_stack (profile := profile) success
    | data =>
      cases profile with
      | ownedOnly => exact checkRead_data success
      | sharedCell =>
        rcases checkRead_data_for success with ordinary | ⟨_, width, reference, current, address⟩
        · exact .inl ordinary
        · exact .inr ⟨width, reference, current, address⟩

private theorem mapM_member {α β ε : Type} {f : α → Except ε β} {inputs : List α} {outputs : List β}
    (success : inputs.mapM f = .ok outputs) {input : α} (member : input ∈ inputs) :
    ∃ output, f input = .ok output := by
  induction inputs generalizing outputs with
  | nil => simp at member
  | cons head tail ih =>
    cases first : f head with
    | error fault => simp [List.mapM_cons, first] at success
    | ok output =>
      cases rest : tail.mapM f with
      | error fault => simp [List.mapM_cons, first, rest] at success
      | ok results =>
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨output, first⟩
        · exact ih rest later

/-- Full-width current authority AND real machine access success are both
derived from retiring execution. The Mixed overlay supplies only data bytes. -/
theorem OrdinaryEffect.accesses {state : State} {tid : Nat} {worker : Worker}
    {instruction : Sequential.Instruction} {af : Bool} {result : State × Observation}
    {profile : Profile} (effect : OrdinaryEffect state tid worker instruction af result profile) :
    ∃ observation, Sequential.step af (localCPU state worker) = .ok observation ∧
      ∀ read ∈ observation.reads, ReadCurrent state worker read profile ∧
        Sequential.OperandReadSucceeds (localCPU state worker) read := by
  cases effect with
  | intro supported bounds decoded reads queue step finish =>
    refine ⟨_, step, ?_⟩
    intro read member
    have executed := step
    rw [Sequential.step_eq_execute af decoded] at executed
    have origin := Sequential.execute_reads executed
    have listed : read ∈ instruction.operandReads (localCPU state worker) := by rw [← origin]; exact member
    obtain ⟨units, checked⟩ := reads
    obtain ⟨checkedUnit, current⟩ := mapM_member checked listed
    cases checkedUnit
    exact ⟨checkRead_current (profile := profile) current,
      Sequential.observed_reads_succeed step read member⟩

/-- Actual MOV64 execution exposes the local load and the exact installed
destination, including when it aliases an address register or RSP. Queue and
counter remain unchanged because this instruction has no store intent. -/
theorem OrdinaryEffect.loadMem64 {state : State} {tid : Nat} {worker : Worker}
    {destination : Register} {address : Sequential.Address} {af : Bool}
    {result : State × Observation} {profile : Profile}
    (effect : OrdinaryEffect state tid worker (.loadMem64 destination address) af result profile) :
    ∃ value, loadQWord (localCPU state worker).memory (address.eval (localCPU state worker)) = .ok value ∧
      ReadCurrent state worker ⟨.data, address.eval (localCPU state worker), 8⟩ profile ∧
      result = (install state tid state.world
        { worker with context := .ofCPU (
          { (localCPU state worker).writeRegister destination value with
            rip := (localCPU state worker).rip +
              BitVec.ofNat 64 (Sequential.Instruction.loadMem64 destination address).length }) },
        .ordinary tid) := by
  cases effect with
  | intro supported bounds decoded reads queue actual finish =>
    have executed := actual
    rw [Sequential.step_eq_execute af decoded] at executed
    obtain ⟨value, loaded, observationEq⟩ := Sequential.execute_loadMem64_success_iff.mp executed
    obtain ⟨units, checked⟩ := reads
    obtain ⟨checkedUnit, current⟩ := mapM_member checked
      (input := ⟨.data, address.eval (localCPU state worker), 8⟩)
      (by simp [Sequential.Instruction.operandReads])
    cases checkedUnit
    have authority := checkRead_current (profile := profile) current
    cases queue with
    | enqueued intent admission =>
      simp [storeIntent, Sequential.Instruction.storeIntent64,
        Sequential.Instruction.storeIntent] at intent
    | unchanged intent =>
      cases finish with
      | next outcome =>
        rw [observationEq] at outcome
        cases outcome
        exact ⟨value, loaded, authority, rfl⟩
      | returned outcome =>
        rw [observationEq] at outcome
        cases outcome

/-- A whole-word source result for a currently authorized managed MOV. The
machine reads its actual local overlay; this does not invent an Atomics64.load
event for an own-buffer forwarded value. Occurrence provenance is separate. -/
theorem OrdinaryEffect.managed_loadMem64 {state : State} {tid : Nat} {worker : Worker}
    {destination : Register} {address : Sequential.Address} {af : Bool}
    {result : State × Observation} {profile : Profile} {reference : Queue.ManagedRef}
    (effect : OrdinaryEffect state tid worker (.loadMem64 destination address) af result profile)
    (valid : WellFormed state profile) (live : state.workers[tid]? = some worker)
    (current : Queue.Current state.world worker.resources reference)
    (operand : reference.cell.address = address.eval (localCPU state worker)) :
    ∃ value, loadQWord (localCPU state worker).memory reference.cell.address = .ok value ∧
      (match StoreBuffer.Mixed.newestQWord (payload worker.pending) reference.cell.address with
      | some origin => Except.ok origin.value
      | none => loadQWord (published state.world) reference.cell.address) = .ok value ∧
      result = (install state tid state.world
        { worker with context := .ofCPU (
          { (localCPU state worker).writeRegister destination value with
            rip := (localCPU state worker).rip +
              BitVec.ofNat 64 (Sequential.Instruction.loadMem64 destination address).length }) },
        .ordinary tid) := by
  obtain ⟨value, loaded, _, installed⟩ := effect.loadMem64
  rw [← operand] at loaded
  have source := local_managed_load (profile := profile) valid
    (valid.2 worker (List.mem_of_getElem? live)) current
  exact ⟨value, loaded, source.symm.trans loaded, installed⟩

/-- A successful production intent has EXACTLY one of the original width
classifications, with the address/value taken from the actual prestate. -/
theorem storeIntent_origin {instruction : Sequential.Instruction} {initial : X86.State} {store : Store}
    (intent : storeIntent instruction initial = some store) :
    (∃ value, store.value = .qword value ∧ instruction.storeIntent64 initial = some (store.address, value)) ∨
    (∃ value, store.value = .dword value ∧ instruction.storeIntent initial = some (store.address, value)) := by
  cases full : instruction.storeIntent64 initial with
  | some pair =>
    simp only [storeIntent, full, Option.some.injEq] at intent
    subst store
    exact Or.inl ⟨pair.2, rfl, rfl⟩
  | none =>
    cases narrow : instruction.storeIntent initial with
    | none => simp [storeIntent, full, narrow] at intent
    | some pair =>
      simp only [storeIntent, full, narrow, Option.map_some, Option.some.injEq] at intent
      subst store
      exact Or.inr ⟨pair.2, rfl, rfl⟩

theorem payload_enqueue (pending : List Pending) (entry : Pending) :
    payload (pending ++ [entry]) = StoreBuffer.Mixed.enqueue (payload pending) entry.store := by
  simp [payload, Queue.payload, StoreBuffer.Mixed.enqueue]

/-- Even an RSP-changing instruction grants no replacement caller slot. -/
theorem changed_rsp_ret_denied (state : State) (worker : Worker)
    (different : worker.context.registers .rsp ≠ worker.resources.callerAddress)
    (profile : Profile := .ownedOnly) :
    checkRead state worker ⟨.stack, worker.context.registers .rsp, 8⟩ profile = .error .callerSlot := by
  simp [checkRead, different]

end EDSL.OS.TSO64
