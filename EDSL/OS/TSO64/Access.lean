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

def ReadCurrent (state : State) (worker : Worker) (read : Sequential.Read) : Prop :=
  match read.kind with
  | .stack => read.address = worker.resources.callerAddress ∧ read.bytes = 8 ∧
      ∃ value, Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
        worker.resources.caller.identifier read.address = .ok value
  | .data =>
      (read.bytes = 4 ∧ ∃ ticket, ticket ∈ worker.resources.grants ∧
        StoreGate state.world worker.resources.actor ticket ⟨read.address, .dword 0⟩) ∨
      (read.bytes = 8 ∧ ∃ ticket, ticket ∈ worker.resources.grants ∧
        StoreGate state.world worker.resources.actor ticket ⟨read.address, .qword 0⟩)

theorem checkRead_current {state : State} {worker : Worker} {read : Sequential.Read}
    (success : checkRead state worker read = .ok ()) : ReadCurrent state worker read := by
  cases read with
  | mk kind address width =>
    cases kind with
    | stack => exact checkRead_stack success
    | data => exact checkRead_data success

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
    (effect : OrdinaryEffect state tid worker instruction af result) :
    ∃ observation, Sequential.step af (localCPU state worker) = .ok observation ∧
      ∀ read ∈ observation.reads, ReadCurrent state worker read ∧
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
    exact ⟨checkRead_current current, Sequential.observed_reads_succeed step read member⟩

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
  simp [payload, StoreBuffer.Mixed.enqueue]

/-- Even an RSP-changing instruction grants no replacement caller slot. -/
theorem changed_rsp_ret_denied (state : State) (worker : Worker)
    (different : worker.context.registers .rsp ≠ worker.resources.callerAddress) :
    checkRead state worker ⟨.stack, worker.context.registers .rsp, 8⟩ = .error .callerSlot := by
  simp [checkRead, different]

end EDSL.OS.TSO64
