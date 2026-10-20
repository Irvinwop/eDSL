/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Model

namespace EDSL.OS.TSO64
open X86 AddressSpace

instance (world : World) (resources : Resources) : Decidable (ResourcesValid world resources) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ (∀ ticket ∈ resources.grants, _) ∧ (∀ identifier ∈ resources.atomics, _)))

/-- Attach existing checked current resources. This neither invents loans nor
captures a RAM snapshot, and does not select or certify a function body. Atomic
handles are checked when the actual operand selects them. -/
def makeWorker (world : World) (actor : Nat) (entry : Context) (codeId callerId : Nat)
    (grants : List Ownership.Ticket) (atomics : List Atomics64.HandleId64) : Except Fault Worker := do
  let code ← (Borrowing.authorize world.legacy.shared actor codeId).mapError Fault.loan
  let caller ← (Borrowing.authorize world.legacy.shared actor callerId).mapError Fault.loan
  let resources : Resources := ⟨actor, ⟨codeId, code⟩, ⟨callerId, caller⟩,
    entry.registers .rsp, grants, atomics⟩
  if ResourcesValid world resources then return ⟨entry, resources, .running, []⟩
  else throw .resource

def attach (state : State) (actor : Nat) (entry : Context) (codeId callerId : Nat)
    (grants : List Ownership.Ticket) (atomics : List Atomics64.HandleId64) : Except Fault State := do
  let worker ← makeWorker state.world actor entry codeId callerId grants atomics
  return ⟨state.world, state.workers ++ [worker]⟩

/-- Resource validity does not promise that the next instruction or RET will
succeed. In particular, it permits changed RSP and returned RIP; their actual
access checks occur at issue, against the original retained resources. -/
def WorkerValid (world : World) (worker : Worker) : Prop :=
  ResourcesValid world worker.resources ∧ ∀ pending ∈ worker.pending, PendingValid world worker.resources pending

def WellFormed (state : State) : Prop :=
  Atomics64.WellFormed state.world ∧ ∀ worker ∈ state.workers, WorkerValid state.world worker

theorem makeWorker_valid {world : World} {actor : Nat} {entry : Context} {codeId callerId : Nat}
    {grants : List Ownership.Ticket} {atomics : List Atomics64.HandleId64} {worker : Worker}
    (success : makeWorker world actor entry codeId callerId grants atomics = .ok worker) :
    WorkerValid world worker ∧ worker.phase = .running ∧ worker.pending = [] ∧ worker.context = entry := by
  cases code : Borrowing.authorize world.legacy.shared actor codeId with
  | error fault => simp [makeWorker, code, Except.mapError] at success
  | ok codeLoan =>
    cases caller : Borrowing.authorize world.legacy.shared actor callerId with
    | error fault => simp [makeWorker, code, caller, Except.mapError] at success
    | ok callerLoan =>
      dsimp only [makeWorker] at success
      simp only [code, caller, Except.mapError, ok_bind] at success
      split at success
      next valid =>
        simp only [pure_ok, Except.ok.injEq] at success
        subst worker
        exact ⟨⟨valid, by simp⟩, rfl, rfl, rfl⟩
      next => cases success

theorem attach_valid {state : State} {actor : Nat} {entry : Context} {codeId callerId : Nat}
    {grants : List Ownership.Ticket} {atomics : List Atomics64.HandleId64} {after : State}
    (valid : WellFormed state)
    (success : attach state actor entry codeId callerId grants atomics = .ok after) : WellFormed after := by
  cases made : makeWorker state.world actor entry codeId callerId grants atomics with
  | error fault => simp [attach, made] at success
  | ok worker =>
    simp only [attach, made, ok_bind, pure_ok, Except.ok.injEq] at success
    subst after
    refine ⟨valid.1, ?_⟩
    intro other member
    rcases List.mem_append.mp member with old | fresh
    · exact valid.2 other old
    · have same := List.mem_singleton.mp fresh
      subst other
      exact (makeWorker_valid made).1

/-- Collection is a read-only observation. No loans/tickets are released by
this fixed-world API. Both RET and own publication are required. -/
def collect (state : State) (tid : Nat) : Except Fault Word := do
  let some worker := state.workers[tid]? | throw .missingWorker
  if worker.phase ≠ .returned ∨ ¬worker.pending.isEmpty then throw .resource
  return worker.context.registers .rax

theorem collect_ready {state : State} {tid : Nat} {value : Word}
    (success : collect state tid = .ok value) :
    ∃ worker, state.workers[tid]? = some worker ∧ worker.phase = .returned ∧
      worker.pending = [] ∧ value = worker.context.registers .rax := by
  cases live : state.workers[tid]? with
  | none => simp [collect, live] at success
  | some worker =>
    by_cases ready : worker.phase = .returned ∧ worker.pending.isEmpty = true
    · simp [collect, live, ready.1, ready.2] at success
      exact ⟨worker, rfl, ready.1, List.isEmpty_iff.mp ready.2, success.symm⟩
    · by_cases phase : worker.phase = .returned
      · have pending : worker.pending.isEmpty ≠ true := fun empty => ready ⟨phase, empty⟩
        simp [collect, live, phase, pending] at success
      · simp [collect, live, phase] at success

end EDSL.OS.TSO64
