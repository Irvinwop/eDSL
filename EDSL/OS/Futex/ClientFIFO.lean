/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientModel

namespace EDSL.OS.Futex.Clients
open X86

def PayloadRole (role : Role) : Prop := role = .publishPayloadWake ∨ role = .payloadPeer

theorem Stage.fifo_shape {client : Client} {stage : Stage} {memory : Memory} {buffer : StoreBuffer.Buffer}
    (fifo : stage.FIFO client memory buffer) :
    buffer = [] ∨ (PayloadRole client.role ∧ buffer = [client.store]) := by
  cases role : client.role with
  | wait expected =>
    cases stage <;> simp only [Stage.FIFO, Stage.bufferCondition, role] at fifo <;> exact Or.inl fifo
  | publishPayloadWake =>
    have publisher : PayloadRole .publishPayloadWake := Or.inl rfl
    cases stage <;> simp only [Stage.FIFO, Stage.bufferCondition, role] at fifo
    all_goals first
      | exact Or.inl fifo
      | exact Or.inl fifo.1
      | exact fifo.elim (fun full => Or.inr ⟨publisher, full⟩) (fun empty => Or.inl empty.1)
  | payloadPeer =>
    have peer : PayloadRole .payloadPeer := Or.inr rfl
    cases stage <;> simp only [Stage.FIFO, Stage.bufferCondition, role] at fifo
    all_goals first
      | exact Or.inl fifo
      | exact fifo.elim Or.inl (fun full => Or.inr ⟨peer, full⟩)

theorem WorkerControl.fifo_shape {client : Client} {worker : Nat} {state : Suspend.State} {actual : TSO.Worker}
    (control : WorkerControl client worker state actual) :
    actual.buffer = [] ∨ (PayloadRole client.role ∧ actual.buffer = [client.store]) := by
  cases control with
  | running stage supported context live free fifo => exact Stage.fifo_shape fifo
  | entered saved pending owner family context live empty published => exact Or.inl empty
  | resumed outcome flags rcx r11 caller context live free empty published => exact Or.inl empty
  | returned outcome flags rcx r11 caller context done free empty published => exact Or.inl empty
  | peerReturned peer context done free fifo =>
    exact fifo.elim Or.inl (fun full => Or.inr ⟨Or.inr peer, full⟩)

theorem WorkerControl.queued_store {client : Client} {worker : Nat} {state : Suspend.State}
    {actual : TSO.Worker} (control : WorkerControl client worker state actual)
    {store : StoreBuffer.Store} (queued : store ∈ actual.buffer) :
    PayloadRole client.role ∧ store = client.store := by
  rcases control.fifo_shape with empty | ⟨role, full⟩
  · simp [empty] at queued
  · exact ⟨role, List.mem_singleton.mp (full ▸ queued)⟩

/-- All buffered stores have current managed authority, including stores held
by a worker which has already returned. This follows from exact current
control and grants, rather than assumed future drain/replay success. -/
theorem Control.fifo_authorized {cohort : Cohort} {state : State}
    (control : Control cohort state.suspended) (static : Static cohort)
    (payload : ∀ worker grant, cohort.profile.payload worker = some grant → grant.Valid state.authority) :
    FIFOAuthorized cohort state := by
  intro worker actual live store queued
  obtain ⟨client, atClient, controlled⟩ := control worker actual live
  obtain ⟨hasPayload, exactStore⟩ := controlled.queued_store queued
  obtain ⟨_, _, _, _, descriptor⟩ := static.descriptors worker client atClient
  rcases hasPayload with publisher | peer
  · rw [publisher] at descriptor
    obtain ⟨grant, atGrant, address⟩ := descriptor.1
    exact ⟨grant, atGrant, by rw [exactStore]; exact address, payload worker grant atGrant⟩
  · rw [peer] at descriptor
    obtain ⟨grant, atGrant, address⟩ := descriptor.1
    exact ⟨grant, atGrant, by rw [exactStore]; exact address, payload worker grant atGrant⟩

end EDSL.OS.Futex.Clients
