/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientModel

set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

namespace EDSL.OS.Futex.Clients
open X86 AddressSpace

/-- The real shared-memory decoder identifies the instruction. Expected
locations and bytes occur only as hypotheses of this theorem. -/
theorem decode_stage (client : Client) (stage : Stage) (memory : Memory)
    (supported : stage.Valid client.role)
    (code : CodeAt memory client.entry.rip client.role.bytes) :
    decodeAt (MachineThreads.contextState (stage.context client) memory) =
      .ok (stage.instruction client.role) := by
  cases role : client.role with
  | wait expected =>
    have b0 := code.2 0 184 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b1 := code.2 1 202 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b2 := code.2 2 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b3 := code.2 3 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b4 := code.2 4 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b5 := code.2 5 190 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b6 := code.2 6 128 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b7 := code.2 7 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b8 := code.2 8 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b9 := code.2 9 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b10 := code.2 10 15 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b11 := code.2 11 5 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b12 := code.2 12 195 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
    cases stage <;> try { simp [Stage.Valid, role] at supported }
    all_goals simp [MachineThreads.contextState, Stage.context, Stage.offset, Stage.instruction,
      role, Role.value, decodeAt, BitVec.add_assoc, joinDWord,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]
  | publishPayloadWake =>
    have b0 := code.2 0 184 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b1 := code.2 1 68 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b2 := code.2 2 51 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b3 := code.2 3 34 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b4 := code.2 4 17 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b5 := code.2 5 137 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b6 := code.2 6 6 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b7 := code.2 7 184 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b8 := code.2 8 1 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b9 := code.2 9 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b10 := code.2 10 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b11 := code.2 11 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b12 := code.2 12 135 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b13 := code.2 13 7 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b14 := code.2 14 184 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b15 := code.2 15 202 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b16 := code.2 16 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b17 := code.2 17 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b18 := code.2 18 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b19 := code.2 19 190 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b20 := code.2 20 129 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b21 := code.2 21 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b22 := code.2 22 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b23 := code.2 23 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b24 := code.2 24 186 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b25 := code.2 25 1 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b26 := code.2 26 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b27 := code.2 27 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b28 := code.2 28 0 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b29 := code.2 29 15 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b30 := code.2 30 5 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b31 := code.2 31 195 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31
    cases stage <;> try { simp [Stage.Valid, role] at supported }
    all_goals simp [MachineThreads.contextState, Stage.context, Stage.offset, Stage.instruction,
      role, Role.value, decodeAt, BitVec.add_assoc, joinDWord,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]
  | payloadPeer =>
    have b0 := code.2 0 184 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b1 := code.2 1 136 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b2 := code.2 2 119 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b3 := code.2 3 102 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b4 := code.2 4 85 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b5 := code.2 5 137 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b6 := code.2 6 6 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    have b7 := code.2 7 195 (by simp [role, Role.bytes, publishingBytes, peerBytes, Examples.FutexStubs.Profile.bytes])
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1 b2 b3 b4 b5 b6 b7
    cases stage <;> try { simp [Stage.Valid, role] at supported }
    all_goals simp [MachineThreads.contextState, Stage.context, Stage.offset, Stage.instruction,
      role, Role.value, decodeAt, BitVec.add_assoc, joinDWord,
      b0, b1, b2, b3, b4, b5, b6, b7]

theorem decode_resumed (client : Client) (memory : Memory) (raw flags rcx r11 : Word)
    (caller : client.role ≠ .payloadPeer)
    (code : CodeAt memory client.entry.rip client.role.bytes) :
    decodeAt (MachineThreads.contextState (client.resumed raw flags rcx r11) memory) = .ok .ret := by
  cases role : client.role with
  | wait expected =>
    have byte := code.2 12 0xc3 (by simp [role, Role.bytes, Examples.FutexStubs.Profile.bytes])
    simp [Client.resumed, Client.callContext, Client.callStage, Stage.context, Stage.offset,
      role, MachineThreads.contextState, decodeAt, BitVec.add_assoc, byte]
  | publishPayloadWake =>
    have byte := code.2 31 0xc3 (by simp [role, Role.bytes, publishingBytes, Examples.FutexStubs.Profile.bytes])
    simp [Client.resumed, Client.callContext, Client.callStage, Stage.context, Stage.offset,
      role, MachineThreads.contextState, decodeAt, BitVec.add_assoc, byte]
  | payloadPeer => exact (caller role).elim

theorem stage_store {client : Client} {stage : Stage} {store : StoreBuffer.Store}
    (supported : stage.Valid client.role)
    (intent : TSO.pendingStore (stage.context client) (stage.instruction client.role) = some store) :
    (client.role = .publishPayloadWake ∨ client.role = .payloadPeer) ∧ store = client.store := by
  cases role : client.role <;> cases stage <;>
    simp [Stage.Valid, Stage.instruction, TSO.pendingStore, role] at supported intent
  all_goals
    subst store
    simp [Client.store, Stage.context, Role.value, role]

theorem stage_locked {client : Client} {stage : Stage}
    (supported : stage.Valid client.role) (locked : TSO.locked (stage.instruction client.role) = true) :
    client.role = .publishPayloadWake ∧ stage = .exchange ∧
      (stage.context client).registers .rdi = client.entry.registers .rdi ∧
      (stage.context client).registers .rax = 1 ∧ stage.instruction client.role = .exchangeEaxRdi := by
  cases role : client.role <;> cases stage <;>
    simp [Stage.Valid, Stage.instruction, TSO.locked, role] at supported locked
  simp [role, Stage.context, Stage.instruction]

theorem stage_syscall {client : Client} {stage : Stage}
    (supported : stage.Valid client.role) (syscall : stage.instruction client.role = .syscall) :
    client.role ≠ .payloadPeer ∧ stage.context client = client.callContext := by
  cases role : client.role <;> cases stage <;>
    simp [Stage.Valid, Stage.instruction, role] at supported syscall
  all_goals simp [Client.callContext, Client.callStage, role]

/-- Each exact request satisfies the canonical full-width syscall ABI. -/
theorem family_classifies {cohort : Cohort} {worker : Nat} {client : Client}
    {request : SyscallRequest} (descriptor : Descriptor cohort worker client)
    (family : client.Family request) :
    classify request = .ok client.operation ∧
      request.user.registers .rdi = cohort.registration.address := by
  obtain ⟨caller, same⟩ := family
  obtain ⟨address, fourth, fifth, sixth, rest⟩ := descriptor
  rw [same]
  cases role : client.role with
  | wait expected =>
    simp only [role] at rest
    simp [Client.request, Client.callContext, Client.callStage, Stage.context, Stage.offset,
      Client.operation, role, classify, MachineThreads.contextState, address, fourth, fifth, sixth, rest.1]
  | publishPayloadWake =>
    simp [Client.request, Client.callContext, Client.callStage, Stage.context, Stage.offset,
      Client.operation, role, classify, MachineThreads.contextState, address, fourth, fifth, sixth]
  | payloadPeer => exact (caller role).elim

theorem family_resume {client : Client} {request : SyscallRequest} (family : client.Family request)
    (memory : Memory) (raw flags rcx r11 : Word) :
    Threads.Context.ofState (X86.resumeAt request memory raw flags rcx r11) =
      client.resumed raw flags rcx r11 := by
  rw [family.2]
  rfl

theorem Stage.FIFO.frame {client : Client} {stage : Stage} {before after : Memory}
    {buffer : StoreBuffer.Buffer}
    (fifo : stage.FIFO client before buffer)
    (frame : client.Published before → client.Published after) :
    stage.FIFO client after buffer := by
  cases role : client.role <;> cases stage <;>
    simp only [Stage.FIFO, Stage.bufferCondition, role] at fifo ⊢
  all_goals first
    | exact fifo
    | exact ⟨fifo.1, frame fifo.2⟩
    | exact fifo.elim Or.inl (fun current => Or.inr ⟨current.1, frame current.2⟩)

theorem WorkerControl.frame {client : Client} {worker : Nat} {before after : Suspend.State}
    {actual : TSO.Worker} (control : WorkerControl client worker before actual)
    (pending : after.pending worker = before.pending worker)
    (frame : client.Published before.machine.memory → client.Published after.machine.memory) :
    WorkerControl client worker after actual := by
  cases control with
  | running stage supported context live free fifo =>
    exact .running stage supported context live (pending.trans free) (fifo.frame frame)
  | entered saved savedAt owner family context live empty published =>
    exact .entered saved (pending.trans savedAt) owner family context live empty (frame published)
  | resumed outcome flags rcx r11 caller context live free empty published =>
    exact .resumed outcome flags rcx r11 caller context live (pending.trans free) empty (frame published)
  | returned outcome flags rcx r11 caller context done free empty published =>
    exact .returned outcome flags rcx r11 caller context done (pending.trans free) empty (frame published)
  | peerReturned peer context done free fifo =>
    exact .peerReturned peer context done (pending.trans free) fifo

theorem Control.pending_family {cohort : Cohort} {state : Suspend.State}
    (control : Control cohort state) {worker : Nat} {actual : TSO.Worker} {saved : Suspend.Saved}
    (live : state.machine.workers[worker]? = some actual) (pending : state.pending worker = some saved) :
    CallFamily cohort worker saved.request := by
  obtain ⟨client, atClient, controlled⟩ := control worker actual live
  refine ⟨client, atClient, ?_⟩
  cases controlled with
  | running _ _ _ _ free _ => simp [free] at pending
  | resumed _ _ _ _ _ _ _ free _ _ => simp [free] at pending
  | returned _ _ _ _ _ _ _ free _ _ => simp [free] at pending
  | peerReturned _ _ _ free _ => simp [free] at pending
  | entered captured savedAt _ family _ _ _ _ =>
    cases Option.some.inj (savedAt.symm.trans pending)
    exact family

end EDSL.OS.Futex.Clients
