/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexTSO.Queues

namespace EDSL.OS.MutexTSO
open X86

/-- The target profile depends on the exact current execute permissions. -/
theorem Profile.frame {config : Mutex.Config} {memory after : Memory}
    (profile : Profile config memory) (executable : after.executable = memory.executable) :
    Profile config after := by
  refine ⟨profile.payload, ?_, ?_⟩
  · simpa only [TSO.dataOnly, executable] using profile.lockData
  · simpa only [TSO.dataOnly, executable] using profile.payloadData

theorem Profile.write {config : Mutex.Config} {memory : Memory}
    (profile : Profile config memory) (address : Word) (value : BitVec 32) :
    Profile config (writeDWordUnchecked memory address value) :=
  profile.frame rfl

namespace Rel
variable {config : Mutex.Config} {physical : Physical} {logical : Logical}

/-- The cohort indices agree, including the empty cohort. -/
theorem length (rel : Rel config physical logical) :
    physical.workers.length = logical.workers.length := by
  simpa only [List.length_map] using congrArg List.length rel.contexts

/-- Matching retains the entire Context and the actual returned marker. -/
theorem match_workers (rel : Rel config physical logical)
    {identifier : Nat} {before : TSO.Worker} {after : MutexReplay.Worker}
    (physicalLive : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some after) :
    before.context = after.context ∧ before.returned = decide (after.phase = .completed) := by
  have equal := congrArg (fun workers => workers[identifier]?) rel.contexts
  simp only [List.getElem?_map, physicalLive, logicalLive, Option.map_some, Option.some.injEq] at equal
  exact ⟨congrArg MachineThreads.Worker.context equal, congrArg MachineThreads.Worker.returned equal⟩

theorem physical_live (rel : Rel config physical logical) {identifier : Nat} {before : TSO.Worker}
    (live : physical.workers[identifier]? = some before) :
    ∃ after, logical.workers[identifier]? = some after ∧ before.context = after.context ∧
      before.returned = decide (after.phase = .completed) := by
  have equal := congrArg (fun workers => workers[identifier]?) rel.contexts
  cases found : logical.workers[identifier]? with
  | none => simp [List.getElem?_map, live, found] at equal
  | some after => exact ⟨after, rfl, rel.match_workers live found⟩

theorem logical_live (rel : Rel config physical logical) {identifier : Nat} {after : MutexReplay.Worker}
    (live : logical.workers[identifier]? = some after) :
    ∃ before, physical.workers[identifier]? = some before ∧ before.context = after.context ∧
      before.returned = decide (after.phase = .completed) := by
  have equal := congrArg (fun workers => workers[identifier]?) rel.contexts
  cases found : physical.workers[identifier]? with
  | none => simp [List.getElem?_map, live, found] at equal
  | some before => exact ⟨before, rfl, rel.match_workers found live⟩

theorem unfinished (rel : Rel config physical logical)
    {identifier : Nat} {before : TSO.Worker} {after : MutexReplay.Worker}
    (physicalLive : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some after) (unreturned : before.returned = false) :
    after.phase ≠ .completed := by
  intro completed
  have returned := (rel.match_workers physicalLive logicalLive).2
  simp [completed, unreturned] at returned

/-- Two separately checked guards refer to the same actor and lease.
Principal injectivity then recovers the actual worker index. -/
theorem guard_exclusive (rel : Rel config physical logical)
    {identifier query : Nat} {worker peer : MutexReplay.Worker} {lease other : Mutex.Lease}
    (live : logical.workers[identifier]? = some worker)
    (peerLive : logical.workers[query]? = some peer)
    (guard : worker.guard = some lease) (peerGuard : peer.guard = some other) :
    identifier = query ∧ lease = other := by
  obtain ⟨first, authorized, _⟩ := (rel.invariant.workers identifier worker live).authority lease guard
  obtain ⟨second, otherAuthorized, _⟩ := (rel.invariant.workers query peer peerLive).authority other peerGuard
  have exclusive := Mutex.exclusive _ _ _ _ _ _ _ authorized otherAuthorized
  exact ⟨Nat.add_right_cancel exclusive.2, exclusive.1⟩

theorem guard_holder (rel : Rel config physical logical)
    {identifier : Nat} {worker : MutexReplay.Worker} {lease : Mutex.Lease}
    (live : logical.workers[identifier]? = some worker) (guard : worker.guard = some lease) :
    ∃ record, logical.shared.mutex = some record ∧ record.holder = some lease ∧
      lease.actor = MutexReplay.principal identifier ∧ record.config = config := by
  obtain ⟨record, checked, same⟩ := (rel.invariant.workers identifier worker live).authority lease guard
  obtain ⟨found, held, actor⟩ := Mutex.authorize_ok _ _ _ _ checked
  exact ⟨record, found, held, actor, same⟩

theorem nonempty_guard (rel : Rel config physical logical) {identifier : Nat} {before : TSO.Worker}
    (live : physical.workers[identifier]? = some before) (nonempty : before.buffer ≠ []) :
    ∃ after lease, logical.workers[identifier]? = some after ∧ after.guard = some lease := by
  obtain ⟨after, found, _, _⟩ := rel.physical_live live
  cases guard : after.guard with
  | none => exact False.elim (nonempty (rel.unguarded identifier before after live found guard))
  | some lease => exact ⟨after, lease, found, guard⟩

/-- Queue exclusivity is derived from authority, rather than assumed by Rel. -/
theorem peers_empty (rel : Rel config physical logical)
    {identifier : Nat} {worker : MutexReplay.Worker} {lease : Mutex.Lease}
    (live : logical.workers[identifier]? = some worker) (guard : worker.guard = some lease) :
    ∀ query peer, physical.workers[query]? = some peer → identifier ≠ query → peer.buffer = [] := by
  intro query peer peerLive different
  obtain ⟨after, found, _, _⟩ := rel.physical_live peerLive
  cases peerGuard : after.guard with
  | none => exact rel.unguarded query peer after peerLive found peerGuard
  | some other => exact False.elim (different (rel.guard_exclusive live found guard peerGuard).1)

theorem one_queue (rel : Rel config physical logical)
    {identifier query : Nat} {worker peer : TSO.Worker}
    (live : physical.workers[identifier]? = some worker)
    (peerLive : physical.workers[query]? = some peer)
    (nonempty : worker.buffer ≠ []) (peerNonempty : peer.buffer ≠ []) : identifier = query := by
  obtain ⟨after, lease, found, guard⟩ := rel.nonempty_guard live nonempty
  by_cases same : identifier = query
  · exact same
  · exact False.elim (peerNonempty (rel.peers_empty found guard query peer peerLive same))

theorem pending_eq (rel : Rel config physical logical)
    {identifier : Nat} {before : TSO.Worker} {after : MutexReplay.Worker} {lease : Mutex.Lease}
    (physicalLive : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some after) (guard : after.guard = some lease) :
    pending physical = before.buffer :=
  pending_eq_of_peers physicalLive (rel.peers_empty logicalLive guard)

theorem guarded_empty (rel : Rel config physical logical)
    {identifier : Nat} {before : TSO.Worker} {after : MutexReplay.Worker} {lease : Mutex.Lease}
    (physicalLive : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some after) (guard : after.guard = some lease)
    (empty : before.buffer = []) : TSO.Quiescent physical := by
  intro peer member
  obtain ⟨query, found⟩ := List.mem_iff_getElem?.mp member
  by_cases selected : identifier = query
  · subst query
    have same := Option.some.inj (physicalLive.symm.trans found)
    exact same ▸ empty
  · exact rel.peers_empty logicalLive guard query peer found selected

theorem guarded_view (rel : Rel config physical logical)
    {identifier : Nat} {before : TSO.Worker} {after : MutexReplay.Worker} {lease : Mutex.Lease}
    (physicalLive : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some after) (guard : after.guard = some lease) :
    logicalMemory logical = StoreBuffer.view physical.memory before.buffer := by
  rw [rel.memory, overlay, rel.pending_eq physicalLive logicalLive guard]

/-- A free registered mutex cannot have a pending physical write. -/
theorem free (rel : Rel config physical logical) {record : Mutex.Registered}
    (registered : logical.shared.mutex = some record) (unheld : record.holder = none) :
    TSO.Quiescent physical := by
  intro before member
  obtain ⟨identifier, live⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨after, found, _, _⟩ := rel.physical_live live
  cases guard : after.guard with
  | none => exact rel.unguarded identifier before after live found guard
  | some lease =>
    obtain ⟨authorized, checked, _⟩ := (rel.invariant.workers identifier after found).authority lease guard
    obtain ⟨current, holder, _⟩ := Mutex.authorize_ok _ _ _ _ checked
    have same := Option.some.inj (current.symm.trans registered)
    rw [same, unheld] at holder
    cases holder

theorem all_unguarded (rel : Rel config physical logical)
    (unguarded : ∀ worker ∈ logical.workers, worker.guard = none) : TSO.Quiescent physical := by
  intro worker member
  obtain ⟨identifier, live⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨after, found, _, _⟩ := rel.physical_live live
  exact rel.unguarded identifier worker after live found (unguarded after (List.mem_of_getElem? found))

/-- Tracked identifies the holder's actual worker even if its queue is empty. -/
theorem holder (rel : Rel config physical logical) {record : Mutex.Registered} {lease : Mutex.Lease}
    (registered : logical.shared.mutex = some record) (held : record.holder = some lease) :
    ∃ (identifier : Nat) (before : TSO.Worker) (after : MutexReplay.Worker), physical.workers[identifier]? = some before ∧
      logical.workers[identifier]? = some after ∧ after.guard = some lease := by
  obtain ⟨identifier, after, found, guard⟩ := rel.invariant.tracked record lease registered held
  obtain ⟨before, live, _, _⟩ := rel.logical_live found
  exact ⟨identifier, before, after, live, found, guard⟩

theorem returned_empty (rel : Rel config physical logical) {identifier : Nat} {before : TSO.Worker}
    (live : physical.workers[identifier]? = some before) (returned : before.returned = true) :
    before.buffer = [] := by
  obtain ⟨after, found, _, marked⟩ := rel.physical_live live
  have completed : after.phase = .completed := of_decide_eq_true (returned ▸ marked.symm)
  have control := (rel.invariant.workers identifier after found).control
  simp only [MutexReplay.Control, completed] at control
  have guard : after.guard = none := control.1
  exact rel.unguarded identifier before after live found guard

theorem returned_quiescent (rel : Rel config physical logical) (returned : TSO.Returned physical) :
    TSO.Quiescent physical := by
  intro worker member
  obtain ⟨identifier, live⟩ := List.mem_iff_getElem?.mp member
  exact rel.returned_empty live (returned worker member)

theorem returned_finished (rel : Rel config physical logical) (returned : TSO.Returned physical) :
    MutexReplay.Finished logical := by
  intro identifier after found
  obtain ⟨before, live, _, marked⟩ := rel.logical_live found
  exact of_decide_eq_true ((returned before (List.mem_of_getElem? live)) ▸ marked.symm)

/-- Actual RET markers suffice; publication is derived separately. -/
theorem returned (rel : Rel config physical logical) (actual : TSO.Returned physical) :
    MutexReplay.Finished logical :=
  rel.returned_finished actual

theorem finished_returned (rel : Rel config physical logical) (finished : MutexReplay.Finished logical) :
    TSO.Returned physical := by
  intro worker member
  obtain ⟨identifier, live⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨after, found, _, marked⟩ := rel.physical_live live
  rw [marked, finished identifier after found]
  rfl

theorem returned_iff (rel : Rel config physical logical) :
    TSO.Returned physical ↔ MutexReplay.Finished logical :=
  ⟨rel.returned, rel.finished_returned⟩

theorem finished (rel : Rel config physical logical) (finished : TSO.Finished physical) :
    MutexReplay.Finished logical :=
  rel.returned_finished finished.1

theorem finished_iff (rel : Rel config physical logical) :
    TSO.Finished physical ↔ MutexReplay.Finished logical := by
  constructor
  · exact rel.finished
  · intro finished
    have returned := rel.finished_returned finished
    exact ⟨returned, rel.returned_quiescent returned⟩

theorem returning_empty (rel : Rel config physical logical)
    {identifier : Nat} {before : TSO.Worker} {after : MutexReplay.Worker}
    (physicalLive : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some after) (phase : after.phase = .returning) :
    before.buffer = [] := by
  have control := (rel.invariant.workers identifier after logicalLive).control
  simp only [MutexReplay.Control, phase] at control
  exact rel.unguarded identifier before after physicalLive logicalLive control.1

theorem quiescent_memory (rel : Rel config physical logical) (empty : TSO.Quiescent physical) :
    physical.memory = logicalMemory logical := by
  rw [rel.memory, overlay, pending_nil empty, StoreBuffer.view_nil]

theorem physicalErase_quiescent (rel : Rel config physical logical) (empty : TSO.Quiescent physical) :
    physicalErase physical = MutexReplay.erase logical := by
  change MachineThreads.State.mk physical.memory _ = MachineThreads.State.mk (logicalMemory logical) _
  rw [rel.quiescent_memory empty, rel.contexts]

/-- The flattened queue inherits checkedness from the actual constituent queues. -/
theorem pending_valid (rel : Rel config physical logical) :
    ∀ store ∈ pending physical, TSO.StoreValid physical.memory store := by
  intro store member
  obtain ⟨worker, live, queued⟩ := List.mem_flatMap.mp member
  exact rel.buffers worker live store queued

theorem pending_payloads (rel : Rel config physical logical) :
    ∀ store ∈ pending physical, store.address = config.dataAddress := by
  intro store member
  obtain ⟨worker, live, queued⟩ := List.mem_flatMap.mp member
  exact rel.payloads worker live store queued

theorem frame (rel : Rel config physical logical) :
    TSO.MemoryFrame physical.memory (logicalMemory logical) := by
  rw [rel.memory]
  exact TSO.MemoryFrame.view _ _ rel.pending_valid

theorem executable (rel : Rel config physical logical) :
    (logicalMemory logical).executable = physical.memory.executable := rel.frame.executable

theorem writable (rel : Rel config physical logical) :
    (logicalMemory logical).writable = physical.memory.writable := rel.frame.writable

theorem readable (rel : Rel config physical logical) (address : Word) :
    ((logicalMemory logical).read address).isSome = (physical.memory.read address).isSome :=
  rel.frame.readable address

theorem logical_profile (rel : Rel config physical logical) : Profile config (logicalMemory logical) :=
  rel.profile.frame rel.executable

theorem canStore (rel : Rel config physical logical) (address : Word) :
    canStoreDWord (logicalMemory logical) address = canStoreDWord physical.memory address :=
  rel.frame.canStore address

theorem fetch (rel : Rel config physical logical) (address : Word) :
    fetchByte (logicalMemory logical) address = fetchByte physical.memory address :=
  rel.frame.fetch address

theorem lock (rel : Rel config physical logical) :
    loadDWord (logicalMemory logical) config.lockAddress = loadDWord physical.memory config.lockAddress := by
  rw [rel.memory]
  exact rel.invariant.buffer_lock _ _ rel.pending_payloads

theorem lock_agrees (rel : Rel config physical logical) :
    MemoryAgreesOn (logicalMemory logical) physical.memory config.lockAddress 4 := by
  rw [rel.memory]
  apply StoreBuffer.view_agrees
  intro store member
  rw [rel.pending_payloads store member]
  exact rel.invariant.data_lock_disjoint

theorem lock_local (rel : Rel config physical logical) {identifier : Nat} {worker : TSO.Worker}
    (live : physical.workers[identifier]? = some worker) :
    loadDWord (StoreBuffer.view physical.memory worker.buffer) config.lockAddress =
      loadDWord physical.memory config.lockAddress :=
  rel.invariant.buffer_lock _ _ (rel.payloads worker (List.mem_of_getElem? live))

theorem code_agrees (rel : Rel config physical logical) {identifier : Nat} {worker : MutexReplay.Worker}
    (live : logical.workers[identifier]? = some worker) :
    MemoryAgreesOn (logicalMemory logical) physical.memory worker.entry.rip MutexReplay.bytes.length := by
  rw [rel.memory]
  exact (rel.invariant.worker_footprints rel.ready live).buffer_agrees_code _ _ rel.pending_payloads

/-- The immutable worker image holds in physical shared RAM. -/
theorem code_global (rel : Rel config physical logical) {identifier : Nat} {worker : MutexReplay.Worker}
    (live : logical.workers[identifier]? = some worker) :
    CodeAt physical.memory worker.entry.rip MutexReplay.bytes := by
  have code := (rel.ready identifier worker live).code
  exact ⟨code.1, fun offset byte found => (rel.fetch _).symm.trans (code.2 offset byte found)⟩

theorem code_local (rel : Rel config physical logical) {identifier query : Nat}
    {worker : MutexReplay.Worker} {before : TSO.Worker}
    (live : logical.workers[identifier]? = some worker)
    (physicalLive : physical.workers[query]? = some before) :
    CodeAt (StoreBuffer.view physical.memory before.buffer) worker.entry.rip MutexReplay.bytes :=
  (rel.buffers.local_frame (List.mem_of_getElem? physicalLive)).codeAt (rel.code_global live)

/-- The entire eight-byte saved return read agrees, including high canonical addresses. -/
theorem stack_global (rel : Rel config physical logical) {identifier : Nat} {worker : MutexReplay.Worker}
    (live : logical.workers[identifier]? = some worker) :
    readWord physical.memory (worker.entry.registers .rsp) = .ok worker.returnAddress := by
  have frame := (rel.invariant.worker_footprints rel.ready live).buffer_readWord
    physical.memory (pending physical) rel.pending_payloads
  have saved := (rel.ready identifier worker live).stack
  change readWord (logicalMemory logical) _ = _ at saved
  rw [rel.memory] at saved
  exact frame.symm.trans saved

theorem stack_local (rel : Rel config physical logical) {identifier query : Nat}
    {worker : MutexReplay.Worker} {before : TSO.Worker}
    (live : logical.workers[identifier]? = some worker)
    (physicalLive : physical.workers[query]? = some before) :
    readWord (StoreBuffer.view physical.memory before.buffer) (worker.entry.registers .rsp) =
      .ok worker.returnAddress :=
  ((rel.invariant.worker_footprints rel.ready live).buffer_readWord physical.memory before.buffer
    (rel.payloads before (List.mem_of_getElem? physicalLive))).trans (rel.stack_global live)

theorem stack_agrees (rel : Rel config physical logical) {identifier : Nat} {worker : MutexReplay.Worker}
    (live : logical.workers[identifier]? = some worker) :
    MemoryAgreesOn (logicalMemory logical) physical.memory (worker.entry.registers .rsp) 8 := by
  rw [rel.memory]
  apply StoreBuffer.view_agrees
  intro store member
  rw [rel.pending_payloads store member]
  exact (rel.invariant.worker_footprints rel.ready live).dataStack

/-- A lock write commutes with the entire overlay by ownership-derived footprints. -/
theorem lock_overlay (rel : Rel config physical logical) (value : BitVec 32) :
    overlay { physical with memory := writeDWordUnchecked physical.memory config.lockAddress value } =
      writeDWordUnchecked (overlay physical) config.lockAddress value :=
  rel.invariant.buffer_lock_commute physical.memory (pending physical) rel.pending_payloads value

/-- With queues unchanged, an installed lock write commutes with their entire overlay. -/
theorem lock_install_overlay (rel : Rel config physical logical)
    {identifier : Nat} {worker : TSO.Worker}
    (live : physical.workers[identifier]? = some worker) (context : Threads.Context)
    (returned : Bool) (value : BitVec 32) :
    overlay (TSO.install physical identifier
      (writeDWordUnchecked physical.memory config.lockAddress value) context returned worker.buffer) =
      writeDWordUnchecked (overlay physical) config.lockAddress value := by
  unfold overlay
  rw [pending_install_same live]
  exact rel.invariant.buffer_lock_commute _ _ rel.pending_payloads value

/-- Enqueue uses the actual selected holder and its actual store value. -/
theorem enqueue_overlay (rel : Rel config physical logical)
    {identifier : Nat} {before : TSO.Worker} {after : MutexReplay.Worker} {lease : Mutex.Lease}
    (physicalLive : physical.workers[identifier]? = some before)
    (logicalLive : logical.workers[identifier]? = some after) (guard : after.guard = some lease)
    (context : Threads.Context) (returned : Bool) (value : BitVec 32) :
    overlay (TSO.install physical identifier physical.memory context returned
      (StoreBuffer.enqueue before.buffer ⟨config.dataAddress, value⟩)) =
      writeDWordUnchecked (logicalMemory logical) config.dataAddress value := by
  rw [overlay_install_enqueue physicalLive (rel.peers_empty logicalLive guard), ← rel.memory]

/-- A real drain identifies the holder before applying the single-queue algebra. -/
theorem drain_overlay (rel : Rel config physical logical) {identifier : Nat}
    {result : Physical × TSO.Observation} (success : TSO.drain physical identifier = .ok result) :
    overlay result.1 = overlay physical := by
  obtain ⟨worker, head, tail, memory, live, buffer, committed, same⟩ := TSO.drain_ok _ _ _ success
  have nonempty : worker.buffer ≠ [] := by rw [buffer]; simp
  obtain ⟨after, lease, found, guard⟩ := rel.nonempty_guard live nonempty
  have written : memory = writeDWordUnchecked physical.memory head.address head.value := by
    unfold storeDWord at committed
    split at committed
    · exact (Except.ok.inj committed).symm
    · cases committed
  rw [same, written]
  exact overlay_install_drain live (rel.peers_empty found guard) head tail buffer

/-- Draining stutters the entire checked OS state. In particular it does not
modify the guard, loan map, replay phase, or the issued-store credit. -/
theorem drain (rel : Rel config physical logical) {identifier : Nat}
    {result : Physical × TSO.Observation} (success : TSO.drain physical identifier = .ok result) :
    Rel config result.1 logical := by
  obtain ⟨worker, head, tail, memory, live, buffer, committed, same⟩ := TSO.drain_ok _ _ _ success
  have written : memory = writeDWordUnchecked physical.memory head.address head.value := by
    unfold storeDWord at committed
    split at committed
    · exact (Except.ok.inj committed).symm
    · cases committed
  have overlays := rel.drain_overlay success
  have valid := rel.buffers.drain success
  rw [same, written] at valid overlays ⊢
  refine ⟨rel.invariant, rel.ready, ?_, valid, ?_, ?_, ?_, rel.profile.write _ _⟩
  · exact (install_architectures_same live _ _).trans rel.contexts
  · apply install_payloads rel.payloads
    intro store member
    exact rel.payloads worker (List.mem_of_getElem? live) store
      (by rw [buffer]; exact List.mem_cons_of_mem head member)
  · intro query before after physicalLive logicalLive guard
    by_cases selected : identifier = query
    · subst query
      have empty := rel.unguarded identifier worker after live logicalLive guard
      simp [buffer] at empty
    · rw [install_peer _ _ _ _ _ _ _ selected] at physicalLive
      exact rel.unguarded query before after physicalLive logicalLive guard
  · exact rel.memory.trans overlays.symm

/-- Checked current queues construct successful publication without a future-success premise. -/
theorem drain_enabled (rel : Rel config physical logical) {identifier : Nat} {worker : TSO.Worker}
    (live : physical.workers[identifier]? = some worker) (nonempty : worker.buffer ≠ []) :
    ∃ result, TSO.drain physical identifier = .ok result :=
  TSO.drain_enabled _ _ _ rel.buffers.pendingWritable live nonempty

/-- A successful drain removes exactly one actual pending store. -/
theorem drain_pending_length (rel : Rel config physical logical) {identifier : Nat}
    {result : Physical × TSO.Observation} (success : TSO.drain physical identifier = .ok result) :
    (pending result.1).length + 1 = (pending physical).length := by
  obtain ⟨worker, head, tail, memory, live, buffer, _, same⟩ := TSO.drain_ok _ _ _ success
  have nonempty : worker.buffer ≠ [] := by rw [buffer]; simp
  obtain ⟨after, lease, found, guard⟩ := rel.nonempty_guard live nonempty
  have peers := rel.peers_empty found guard
  rw [same, pending_install_of_peers live peers, pending_eq_of_peers live peers, buffer, List.length_cons]

/-- Drain preserves every complete context and actual returned marker. -/
theorem drain_contexts (rel : Rel config physical logical) {identifier : Nat}
    {result : Physical × TSO.Observation} (success : TSO.drain physical identifier = .ok result) :
    result.1.workers.map architecture = physical.workers.map architecture :=
  (rel.drain success).contexts.trans rel.contexts.symm

/-- Initial queues are actually empty; no future execution premise is needed. -/
theorem initial {config : Mutex.Config} {logical : Logical}
    (valid : MutexReplay.Invariant config logical) (ready : MutexReplay.ExecutionReady logical)
    (profile : Profile config (logicalMemory logical)) :
    Rel config (TSO.initial (MutexReplay.erase logical)) logical := by
  refine ⟨valid, ready, ?_, TSO.BuffersValid.initial _, ?_, ?_, ?_, profile⟩
  · simp only [TSO.initial, MutexReplay.erase, List.map_map]
    rfl
  · intro worker member store queued
    obtain ⟨before, _, rfl⟩ := List.mem_map.mp member
    cases queued
  · intro identifier before after live _ _
    simp only [TSO.initial, List.getElem?_map] at live
    cases found : (MutexReplay.erase logical).workers[identifier]? with
    | none => simp [found] at live
    | some worker =>
      simp only [found, Option.map_some, Option.some.injEq] at live
      cases live
      rfl
  · have empty : TSO.Quiescent (TSO.initial (MutexReplay.erase logical)) := by
      intro worker member
      obtain ⟨before, _, rfl⟩ := List.mem_map.mp member
      rfl
    rw [overlay, pending_nil empty, StoreBuffer.view_nil]
    rfl

end Rel
end EDSL.OS.MutexTSO

#audit_edsl
