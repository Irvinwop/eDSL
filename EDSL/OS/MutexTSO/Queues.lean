/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexTSO.Model

namespace EDSL.OS.MutexTSO
open X86

private theorem set_eq_of_lookup {α : Type} {workers : List α} {identifier : Nat} {worker : α}
    (live : workers[identifier]? = some worker) : workers.set identifier worker = workers := by
  obtain ⟨bound, same⟩ := List.getElem_of_getElem? live
  rw [← same]
  exact List.set_getElem_self bound

@[simp] theorem install_live {physical : Physical} {identifier : Nat} {worker : TSO.Worker}
    (live : physical.workers[identifier]? = some worker)
    (memory : Memory) (context : Threads.Context) (returned : Bool) (buffer : StoreBuffer.Buffer) :
    (TSO.install physical identifier memory context returned buffer).workers[identifier]? =
      some ⟨context, returned, buffer⟩ :=
  List.getElem?_set_self (List.getElem_of_getElem? live).1

/-- Installation retains the complete worker at every other index. -/
theorem install_peer (physical : Physical) (identifier query : Nat) (memory : Memory)
    (context : Threads.Context) (returned : Bool) (buffer : StoreBuffer.Buffer)
    (different : identifier ≠ query) :
    (TSO.install physical identifier memory context returned buffer).workers[query]? =
      physical.workers[query]? :=
  List.getElem?_set_ne different

@[simp] theorem install_architectures (physical : Physical) (identifier : Nat) (memory : Memory)
    (context : Threads.Context) (returned : Bool) (buffer : StoreBuffer.Buffer) :
    (TSO.install physical identifier memory context returned buffer).workers.map architecture =
      (physical.workers.map architecture).set identifier ⟨context, returned⟩ := by
  simp only [TSO.install, List.map_set, architecture]

theorem install_architectures_same {physical : Physical} {identifier : Nat} {worker : TSO.Worker}
    (live : physical.workers[identifier]? = some worker) (memory : Memory) (buffer : StoreBuffer.Buffer) :
    (TSO.install physical identifier memory worker.context worker.returned buffer).workers.map architecture =
      physical.workers.map architecture := by
  rw [install_architectures]
  have found : (physical.workers.map architecture)[identifier]? = some (architecture worker) := by
    simp only [List.getElem?_map, live, Option.map_some]
  exact set_eq_of_lookup found

/-- A replacement queue and all surviving queues retain their payload address. -/
theorem install_payloads {physical : Physical} {config : Mutex.Config}
    (payloads : ∀ worker ∈ physical.workers, ∀ store ∈ worker.buffer,
      store.address = config.dataAddress)
    (identifier : Nat) (memory : Memory) (context : Threads.Context) (returned : Bool)
    (buffer : StoreBuffer.Buffer)
    (selected : ∀ store ∈ buffer, store.address = config.dataAddress) :
    ∀ worker ∈ (TSO.install physical identifier memory context returned buffer).workers,
      ∀ store ∈ worker.buffer, store.address = config.dataAddress := by
  intro worker member store queued
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact payloads worker old store queued
  · exact selected store queued

@[simp] theorem pending_nil {physical : Physical} (empty : TSO.Quiescent physical) :
    pending physical = [] :=
  List.flatMap_eq_nil_iff.mpr empty

/-- Only this selected queue contributes when every other queue is empty.
The premise is essential for overlapping writes in arbitrary worker lists. -/
theorem pending_eq_of_peers {physical : Physical} {identifier : Nat} {worker : TSO.Worker}
    (live : physical.workers[identifier]? = some worker)
    (peers : ∀ query peer, physical.workers[query]? = some peer →
      identifier ≠ query → peer.buffer = []) : pending physical = worker.buffer := by
  obtain ⟨memory, workers⟩ := physical
  change workers.flatMap (fun worker => worker.buffer) = worker.buffer
  change workers[identifier]? = some worker at live
  change ∀ query peer, workers[query]? = some peer → identifier ≠ query → peer.buffer = [] at peers
  induction workers generalizing identifier with
  | nil => simp at live
  | cons first rest ih =>
    cases identifier with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at live
      subst first
      have empty : rest.flatMap (fun worker => worker.buffer) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro peer member
        obtain ⟨query, found⟩ := List.mem_iff_getElem?.mp member
        exact peers (query + 1) peer found (by omega)
      simp only [List.flatMap_cons, empty, List.append_nil]
    | succ identifier =>
      have empty : first.buffer = [] := peers 0 first rfl (by omega)
      have tail := ih (identifier := identifier) live (by
        intro query peer found different
        exact peers (query + 1) peer found (by omega))
      simp only [List.flatMap_cons, empty, List.nil_append, tail]

theorem pending_install_of_peers {physical : Physical} {identifier : Nat} {worker : TSO.Worker}
    (live : physical.workers[identifier]? = some worker)
    (peers : ∀ query peer, physical.workers[query]? = some peer →
      identifier ≠ query → peer.buffer = [])
    (memory : Memory) (context : Threads.Context) (returned : Bool) (buffer : StoreBuffer.Buffer) :
    pending (TSO.install physical identifier memory context returned buffer) = buffer := by
  apply pending_eq_of_peers (install_live live memory context returned buffer)
  intro query peer found different
  rw [install_peer _ _ _ _ _ _ _ different] at found
  exact peers query peer found different

/-- Context and return-marker updates alone leave the flattened actual queues intact. -/
theorem pending_install_same {physical : Physical} {identifier : Nat} {worker : TSO.Worker}
    (live : physical.workers[identifier]? = some worker)
    (memory : Memory) (context : Threads.Context) (returned : Bool) :
    pending (TSO.install physical identifier memory context returned worker.buffer) = pending physical := by
  unfold pending TSO.install
  simp only [List.flatMap_def, List.map_set]
  have found : (physical.workers.map (fun worker => worker.buffer))[identifier]? = some worker.buffer := by
    simp only [List.getElem?_map, live, Option.map_some]
  rw [set_eq_of_lookup found]

theorem overlay_install_same {physical : Physical} {identifier : Nat} {worker : TSO.Worker}
    (live : physical.workers[identifier]? = some worker)
    (context : Threads.Context) (returned : Bool) :
    overlay (TSO.install physical identifier physical.memory context returned worker.buffer) =
      overlay physical := by
  unfold overlay
  rw [pending_install_same live]
  rfl

/-- Appending to the sole possible nonempty queue appends the final overlay write. -/
theorem overlay_install_enqueue {physical : Physical} {identifier : Nat} {worker : TSO.Worker}
    (live : physical.workers[identifier]? = some worker)
    (peers : ∀ query peer, physical.workers[query]? = some peer →
      identifier ≠ query → peer.buffer = [])
    (context : Threads.Context) (returned : Bool) (store : StoreBuffer.Store) :
    overlay (TSO.install physical identifier physical.memory context returned
      (StoreBuffer.enqueue worker.buffer store)) =
      writeDWordUnchecked (overlay physical) store.address store.value := by
  unfold overlay
  rw [pending_install_of_peers live peers, pending_eq_of_peers live peers]
  exact StoreBuffer.view_enqueue _ _ _

/-- A FIFO head can move to RAM without changing the full overlay when peer
queues are empty. No claim is made for arbitrary overlapping peer queues. -/
theorem overlay_install_drain {physical : Physical} {identifier : Nat} {worker : TSO.Worker}
    (live : physical.workers[identifier]? = some worker)
    (peers : ∀ query peer, physical.workers[query]? = some peer →
      identifier ≠ query → peer.buffer = [])
    (head : StoreBuffer.Store) (tail : StoreBuffer.Buffer) (buffer : worker.buffer = head :: tail) :
    overlay (TSO.install physical identifier
      (writeDWordUnchecked physical.memory head.address head.value)
      worker.context worker.returned tail) = overlay physical := by
  unfold overlay
  rw [pending_install_of_peers live peers, pending_eq_of_peers live peers, buffer]
  rfl

/-- Every physical drain retains every architectural context and returned flag,
independently of the mutex-specific queue exclusivity argument. -/
theorem drain_architectures {physical : Physical} {identifier : Nat}
    {result : Physical × TSO.Observation} (success : TSO.drain physical identifier = .ok result) :
    result.1.workers.map architecture = physical.workers.map architecture := by
  obtain ⟨worker, head, tail, memory, live, _, _, same⟩ := TSO.drain_ok _ _ _ success
  rw [same]
  exact install_architectures_same live memory tail

theorem drain_empty {physical : Physical} {identifier : Nat} {worker : TSO.Worker}
    (live : physical.workers[identifier]? = some worker) (empty : worker.buffer = []) :
    TSO.drain physical identifier = .error .emptyBuffer := by
  simp [TSO.drain, live, empty]

end EDSL.OS.MutexTSO

#audit_edsl
