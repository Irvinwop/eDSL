/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.TSOWord
import EDSL.OS.TSO64.WordProjection.Locations

set_option autoImplicit false

namespace EDSL.OS.TSO64.WordProjection
open X86 Concurrency

abbrev ReferenceState := TSOWord.State Atomics64.CellId64
abbrev ReferenceLabel := TSOWord.Label Atomics64.CellId64

/-- Register/control state and RAM outside registered cells are erased. The reference lock is
free at concrete instruction boundaries; a locked instruction expands to an
explicit acquire/read/write/publication/unlock path between those boundaries. -/
def project (state : State) : ReferenceState :=
  ⟨memory state.world, buffers state, none⟩

theorem reference_ext {first second : ReferenceState}
    (memory : first.memory = second.memory) (buffers : first.buffers = second.buffers)
    (lock : first.lock = second.lock) : first = second := by
  cases first
  cases second
  cases memory
  cases buffers
  cases lock
  rfl

theorem managed_append (first second : List Pending) :
    managed (first ++ second) = managed first ++ managed second := by
  induction first with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simp only [List.cons_append, managed, ih, List.cons_append]

theorem buffers_live {state : State} {tid : Nat} {worker : Worker}
    (live : state.workers[tid]? = some worker) : buffers state tid = (managed worker.pending).reverse := by
  simp only [buffers, live]

theorem buffers_install {state : State} {tid : Nat} {world : World} {prior replacement : Worker}
    (live : state.workers[tid]? = some prior) :
    buffers (install state tid world replacement) =
      TSOWord.setBuffer (buffers state) tid (managed replacement.pending).reverse := by
  have here : (install state tid world replacement).workers[tid]? = some replacement :=
    List.getElem?_set_self (List.getElem_of_getElem? live).1
  funext peer
  by_cases same : peer = tid
  · subst peer
    simp only [buffers_live here, TSOWord.setBuffer, ↓reduceIte]
  · have unchanged := install_peer (state := state) (world := world) (worker := replacement) same
    simp only [buffers, unchanged, TSOWord.setBuffer, ite_eq_right same]

theorem setBuffer_current (buffer : Nat → List (Atomics64.CellId64 × Word)) (tid : Nat) :
    TSOWord.setBuffer buffer tid (buffer tid) = buffer := by
  funext peer
  by_cases same : peer = tid
  · subst peer; simp only [TSOWord.setBuffer, ↓reduceIte]
  · simp only [TSOWord.setBuffer, ite_eq_right same]

theorem project_install {state : State} {tid : Nat} {world : World} {prior replacement : Worker}
    (live : state.workers[tid]? = some prior) :
    project (install state tid world replacement) =
      ⟨memory world, TSOWord.setBuffer (buffers state) tid (managed replacement.pending).reverse, none⟩ := by
  exact reference_ext rfl (buffers_install live) rfl

theorem erased_install {state : State} {tid : Nat} {world : World} {prior replacement : Worker}
    (live : state.workers[tid]? = some prior) (sameMemory : memory world = memory state.world)
    (samePending : managed replacement.pending = managed prior.pending) :
    project (install state tid world replacement) = project state := by
  rw [project_install live, samePending, ← buffers_live live, setBuffer_current]
  exact reference_ext sameMemory rfl rfl

end EDSL.OS.TSO64.WordProjection
