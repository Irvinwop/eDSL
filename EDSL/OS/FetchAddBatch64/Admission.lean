/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.FetchAddBatch64
import EDSL.Grading.ConcurrentTask

set_option warningAsError true
set_option autoImplicit false

/-!
Derive checked-method batch admission from the independent current ABI gate.
The image base, complete byte list, padding, register files, resources and full
64-bit inputs are arbitrary. Only the static AtomicMethods checker specializes
the code to the RSI-to-RAX, LOCK XADD [RDI], RET family.

This is adapter evidence for the existing managed scalar model, not a registered
Claim or a corpus certificate. It assumes no future execution, old target word,
Protocol or desired result, and introduces no executor or arithmetic semantics.
-/

namespace EDSL.OS.FetchAddBatch64.Admission
open X86 TSO64 X86.VCGen.AtomicMethods

/-- One actual initial worker, with a method built from its current RF,
original resources, selected handle/cell and original caller return address. -/
structure Admitted {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    (image : FetchAddABI64.Image) (before : FetchAddCalls64.CheckedState target cell)
    (tid : Nat) (delta : Word) (padding : List Padding) where
  member : Member image target cell
  worker : Worker
  live : before.state.workers[tid]? = some worker
  current : Current member.method before.state
  entry : At member.method (.preamble 0 member.padding) worker
  registers : member.method.entry = worker.context.registers
  resources : member.method.resources = worker.resources
  input : member.method.entry .rsi = delta
  padded : member.padding = padding
  locked : member.method.locked = LockedAdd64.frozen

/-- Extract the tuple from the gate's actual selector. No address-identity
uniqueness argument or stronger resource precondition is needed. -/
theorem of_gate {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    {image : FetchAddABI64.Image} {before : FetchAddCalls64.CheckedState target cell}
    {tid : Nat} {delta : Word} {padding : List Padding}
    (checked : check image.bytes .rsi LockedAdd64.frozen padding = true)
    (accepted : FetchAddABI64.gate image before tid tid delta = true) :
    Nonempty (Admitted image before tid delta padding) := by
  obtain ⟨worker, live, facts⟩ := FetchAddABI64.gate_sound accepted
  have gate : FetchAddABI64.workerGate image before.state target cell worker delta = true := by
    simpa only [FetchAddABI64.gate, live] using accepted
  have atomic := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp gate).1).2
  cases selected : atomicFor before.state.world worker.resources cell.address with
  | none => simp only [selected, Bool.false_eq_true] at atomic
  | some triple =>
    obtain ⟨identifier, handle, actual⟩ := triple
    have same : handle.cell = target ∧ actual = cell := by
      simpa only [selected, decide_eq_true_eq] using atomic
    obtain ⟨linked, sameCell⟩ := same
    subst actual
    obtain ⟨address, caller, _, _, canonicalReturn⟩ := facts.caller
    let method : Method := {
      bytes := image.bytes
      input := .rsi
      locked := LockedAdd64.frozen
      base := image.base
      entry := worker.context.registers
      resources := worker.resources
      identifier := identifier
      handle := handle
      cell := cell
      returnAddress := address
      size := (check_sound checked).1
      sourceNotRsp := by decide +kernel
      originalRsp := facts.present.2.2.2.2.2.1
      returnCanonical := canonicalReturn
      stackNoWrap := by
        rw [facts.present.2.2.2.2.2.1]
        exact facts.present.2.2.2.2.2.2.2.2.2.1 }
    let member : Member image target cell := {
      method := method
      padding := padding
      base := rfl
      bytes := rfl
      source := by
        change LockedAdd64.frozen.source = .rax
        decide +kernel
      input := rfl
      object := rfl
      target := linked }
    have current : Current method before.state := by
      refine ⟨before.valid, facts.code, facts.present.2.2.2.2.2.2.2.2.1, caller, ?_⟩
      change atomicFor before.state.world worker.resources
        (written worker.context.registers LockedAdd64.frozen.source
          (worker.context.registers .rsi) LockedAdd64.frozen.base) = _
      have source : LockedAdd64.frozen.source = .rax := by decide +kernel
      have base : LockedAdd64.frozen.base = .rdi := by decide +kernel
      rw [source, base, written_other _ _ _ _ (by decide +kernel), facts.present.2.2.2.1]
      exact selected
    have entry : At method (.preamble 0 padding) worker := by
      refine ⟨rfl, facts.present.2.1, facts.present.1, ?_, rfl, (check_sound checked).2⟩
      simpa only [BitVec.add_zero] using facts.present.2.2.1
    exact ⟨⟨member, worker, live, current, entry, rfl, rfl,
      facts.present.2.2.2.2.1, rfl, rfl⟩⟩

/-- The full initial population, retaining exact input-list equality and a
single padding list. Both are proof outputs, independent of later body events. -/
structure Family {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    (image : FetchAddABI64.Image) (before : FetchAddCalls64.CheckedState target cell)
    (deltas : List Word) (padding : List Padding) where
  members : List (Member image target cell)
  pre : FetchAddBatch64.Pre members before
  length : members.length = deltas.length
  inputs : members.map (fun member => member.method.entry .rsi) = deltas
  padded : ∀ member ∈ members, member.padding = padding

/-- One generic static check bridges every independently admitted context.
Choice selects proof-facing descriptions of actual workers; it adds no
operational behavior or input restriction. -/
theorem admit {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    {image : FetchAddABI64.Image} {before : FetchAddCalls64.CheckedState target cell}
    {deltas : List Word} {padding : List Padding}
    (checked : check image.bytes .rsi LockedAdd64.frozen padding = true)
    (pre : Grading.ConcurrentTask.FetchAdd64.Pre image before deltas) :
    Nonempty (Family image before deltas padding) := by
  classical
  let selected (i : Fin deltas.length) : Admitted image before i.val deltas[i] padding :=
    Classical.choice (of_gate checked (pre.entry i))
  let members := List.ofFn fun i => (selected i).member
  have length : members.length = deltas.length := List.length_ofFn
  have member_at (i : Fin members.length) : members[i] =
      (selected ⟨i.val, by simpa only [length] using i.isLt⟩).member := by
    simp only [members, List.getElem_ofFn, Fin.getElem_fin]
  refine ⟨⟨members, ?_, length, ?_, ?_⟩⟩
  · refine ⟨pre.length.trans length.symm, ?_, ?_, ?_⟩
    · intro i
      rw [member_at i]
      exact (selected ⟨i.val, by simpa only [length] using i.isLt⟩).current
    · intro i
      rw [member_at i]
      let j : Fin deltas.length := ⟨i.val, by simpa only [length] using i.isLt⟩
      exact ⟨(selected j).worker, (selected j).live, (selected j).entry⟩
    · intro i
      rw [member_at i, (selected _).input]
      exact pre.entry ⟨i.val, by simpa only [length] using i.isLt⟩
  · apply List.ext_getElem
    · simpa only [List.length_map] using length
    · intro i left right
      rw [List.getElem_map]
      change members[(⟨i, by simpa only [List.length_map] using left⟩ : Fin members.length)].method.entry .rsi = _
      rw [member_at]
      exact (selected ⟨i, right⟩).input
  · intro member memberIn
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp memberIn
    exact (selected i).padded

/-- Equality of total input views, including their common zero default outside
the cohort. Covered inputs retain every bit, including high halves and zero. -/
theorem Family.delta_eq {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    {image : FetchAddABI64.Image} {before : FetchAddCalls64.CheckedState target cell}
    {deltas : List Word} {padding : List Padding}
    (family : Family image before deltas padding) (tid : Nat) :
    FetchAddBatch64.delta family.members tid = deltas[tid]?.getD 0 := by
  have values := congrArg (fun words : List Word => words[tid]?.getD 0) family.inputs
  simpa only [List.getElem?_map, FetchAddBatch64.delta] using values

theorem Family.input_at {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    {image : FetchAddABI64.Image} {before : FetchAddCalls64.CheckedState target cell}
    {deltas : List Word} {padding : List Padding}
    (family : Family image before deltas padding) (i : Fin family.members.length) :
    family.members[i].method.entry .rsi = deltas[i.val]?.getD 0 := by
  simpa only [FetchAddBatch64.delta, List.getElem?_eq_getElem i.isLt,
    Option.map_some, Option.getD_some, Fin.getElem_fin] using family.delta_eq i.val

theorem Family.padding_at {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    {image : FetchAddABI64.Image} {before : FetchAddCalls64.CheckedState target cell}
    {deltas : List Word} {padding : List Padding}
    (family : Family image before deltas padding) (i : Fin family.members.length) :
    family.members[i].padding = padding :=
  family.padded _ (List.mem_of_getElem (i := i.val) rfl)

/-- The body cohort is exactly the independently registered cohort at any
supplied state. This metadata equality assumes no completion or result value. -/
theorem Family.cohort_eq {target : Atomics64.CellId64} {cell : Atomics64.Cell}
    {image : FetchAddABI64.Image} {before : FetchAddCalls64.CheckedState target cell}
    {deltas : List Word} {padding : List Padding}
    (family : Family image before deltas padding) (after : TSO64.State) :
    FetchAddBatch64.cohort family.members after =
      Grading.ConcurrentTask.FetchAdd64.cohort deltas after := by
  unfold FetchAddBatch64.cohort Grading.ConcurrentTask.FetchAdd64.cohort
  rw [family.length]
  apply List.map_congr_left
  intro tid _
  unfold FetchAddBatch64.cohortCall
  rw [family.delta_eq]
  rfl

end EDSL.OS.FetchAddBatch64.Admission

#audit_edsl
