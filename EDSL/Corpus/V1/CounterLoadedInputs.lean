/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterResources
import EDSL.Corpus.V1.CounterCompletion

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Completion and production retirement from the actual loaded counter inputs.
One compiler selects one complete frozen ELF for both workers. The initial
word, two independent uint32 counts, upper RSI halves, complete modeled flag
words and per-thread AF choices are arbitrary. Current admission, validity,
empty queues, resource shape, separation and the initial read all come from
the actual resource constructor; no setup or future execution succeeds by
assumption. Other initial registers retain that constructor's fixed choices.

The existing completion theorem supplies the entire ranked execution and its
production cleanup. The output retains that same execution's chosen issues,
lifted histories, returned/quiescent endpoint and cleanup history, current RAM,
revocations, independent modular sum and outside-byte frame. Every original
loaded ELF cell also survives, including its complete permission record.

The imported long-mode/CET-off, coherent scalar WB RAM, stable translation
and no-alias, protected-loan and logical-authority model assumptions remain.
This gives one finite model execution for each AF choice function, without
fairness, all-schedule termination, minimum cost, native/hardware/source or
compiler refinement, corpus credit, or grader/native/certificate completeness.
The two compiler cases are separate homogeneous executions, never simultaneous
incompatible compiler images. This standalone module is not a registry entry.
-/

namespace EDSL.Corpus.V1.CounterLoadedInputs
open X86 OS OS.AddressSpace OS.TSO64 OS.TSO64.EffectSimulation
open CounterResources

/-- The existing ranked suffix specialized to both actual attached workers.
Its fields retain the actual schedule, chosen issues and the same full ghosts
and histories, rather than unrelated existential execution witnesses. -/
abbrev Execution (compiler : CounterCommon.Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (choices : Nat → Nat → Bool) :=
  let leftPre := pre compiler old count upper flags 0
  let rightPre := pre compiler old count upper flags 1
  let leftProfile := site_profile compiler old count upper flags 0
  let rightProfile := site_profile compiler old count upper flags 1
  let subjects := CounterCommon.twoCounterSubjects leftPre rightPre leftProfile rightProfile
  let slots := CounterCommon.twoCounterSubjects_slots leftPre rightPre leftProfile rightProfile
    (site_slot compiler old count upper flags 0) (site_slot compiler old count upper flags 1)
  (CounterCommon.counterRankedCohort subjects slots).Suffix
    (before := initial compiler old count upper flags)
    (CounterCommon.counterInitialGhosts subjects slots) choices (fun _ => 0)

/-- All witnesses refer to one constructed execution and its actual retireAll
result. The counter read and formula concern the cleaned world's current RAM.
The full-image clause includes non-code bytes and every permission bit. -/
structure Output (compiler : CounterCommon.Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (choices : Nat → Nat → Bool) where
  execution : Execution compiler old count upper flags choices
  result : S × List Context
  value : Word
  retired : Lifecycle.retireAll execution.final = .ok result
  valid : WellFormed result.1 .ownedOnly
  workers : result.1.workers = []
  contexts : result.2 = execution.final.workers.reverse.map Worker.context
  resources : result.1.world.legacy.shared.resources = execution.final.world.legacy.shared.resources
  cells : result.1.world.cells = execution.final.world.cells
  ram : published result.1.world = published execution.final.world
  history : ∃ labels, Atomics64.History execution.final.world labels result.1.world
  revoked : ∀ worker ∈ execution.final.workers, Lifecycle.WorkerRevoked result.1.world worker
  targetLive : result.1.world.cells (Image.resources compiler old).target =
    some (Image.resources compiler old).cell
  counter : loadQWord (published result.1.world) PlainResources.standard.target = .ok value
  total : value.toNat = (old.toNat + (count 0).toNat + (count 1).toNat) % 2^64
  frame : ∀ query : Word, 8 ≤ (query - PlainResources.standard.target).toNat →
    (published result.1.world).read query =
      (published (initial compiler old count upper flags).world).read query
  image : ∀ {address : Word} {original : AddressSpace.Cell},
    (Image.installed compiler).space.cells address = some original →
      result.1.world.legacy.shared.resources.space.cells address = some original

/-- The abstract ELF loader installs readable cells, also outside the function
window. This extracts that generic permission fact without evaluating a file. -/
private theorem installed_readable (compiler : CounterCommon.Compiler)
    {address : Word} {original : AddressSpace.Cell}
    (live : (Image.installed compiler).space.cells address = some original) :
    original.permissions.readable = true := by
  change (ELF.install (CounterMixedGraphs.file compiler)
    (CounterMixedGraphs.input compiler).table.image empty).cells address = some original at live
  cases selected : ELF.segmentAt (CounterMixedGraphs.input compiler).table.image address.toNat with
  | none => simp only [ELF.install, selected, empty] at live; cases live
  | some segment =>
    have found : ELF.segmentCell (CounterMixedGraphs.file compiler) segment address.toNat =
        some original := by
      simpa only [ELF.install, selected] using live
    dsimp only [ELF.segmentCell] at found
    split at found
    · cases byte : (CounterMixedGraphs.file compiler)[segment.offset +
          (address.toNat - segment.virtualAddress)]? with
      | none => simp only [byte, Option.map_none] at found; cases found
      | some value =>
        simp only [byte, Option.map_some, Option.some.injEq] at found
        cases found
        rfl
    · cases Option.some.inj found
      rfl

/-- A preserved readable byte and complete permission record determine the
whole cell. Read equality alone would not determine inaccessible contents. -/
private theorem readable_cell_eq {before after : Space} {address : Word}
    {original : AddressSpace.Cell} (live : before.cells address = some original)
    (readable : original.permissions.readable = true)
    (permissions : (after.cells address).map AddressSpace.Cell.permissions =
      (before.cells address).map AddressSpace.Cell.permissions)
    (read : (toMemory after).read address = (toMemory before).read address) :
    after.cells address = some original := by
  cases current : after.cells address with
  | none => simp only [current, live, Option.map_none, Option.map_some] at permissions; cases permissions
  | some now =>
    have samePermissions : now.permissions = original.permissions := by
      simpa only [current, live, Option.map_some, Option.some.injEq] using permissions
    have sameByte : now.byte = original.byte := by
      simpa [toMemory, current, live, samePermissions, readable] using read
    have same : now = original := by
      cases now
      cases original
      cases samePermissions
      cases sameByte
      rfl
    exact congrArg some same

/-- Every actual loaded input has a finite production execution and successful
logical retirement. No Pre, setup success, validity, schedule, returned state,
desired result, resource shape or separation is a caller-supplied premise. -/
theorem complete (compiler : CounterCommon.Compiler) (old : Word)
    (count upper : Fin 2 → BitVec 32) (flags : Fin 2 → Word)
    (choices : Nat → Nat → Bool) :
    Nonempty (Output compiler old count upper flags choices) := by
  obtain ⟨suffix, result, value, retired, valid, workers, contexts, resources, cells,
      ram, history, revoked, counter, total, frame⟩ :=
    CounterCommon.two_complete_retired_total_frame
      (pre compiler old count upper flags 0) (pre compiler old count upper flags 1)
      (site_profile compiler old count upper flags 0) (site_profile compiler old count upper flags 1)
      (site_slot compiler old count upper flags 0) (site_slot compiler old count upper flags 1)
      (workerUniverse2 compiler old count upper flags) (quiescent compiler old count upper flags)
      (cleanupShape compiler old count upper flags 0) (cleanupShape compiler old count upper flags 1)
      (separate compiler old count upper flags) choices
      (Image.resources compiler old).target (Image.resources compiler old).cell
      (registered compiler old count upper flags) rfl rfl old (initial_read compiler old count upper flags)
  have stable := TSO64.schedule_stable suffix.actual
  have targetLive : result.1.world.cells (Image.resources compiler old).target =
      some (Image.resources compiler old).cell := by
    rw [cells, stable.cells]
    exact registered compiler old count upper flags
  have retained : ∀ {address : Word} {original : AddressSpace.Cell},
      (Image.installed compiler).space.cells address = some original →
        result.1.world.legacy.shared.resources.space.cells address = some original := by
    intro address original live
    have noWrap : (Image.resources compiler old).cell.address.toNat + 7 < 2^64 := by
      rw [Image.target_address]
      decide +kernel
    have outside : 8 ≤ (address - (Image.resources compiler old).cell.address).toNat := by
      apply Classical.byContradiction
      intro inside
      exact target_outside_loaded compiler old live
        ((qword_contains_iff _ _ noWrap).mpr (by omega))
    apply readable_cell_eq (full_image compiler old count upper flags live)
      (installed_readable compiler live)
    · rw [resources]
      exact stable.permissions address
    · exact frame address outside
  exact ⟨{
    execution := suffix
    result := result
    value := value
    retired := retired
    valid := valid
    workers := workers
    contexts := contexts
    resources := resources
    cells := cells
    ram := ram
    history := history
    revoked := revoked
    targetLive := targetLive
    counter := by simpa only [Image.target_address] using counter
    total := total
    frame := by simpa only [Image.target_address] using frame
    image := retained }⟩

#print axioms Execution
#print axioms Output
#print axioms Output.mk
#print axioms Output.execution
#print axioms Output.result
#print axioms Output.value
#print axioms Output.retired
#print axioms Output.valid
#print axioms Output.workers
#print axioms Output.contexts
#print axioms Output.resources
#print axioms Output.cells
#print axioms Output.ram
#print axioms Output.history
#print axioms Output.revoked
#print axioms Output.targetLive
#print axioms Output.counter
#print axioms Output.total
#print axioms Output.frame
#print axioms Output.image
#print axioms installed_readable
#print axioms readable_cell_eq
#print axioms complete

end EDSL.Corpus.V1.CounterLoadedInputs

#audit_edsl
