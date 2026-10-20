/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicFetchAdd64
import EDSL.Concurrency.ModuloCounter

namespace EDSL.OS.AtomicFetchAddHistory64
open X86 AddressSpace Atomics64

/-- A persistent-registration interval admits only current checked arithmetic,
checked ordinary mutations and idle. Enrollment, issue/close, retirement and raw
legacy mutations have no constructor. In particular ordinary changes cannot
release, transfer, protect or store into any registered allocation. -/
inductive Step : Atomics64.State → Option FetchAddEvent → Atomics64.State → Prop where
  | fetchAdd {before actor identifier delta result}
      (success : Atomics64.fetchAdd before actor identifier delta = .ok result) :
      Step before (some result.2) result.1
  | mutate {before operation result}
      (success : Atomics64.mutate before operation = .ok result) : Step before none result.1
  | idle {state} : Step state none state

/-- Positions retain every real arithmetic event, including other cells and
zero-delta calls, and all silent checked mutations. No invocation or return
boundary, CPU execution, TSO scheduling or native atomicity is inferred. -/
inductive History : Atomics64.State → List (Option FetchAddEvent) → Atomics64.State → Prop where
  | refl {state} : History state [] state
  | next {before middle after label labels} (first : Step before label middle)
      (tail : History middle labels after) : History before (label :: labels) after

theorem Step.wellFormed {before after : Atomics64.State} {label : Option FetchAddEvent}
    (step : Step before label after) (valid : WellFormed before) : WellFormed after := by
  cases step with
  | fetchAdd success => exact fetchAdd_wellFormed _ _ _ _ _ valid success
  | mutate success => exact mutate_wellFormed _ _ _ valid success
  | idle => exact valid

/-- The entire descriptor registry is unchanged, not merely a reused address. -/
theorem Step.cells {before after : Atomics64.State} {label : Option FetchAddEvent}
    (step : Step before label after) : after.cells = before.cells := by
  cases step with
  | fetchAdd success => exact (fetchAdd_effect _ _ _ _ _ success).cells
  | mutate success =>
    obtain ⟨_, _, _, same⟩ := mutate_ok _ _ _ success
    rw [same]
  | idle => rfl

theorem Step.handles {before after : Atomics64.State} {label : Option FetchAddEvent}
    (step : Step before label after) : after.handles = before.handles := by
  cases step with
  | fetchAdd success => exact (fetchAdd_effect _ _ _ _ _ success).handles
  | mutate success =>
    obtain ⟨_, _, _, same⟩ := mutate_ok _ _ _ success
    rw [same]
  | idle => rfl

/-- Event input is the actual operation argument; the complete old response,
actor/handle and current registered-cell context come from that operation. -/
theorem Step.event_origin {before after : Atomics64.State} {event : FetchAddEvent}
    (step : Step before (some event) after) :
    ∃ actor identifier delta handle cell,
      Atomics64.fetchAdd before actor identifier delta = .ok (after, event) ∧
      before.handles identifier = some handle ∧ handle.actor = actor ∧
      before.cells handle.cell = some cell ∧ ValidCell before.legacy.shared cell ∧
      event.cell = handle.cell ∧ event.arithmetic.event.address = cell.address ∧
      event.arithmetic.delta = delta ∧ event.actor = actor ∧ event.handle = identifier ∧
      loadQWord (toMemory before.legacy.shared.resources.space) cell.address =
        .ok event.arithmetic.event.before ∧
      loadQWord (toMemory after.legacy.shared.resources.space) cell.address =
        .ok event.arithmetic.event.after ∧
      Concurrency.ModuloCounter.Step event.arithmetic.event.before delta
        event.arithmetic.event.before event.arithmetic.event.after := by
  cases step with
  | @fetchAdd actor identifier delta result success =>
    obtain ⟨handle, cell, live, acts, linked, checked, identity, address⟩ :=
      fetchAdd_context _ _ _ _ _ success
    have sound := fetchAdd_sound _ _ _ _ _ success
    refine ⟨actor, identifier, delta, handle, cell, success, live, acts, linked, checked,
      identity, address, sound.2.1, sound.2.2.2.1, sound.2.2.2.2, ?_, ?_,
      rfl, fetchAdd_modular _ _ _ _ _ success⟩
    · rw [← address]
      exact fetchAdd_old _ _ _ _ _ success
    · rw [← address]
      exact fetchAdd_readback _ _ _ _ _ success

/-- Whole-eight-byte current containment turns an allocation frame into exact
load equality. No desired post-value or future successful read is assumed. -/
theorem load_frame {before after : Ownership.World} {cell : Atomics64.Cell}
    (world : Ownership.WellFormed before)
    (valid : ValidCell ⟨before, 0, fun _ => none⟩ cell)
    (frame : Ownership.PreservesAllocation before after cell.ticket.identifier) :
    loadQWord (toMemory after.space) cell.address = loadQWord (toMemory before.space) cell.address := by
  obtain ⟨⟨allocation, found, _, _, fits, _⟩, _, _⟩ := valid
  have framed := (frame allocation found).2
  let loan : Borrowing.Loan := ⟨cell.ticket, cell.owner, cell.owner, allocation.region⟩
  have regionValid := (world.1 _ _ found).2.1
  have subregion : Borrowing.Subregion (qwordRegion cell.address) loan.region := of_decide_eq_true fits
  apply loadQWord_congr
  intro offset bound
  exact (toMemory_agrees_at _ _ _
    (framed _ (Borrowing.qword_inside loan regionValid cell.address subregion offset bound))).1

theorem mutate_load {before : Atomics64.State} {operation : Ownership.Mutation}
    {result : Atomics64.State × Option Ownership.Ticket}
    (valid : WellFormed before) (success : Atomics64.mutate before operation = .ok result)
    (target : CellId64) (cell : Atomics64.Cell) (live : before.cells target = some cell) :
    loadQWord (toMemory result.1.legacy.shared.resources.space) cell.address =
      loadQWord (toMemory before.legacy.shared.resources.space) cell.address :=
  load_frame valid.legacy.shared.1 (valid.cells _ _ live).2
    (mutate_preserves_cell _ _ _ valid success target cell live)

theorem fetchAdd_other_load {before : Atomics64.State} {actor : Nat} {identifier : HandleId64}
    {delta : Word} {result : Atomics64.State × FetchAddEvent}
    (valid : WellFormed before)
    (success : Atomics64.fetchAdd before actor identifier delta = .ok result)
    (target : CellId64) (cell : Atomics64.Cell) (live : before.cells target = some cell)
    (different : target ≠ result.2.cell) :
    loadQWord (toMemory result.1.legacy.shared.resources.space) cell.address =
      loadQWord (toMemory before.legacy.shared.resources.space) cell.address :=
  load_frame valid.legacy.shared.1 (valid.cells _ _ live).2
    (fetchAdd_preserves_other _ _ _ _ _ valid success target cell live different)

/-- One selected identity changes precisely according to the independent
mathematical counter step; every other position preserves its current word. -/
def Projection (target : CellId64) (label : Option FetchAddEvent) (prior next : Word) : Prop :=
  match label with
  | none => next = prior
  | some event => if event.cell = target then
      Concurrency.ModuloCounter.Step prior event.arithmetic.delta event.arithmetic.event.before next
    else next = prior

theorem Step.projection {before after : Atomics64.State} {label : Option FetchAddEvent}
    (step : Step before label after) (valid : WellFormed before)
    (target : CellId64) (cell : Atomics64.Cell) (live : before.cells target = some cell)
    (prior next : Word)
    (readBefore : loadQWord (toMemory before.legacy.shared.resources.space) cell.address = .ok prior)
    (readAfter : loadQWord (toMemory after.legacy.shared.resources.space) cell.address = .ok next) :
    Projection target label prior next := by
  cases step with
  | fetchAdd success =>
    rename_i actor identifier delta result
    by_cases selected : result.2.cell = target
    · obtain ⟨handle, actual, _, _, linked, _, identity, address⟩ :=
        fetchAdd_context _ _ _ _ _ success
      have sameId : handle.cell = target := identity.symm.trans selected
      rw [sameId, live] at linked
      have sameCell := Option.some.inj linked
      subst actual
      have old := fetchAdd_old _ _ _ _ _ success
      have final := fetchAdd_readback _ _ _ _ _ success
      rw [address, readBefore] at old
      rw [address, readAfter] at final
      have oldEq := Except.ok.inj old
      have finalEq := Except.ok.inj final
      simp only [Projection, selected, ↓reduceIte]
      rw [oldEq, finalEq]
      exact ⟨rfl, by
        rw [(fetchAdd_sound _ _ _ _ _ success).2.1]
        exact fetchAdd_modular _ _ _ _ _ success⟩
    · have quiet := fetchAdd_other_load valid success target cell live (Ne.symm selected)
      simp only [Projection, selected, ↓reduceIte]
      exact Except.ok.inj (readAfter.symm.trans (quiet.trans readBefore))
  | mutate success =>
    exact Except.ok.inj (readAfter.symm.trans ((mutate_load valid success target cell live).trans readBefore))
  | idle => exact Except.ok.inj (readAfter.symm.trans readBefore)

/-- Labels can be paired with arbitrary client identifiers/thread names for
sequential reasoning only. Their authenticity, uniqueness and invocation/RET
intervals are deliberately not established by this conversion. The stored
actor remains separately available in the actual source event. -/
def asCall {Id Thread : Type} (identifier : Id) (thread : Thread) (event : FetchAddEvent) :
    Concurrency.ModuloCounter.Call 64 Id Thread :=
  ⟨identifier, thread, event.arithmetic.delta, event.arithmetic.event.before⟩

def selectedCalls {Id Thread : Type} (target : CellId64)
    (identifier : FetchAddEvent → Id) (thread : FetchAddEvent → Thread) :
    List (Option FetchAddEvent) → List (Concurrency.ModuloCounter.Call 64 Id Thread)
  | [] => []
  | none :: labels => selectedCalls target identifier thread labels
  | some event :: labels => if event.cell = target then
      asCall (identifier event) (thread event) event :: selectedCalls target identifier thread labels
    else selectedCalls target identifier thread labels

theorem History.wellFormed {before after : Atomics64.State} {labels : List (Option FetchAddEvent)}
    (history : History before labels after) (valid : WellFormed before) : WellFormed after := by
  induction history with
  | refl => exact valid
  | next first _ ih => exact ih (first.wellFormed valid)

theorem History.cells {before after : Atomics64.State} {labels : List (Option FetchAddEvent)}
    (history : History before labels after) : after.cells = before.cells := by
  induction history with
  | refl => rfl
  | next first _ ih => exact ih.trans first.cells

theorem History.handles {before after : Atomics64.State} {labels : List (Option FetchAddEvent)}
    (history : History before labels after) : after.handles = before.handles := by
  induction history with
  | refl => rfl
  | next first _ ih => exact ih.trans first.handles

theorem History.trans {before middle after : Atomics64.State}
    {firstLabels lastLabels : List (Option FetchAddEvent)}
    (first : History before firstLabels middle) (last : History middle lastLabels after) :
    History before (firstLabels ++ lastLabels) after := by
  induction first with
  | refl => exact last
  | next first _ ih => exact .next first (ih last)

/-- Actual checked histories project to the separately defined arithmetic
object specification. Every silent mutation and other-cell RMW is framed from
present authority and registration, rather than an assumed target equality. -/
theorem History.sequential {Id Thread : Type} {before after : Atomics64.State}
    {labels : List (Option FetchAddEvent)} (history : History before labels after)
    (valid : WellFormed before) (target : CellId64) (cell : Atomics64.Cell)
    (live : before.cells target = some cell) (identifier : FetchAddEvent → Id)
    (thread : FetchAddEvent → Thread) (prior final : Word)
    (readBefore : loadQWord (toMemory before.legacy.shared.resources.space) cell.address = .ok prior)
    (readAfter : loadQWord (toMemory after.legacy.shared.resources.space) cell.address = .ok final) :
    Concurrency.ModuloCounter.Sequential prior (selectedCalls target identifier thread labels) final := by
  induction history generalizing prior with
  | refl =>
    have same := Except.ok.inj (readBefore.symm.trans readAfter)
    subst final
    exact .nil _
  | @next before middle after label labels first tail ih =>
    have validMiddle := first.wellFormed valid
    have liveMiddle : middle.cells target = some cell := by rwa [first.cells]
    obtain ⟨value, observed⟩ := (validMiddle.cells _ _ liveMiddle).2.1.load_exists
    have projected := first.projection valid target cell live prior value readBefore observed
    have remaining := ih validMiddle liveMiddle value observed readAfter
    cases label with
    | none =>
      change value = prior at projected
      subst value
      exact remaining
    | some event =>
      by_cases selected : event.cell = target
      · simp only [selectedCalls, selected, ↓reduceIte]
        exact .cons (by simpa only [Projection, selected, ↓reduceIte, asCall] using projected) remaining
      · simp only [selectedCalls, selected, ↓reduceIte]
        have quiet : value = prior := by simpa only [Projection, selected, ↓reduceIte] using projected
        subst value
        exact remaining

/-- The original target descriptor and current full8 authority survive the entire
persistent interval; release/transfer/protection cannot bypass registration. -/
theorem History.retained {before after : Atomics64.State} {labels : List (Option FetchAddEvent)}
    (history : History before labels after) (valid : WellFormed before)
    (target : CellId64) (cell : Atomics64.Cell) (live : before.cells target = some cell) :
    after.cells target = some cell ∧ ValidCell after.legacy.shared cell ∧
      reserved after cell.ticket.identifier = true := by
  have current : after.cells target = some cell := by rwa [history.cells]
  have finalValid := history.wellFormed valid
  exact ⟨current, (finalValid.cells _ _ current).2, reserved_of_live after finalValid target cell current⟩

-- Endpoint read existence is derived from the preserved current registration.
theorem History.project_exists {Id Thread : Type} {before after : Atomics64.State}
    {labels : List (Option FetchAddEvent)} (history : History before labels after)
    (valid : WellFormed before) (target : CellId64) (cell : Atomics64.Cell)
    (live : before.cells target = some cell) (identifier : FetchAddEvent → Id)
    (thread : FetchAddEvent → Thread) (prior : Word)
    (readBefore : loadQWord (toMemory before.legacy.shared.resources.space) cell.address = .ok prior) :
    ∃ final, loadQWord (toMemory after.legacy.shared.resources.space) cell.address = .ok final ∧
      Concurrency.ModuloCounter.Sequential prior (selectedCalls target identifier thread labels) final := by
  have current : after.cells target = some cell := by rwa [history.cells]
  obtain ⟨final, observed⟩ := ((history.wellFormed valid).cells _ _ current).2.1.load_exists
  exact ⟨final, observed, history.sequential valid target cell live identifier thread prior final readBefore observed⟩

theorem History.total {Id Thread : Type} {before after : Atomics64.State}
    {labels : List (Option FetchAddEvent)} (history : History before labels after)
    (valid : WellFormed before) (target : CellId64) (cell : Atomics64.Cell)
    (live : before.cells target = some cell) (identifier : FetchAddEvent → Id)
    (thread : FetchAddEvent → Thread) (prior final : Word)
    (readBefore : loadQWord (toMemory before.legacy.shared.resources.space) cell.address = .ok prior)
    (readAfter : loadQWord (toMemory after.legacy.shared.resources.space) cell.address = .ok final) :
    final.toNat = (prior.toNat +
      Concurrency.ModuloCounter.inputSum (selectedCalls target identifier thread labels)) % 2^64 :=
  (history.sequential valid target cell live identifier thread prior final readBefore readAfter).total

theorem History.final_fold {Id Thread : Type} {before after : Atomics64.State}
    {labels : List (Option FetchAddEvent)} (history : History before labels after)
    (valid : WellFormed before) (target : CellId64) (cell : Atomics64.Cell)
    (live : before.cells target = some cell) (identifier : FetchAddEvent → Id)
    (thread : FetchAddEvent → Thread) (prior final : Word)
    (readBefore : loadQWord (toMemory before.legacy.shared.resources.space) cell.address = .ok prior)
    (readAfter : loadQWord (toMemory after.legacy.shared.resources.space) cell.address = .ok final) :
    final = (selectedCalls target identifier thread labels).foldl (fun value call => value + call.input) prior :=
  (history.sequential valid target cell live identifier thread prior final readBefore readAfter).final_fold

end EDSL.OS.AtomicFetchAddHistory64

#audit_edsl
