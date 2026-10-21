/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.ExecutionViews.Query
import EDSL.OS.TSO64.ExecutionViews.Monotone
import tests.PendingPublicationViews
import tests.MixedWriteOrder

/-!
Metadata queries on the production execution and prefix states already used by
PendingPublicationViews. The literal trajectories below specify publication
positions independently of the query. An ordinary issue, repeated equal managed
stores, peer publications, RET and the transition from selected pending writer
to published writer all retain their original positions at stream offset 37.

The full `Execution` is established from checked setup and actual attachment,
not from an assumed well-formed future state. Query soundness connects the
literal numbers to actual `At` witnesses, and the general monotonicity theorem
is instantiated at arbitrary ordered cuts of this same execution.

These are finite sharedCell scalar-RAM, long-mode, CET-off metadata clients.
They establish no fairness, source-C23 legality or physical/native execution.
-/

set_option autoImplicit false

namespace EDSL.Tests.ExecutionViews
open X86 OS.TSO64 OS.TSO64.ExecutionViews PendingPublicationViews

private theorem output_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) :
    attempt = .ok (attempt.toOption.get accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

private theorem found_ok {α : Type} (value : Option α) (present : value.isSome = true) :
    value = some (value.get present) := by
  cases value with
  | none => cases present
  | some value => rfl

private theorem empty_valid (world : World) (valid : OS.Atomics64.WellFormed world) :
    WellFormed ⟨world, []⟩ .sharedCell := by
  refine ⟨valid, ?_⟩
  intro worker absent
  cases absent

/-- Extract both real attach successes from the existing setup. The checked
manager supplies world validity before either worker is attached. -/
private theorem shared_start_valid {first second old deltaA deltaB : Word}
    {offsetA offsetB : Nat} {state : OS.TSO64.State}
    (success : TSO64SharedCells.start first second old deltaA deltaB offsetA offsetB = .ok state) :
    WellFormed state .sharedCell := by
  cases setup : TSO64.fixture first second old with
  | error fault =>
    simp [TSO64SharedCells.start, setup, Except.mapError] at success
  | ok ready =>
    let a : Context :=
      { TSO64.context 262144 131072 deltaA 5 with rip := 393216 + BitVec.ofNat 64 offsetA }
    let b : Context :=
      { TSO64.context 327680 196608 deltaB 5 with rip := 393216 + BitVec.ofNat 64 offsetB }
    have attached : (do
        let one ← attach ⟨ready.checked.world, []⟩ 11 a ready.codeA ready.callerA
          [ready.dataA] [ready.atomicA]
        attach one 12 b ready.codeB ready.callerB [ready.dataB] [ready.atomicB]) = .ok state := by
      simpa only [TSO64SharedCells.start, setup, Except.mapError, ok_bind] using success
    cases one : attach ⟨ready.checked.world, []⟩ 11 a ready.codeA ready.callerA
        [ready.dataA] [ready.atomicA] with
    | error fault => simp [one] at attached
    | ok firstState =>
      have final : attach firstState 12 b ready.codeB ready.callerB
          [ready.dataB] [ready.atomicB] = .ok state := by
        simpa only [one, ok_bind] using attached
      exact attach_valid_for .sharedCell
        (attach_valid_for .sharedCell (empty_valid _ ready.checked.valid) one) final

theorem initial_actual : initialAttempt = .ok initial :=
  output_ok initialAttempt initial_succeeds

theorem initial_valid : WellFormed initial .sharedCell :=
  shared_start_valid initial_actual

/-- This is the imported actual execution with the previously missing global
well-formedness derived above. No desired query result occurs in its premises. -/
theorem execution : Execution initial actions result .sharedCell :=
  ⟨scheduled, initial_valid, initial_sequenced, final_quiescent⟩

def ownWorker : Worker := (initial.workers[0]?).get (by decide +kernel)
def peerWorker : Worker := (initial.workers[1]?).get (by decide +kernel)

theorem own_live : initial.workers[0]? = some ownWorker := found_ok _ _
theorem peer_live : initial.workers[1]? = some peerWorker := found_ok _ _

/-- Original authority belongs to worker zero. The queried worker may instead
be its peer; target authority need not be owned by the viewed worker. -/
theorem target_current : Queue.Current initial.world ownWorker.resources ownReference := by
  decide +kernel

def queried (cut tid : Nat) : Option Nat :=
  query (atCut cut).1 result.2 cut tid ownReference 37 PublishedHistory.empty

-- Stage the independent observations separately by cut for the fixed
-- heartbeat and recursion limits.
private theorem cut0 : queried 0 0 = some 0 ∧ queried 0 1 = some 0 := by decide +kernel
private theorem cut1 : queried 1 0 = some 0 ∧ queried 1 1 = some 0 := by decide +kernel
private theorem cut2 : queried 2 0 = some 45 ∧ queried 2 1 = some 0 := by decide +kernel
private theorem cut3 : queried 3 0 = some 45 ∧ queried 3 1 = some 42 := by decide +kernel
private theorem cut4 : queried 4 0 = some 48 ∧ queried 4 1 = some 42 := by decide +kernel
private theorem cut5 : queried 5 0 = some 48 ∧ queried 5 1 = some 42 := by decide +kernel
private theorem cut6 : queried 6 0 = some 48 ∧ queried 6 1 = some 42 := by decide +kernel
private theorem cut7 : queried 7 0 = some 48 ∧ queried 7 1 = some 42 := by decide +kernel
private theorem cut8 : queried 8 0 = some 48 ∧ queried 8 1 = some 45 := by decide +kernel
private theorem cut9 : queried 9 0 = some 48 ∧ queried 9 1 = some 47 := by decide +kernel
private theorem cut10 : queried 10 0 = some 48 ∧ queried 10 1 = some 47 := by decide +kernel
private theorem cut11 : queried 11 0 = some 48 ∧ queried 11 1 = some 48 := by decide +kernel
private theorem cut12 : queried 12 0 = some 48 ∧ queried 12 1 = some 48 := by decide +kernel

def trajectory (tid : Nat) : List (Option Nat) :=
  (List.range 13).map fun cut => queried cut tid

def expectedOwn : List Nat := [0, 0, 45, 45, 48, 48, 48, 48, 48, 48, 48, 48, 48]
def expectedPeer : List Nat := [0, 0, 0, 42, 42, 42, 42, 42, 45, 47, 47, 48, 48]

/-- The newer equal-valued own writer advances to 48 before any publication,
and stays there across peer publication, RET, ordinary drain and its own drain. -/
theorem literal_own_trajectory : trajectory 0 = expectedOwn.map some := by
  change [queried 0 0, queried 1 0, queried 2 0, queried 3 0, queried 4 0,
    queried 5 0, queried 6 0, queried 7 0, queried 8 0, queried 9 0,
    queried 10 0, queried 11 0, queried 12 0] = _
  simp only [cut0.1, cut1.1, cut2.1, cut3.1, cut4.1, cut5.1, cut6.1, cut7.1,
    cut8.1, cut9.1, cut10.1, cut11.1, cut12.1, expectedOwn, List.map_cons, List.map_nil]

/-- The peer first has its own pending rank 42, later observes publication 45,
then selects its second own rank 47 and finally observes publication 48. -/
theorem literal_peer_trajectory : trajectory 1 = expectedPeer.map some := by
  change [queried 0 1, queried 1 1, queried 2 1, queried 3 1, queried 4 1,
    queried 5 1, queried 6 1, queried 7 1, queried 8 1, queried 9 1,
    queried 10 1, queried 11 1, queried 12 1] = _
  simp only [cut0.2, cut1.2, cut2.2, cut3.2, cut4.2, cut5.2, cut6.2, cut7.2,
    cut8.2, cut9.2, cut10.2, cut11.2, cut12.2, expectedPeer, List.map_cons, List.map_nil]

/-- Successful queries are connected to independently obtained actual views,
using the full execution and the imported actual prefix states. -/
theorem queried_at {cut tid value : Nat} {worker : Worker}
    (live : initial.workers[tid]? = some worker) (answer : queried cut tid = some value) :
    Nonempty (At initial actions result .sharedCell cut tid ownReference 37
      PublishedHistory.empty value) :=
  query_sound execution live (prefix_exact cut) target_current answer

private theorem trajectory_at {cut tid value : Nat} {worker : Worker}
    (live : initial.workers[tid]? = some worker)
    (entry : (trajectory tid)[cut]? = some (some value)) :
    Nonempty (At initial actions result .sharedCell cut tid ownReference 37
      PublishedHistory.empty value) := by
  have bound : cut < 13 := by
    have present := (List.getElem_of_getElem? entry).1
    simpa only [trajectory, List.length_map, List.length_range] using present
  have answer : queried cut tid = some value := by
    simpa only [trajectory, List.getElem?_map, List.getElem?_range bound,
      Option.map_some, Option.some.injEq] using entry
  exact queried_at live answer

/-- Every literal own trajectory entry, rather than just a selected sample,
is an actual view obtained through query soundness. -/
theorem literal_own_views {cut value : Nat} (listed : expectedOwn[cut]? = some value) :
    Nonempty (At initial actions result .sharedCell cut 0 ownReference 37
      PublishedHistory.empty value) := by
  apply trajectory_at own_live
  simp only [literal_own_trajectory, List.getElem?_map, listed, Option.map_some]

theorem literal_peer_views {cut value : Nat} (listed : expectedPeer[cut]? = some value) :
    Nonempty (At initial actions result .sharedCell cut 1 ownReference 37
      PublishedHistory.empty value) := by
  apply trajectory_at peer_live
  simp only [literal_peer_trajectory, List.getElem?_map, listed, Option.map_some]

/-- Arbitrary ordered cuts and successful queried values of the actual full
execution inherit monotonicity. View order is a conclusion, never a premise. -/
theorem queried_values_monotone {first last tid firstValue lastValue : Nat} {worker : Worker}
    (live : initial.workers[tid]? = some worker) (ordered : first ≤ last)
    (earlier : queried first tid = some firstValue) (later : queried last tid = some lastValue) :
    firstValue ≤ lastValue := by
  obtain ⟨earlierView⟩ := queried_at live earlier
  obtain ⟨laterView⟩ := queried_at live later
  exact earlierView.monotone execution (PublishedOrder.prior_empty 37) ordered laterView

theorem own_queries_monotone {first last firstValue lastValue : Nat} (ordered : first ≤ last)
    (earlier : queried first 0 = some firstValue) (later : queried last 0 = some lastValue) :
    firstValue ≤ lastValue :=
  queried_values_monotone own_live ordered earlier later

theorem peer_queries_monotone {first last firstValue lastValue : Nat} (ordered : first ≤ last)
    (earlier : queried first 1 = some firstValue) (later : queried last 1 = some lastValue) :
    firstValue ≤ lastValue :=
  queried_values_monotone peer_live ordered earlier later

/-- An earlier real equal-valued own drain and real peer drains do not replace
the missing selected occurrence. Incomplete observations therefore reject. -/
theorem missing_selected_publication :
    query (atCut 4).1 (result.2.take 10) 4 0 ownReference 37 PublishedHistory.empty = none := by
  decide +kernel

/-- These synthetic drains each corrupt one part of the selected identity.
No authority or executable provenance is claimed for this negative input. -/
def inexactDrains : List Observation :=
  [.drained 1 (.managed ownReference 0 2),
    .drained 0 (.managed { ownReference with identifier := ⟨99⟩ } 0 2),
    .drained 0 (.managed ownReference 1 2),
    .drained 0 (.managed ownReference 0 1)]

theorem inexact_publications_rejected :
    query (atCut 4).1 inexactDrains 4 0 ownReference 37 PublishedHistory.empty = none := by
  decide +kernel

/-- Arbitrary synthetic metadata can select an ordinary same-address qword.
The query rejects that unsupported source instead of manufacturing a view. -/
def ordinarySelection : OS.TSO64.State :=
  { initial with workers := [{ ownWorker with pending :=
      [.ordinary ownReference.cell.ticket ⟨ownReference.cell.address, .qword 0⟩] }] }

theorem ordinary_selection_rejected :
    query ordinarySelection result.2 4 0 ownReference 37 PublishedHistory.empty = none := by
  decide +kernel

theorem missing_worker_rejected : queried 4 99 = none := by decide +kernel

end EDSL.Tests.ExecutionViews

#print axioms EDSL.Tests.ExecutionViews.initial_valid
#print axioms EDSL.Tests.ExecutionViews.execution
#print axioms EDSL.Tests.ExecutionViews.literal_own_trajectory
#print axioms EDSL.Tests.ExecutionViews.literal_peer_trajectory
#print axioms EDSL.Tests.ExecutionViews.literal_own_views
#print axioms EDSL.Tests.ExecutionViews.literal_peer_views
#print axioms EDSL.Tests.ExecutionViews.queried_values_monotone
#print axioms EDSL.Tests.ExecutionViews.missing_selected_publication
#print axioms EDSL.Tests.ExecutionViews.inexact_publications_rejected
#print axioms EDSL.Tests.ExecutionViews.ordinary_selection_rejected
#print axioms EDSL.Tests.ExecutionViews.missing_worker_rejected
#audit_edsl
