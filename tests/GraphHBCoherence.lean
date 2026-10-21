/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.GraphHappensBefore
import tests.GraphOperationalCoherence
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphHBCoherence
import EDSL.Audit

/-!
Acquiring clients of universal actual-execution HB coherence and legality.
The existing foreign-RMW and own-forwarded/equal-word scans are reused without
per-pair coherence proofs or graph legality checker certificates.

The cross-cell client reannotates the immutable offset-151 run: initialize A=3
and B=7, publish A=0, perform an unchanged-value B RMW, then acquire B and read A.
`Graph.build` receives the existing complete event/publication inputs and live
manifest. The selected B writer must be the RMW, despite its initial-equal bits.
Concrete RF, release membership and sequencing witnesses establish the actual
cross-cell publication chain. Generic message passing then bounds the payload
source rank and forces its value using the maximal actual A write. Neither the
payload result nor its source identity is an input to that argument.

Scope: the finite modeled atomic fragment of these sharedCell scalar-RAM,
long-mode/CET-off executions with stable initialized resources and explicitly
declared interface annotations. No full C23, source/compiler preservation,
native/kernel execution, fairness, build totality or corpus increment is claimed.
-/

set_option autoImplicit false

namespace EDSL.Tests.GraphHBCoherence
open X86 OS.TSO64 OS.TSO64.C23Projection AtomicTrace
open Concurrency.C23Atomic

/-- Reuse all actual execution invariants; only the annotation-dependent
structural mapping must be supplied for the new table. -/
private theorem reannotate {initial : OS.TSO64.State} {actions : List Action}
    {profile : Profile} {offset : Nat} {run : AtomicTrace.Result}
    {initials : List Initials.Entry} {oldOrders orders : Orders}
    {oldTable table : Graph.Table}
    (previous : Graph.Executed initial actions profile offset run initials oldOrders oldTable)
    (mapped : Graph.Built (Graph.runInputs initials run offset) orders table) :
    Graph.Executed initial actions profile offset run initials orders table :=
  ⟨previous.valid, previous.sequenced, previous.scanned, previous.quiescent, mapped⟩

private theorem get_ok {α : Type} (attempt : Option α)
    (accepted : attempt.isSome = true) : attempt = some (attempt.get accepted) := by
  cases attempt with
  | none => cases accepted
  | some value => rfl

namespace ForeignRMW

theorem hb_coherent : Coherent GraphHappensBefore.ForeignRMW.table.toCandidate :=
  GraphHappensBefore.ForeignRMW.executed.hbCoherent

/-- Includes the foreign-thread release-sequence member and acquiring RMWs. -/
theorem finite_fragment_legal : Legal GraphHappensBefore.ForeignRMW.table.toCandidate :=
  GraphHappensBefore.ForeignRMW.executed.legal

end ForeignRMW

namespace ForwardedLoads

theorem hb_coherent : Coherent GraphHappensBefore.ForwardedLoads.table.toCandidate :=
  GraphHappensBefore.ForwardedLoads.executed.hbCoherent

/-- Includes own forwarding before drain and the peer's older equal-bit source. -/
theorem finite_fragment_legal : Legal GraphHappensBefore.ForwardedLoads.table.toCandidate :=
  GraphHappensBefore.ForwardedLoads.executed.legal

end ForwardedLoads

namespace CrossCell

/-- These are primitive-interface annotations, rather than ISA decoding rules. -/
def interfaceOrders : Orders where
  read _ _ := .acquire
  write _ _ := .release
  rmw _ _ := .acqRel

def buildAttempt : Option Graph.Table :=
  Graph.build GraphOperationalCoherence.CrossCell.inputs interfaceOrders

theorem build_succeeds : buildAttempt.isSome = true := by decide +kernel

def table : Graph.Table := buildAttempt.get build_succeeds

theorem table_actual :
    Graph.build GraphOperationalCoherence.CrossCell.inputs interfaceOrders = some table :=
  get_ok buildAttempt build_succeeds

theorem built : Graph.Built GraphOperationalCoherence.CrossCell.inputs interfaceOrders table :=
  Graph.build_sound table_actual

theorem executed : Graph.Executed WriteViewRanks.Whole.initial WriteViewRanks.Whole.actions
    .sharedCell 151 WriteViewRanks.Whole.scanned GraphOperationalCoherence.CrossCell.manifest
    interfaceOrders table :=
  reannotate GraphOperationalCoherence.CrossCell.executed built

theorem hb_coherent : Coherent table.toCandidate := executed.hbCoherent

theorem finite_fragment_legal : Legal table.toCandidate := executed.legal

/-- Independent expectations for the computed full graph, including both
equal-valued B modifications, source identities, rank gaps and explicit orders. -/
theorem literal_mapping :
    table.events = [⟨none, ⟨0⟩, .initialize 3⟩, ⟨none, ⟨1⟩, .initialize 7⟩,
      ⟨some 0, ⟨0⟩, .store .release 0⟩, ⟨some 0, ⟨1⟩, .rmw .acqRel 7 7⟩,
      ⟨some 1, ⟨1⟩, .load .acquire 7⟩, ⟨some 1, ⟨0⟩, .load .acquire 0⟩] ∧
      table.sources = [none, none, none, some 1, some 3, some 2] ∧
      table.ranks = [0, 0, 153, 154, 0, 0] := by
  decide +kernel

theorem event_count : table.events.length = 6 := by rw [literal_mapping.1]; rfl

def payloadStore : table.Index := ⟨2, by rw [event_count]; decide⟩
def releaseHead : table.Index := ⟨3, by rw [event_count]; decide⟩
def acquiringB : table.Index := ⟨4, by rw [event_count]; decide⟩
def payloadLoad : table.Index := ⟨5, by rw [event_count]; decide⟩

theorem B_acquire_source : ReadsFrom table.toCandidate 4 3 :=
  (Check.rf_iff table acquiringB releaseHead).mpr (by decide +kernel)

/-- Equal bits cannot redirect the acquire to initial B and erase its release. -/
theorem unchanged_B_not_initial : ¬ ReadsFrom table.toCandidate 4 1 :=
  not_readsFrom_of_ne B_acquire_source (by decide)

theorem B_acquires : Acquires table.toCandidate 4 :=
  (Check.acquires_iff table acquiringB).mpr (by decide +kernel)

theorem B_release_member : ReleaseMember table.toCandidate 3 3 :=
  (Check.releaseMember_iff table releaseHead releaseHead).mpr (by decide +kernel)

theorem before_release : SeqBefore table.toCandidate 2 3 :=
  (Check.seq_iff table payloadStore releaseHead).mpr (by decide +kernel)

theorem after_acquire : SeqBefore table.toCandidate 4 5 :=
  (Check.seq_iff table acquiringB payloadLoad).mpr (by decide +kernel)

/-- The path crosses objects: store A -> release RMW B -> acquire B -> load A.
It is derived from concrete generating edges, independently of Legal. -/
theorem publication_hb : HappensBefore table.toCandidate 2 5 :=
  publication_chain before_release B_acquires B_acquire_source B_release_member after_acquire

theorem payload_written : Writes table.toCandidate 2 ⟨0⟩ (0 : Word) :=
  (table.writes_iff payloadStore ⟨0⟩ 0).mpr (by decide +kernel)

theorem payload_rank : table.rank 2 = 153 := by
  simp [Check.Table.rank, literal_mapping.2.2]

/-- Maximality ranges over actual writes to A; B's later rank is irrelevant.
This finite access/rank fact supplies no coherence or legality certificate. -/
theorem payload_last_write (index : Nat) (value : Word)
    (written : Writes table.toCandidate index ⟨0⟩ value) :
    ¬ ModBefore table.toCandidate 2 index := by
  let writer : table.Index := ⟨index, table.writes_bound written⟩
  have access := (table.writes_iff writer ⟨0⟩ value).mp written
  have maximal : ∀ actual : table.Index,
      (table.node actual).object = ⟨0⟩ →
      (table.node actual).access.writeValue.isSome = true →
      table.rank actual.val ≤ table.rank 2 := by
    decide +kernel
  intro later
  obtain ⟨_, _, _, _, _, strict⟩ := later
  exact Nat.not_lt_of_ge (maximal writer access.1 (Option.isSome_of_eq_some access.2)) strict

/-- The read value remains arbitrary and its writer is obtained from universal
well-formedness. Message passing, rather than a desired RF/result premise,
supplies the source lower bound and the value forced by maximality. -/
theorem message_passing_payload {observed : Word}
    (read : Reads table.toCandidate 5 ⟨0⟩ observed) :
    observed = 0 ∧ ∃ writer, ReadsFrom table.toCandidate 5 writer ∧
      153 ≤ table.rank writer := by
  obtain ⟨writer, source⟩ := finite_fragment_legal.wellFormed.readsSource 5 ⟨0⟩ observed read
  have lower := finite_fragment_legal.message_passing_not_older payload_written before_release
    B_acquires B_acquire_source B_release_member after_acquire read source
  have value := finite_fragment_legal.message_passing_value payload_written payload_last_write
    before_release B_acquires B_acquire_source B_release_member after_acquire read source
  refine ⟨value, writer, source, ?_⟩
  simpa only [Check.Table.toCandidate, payload_rank] using lower

/-- Recover a read without specifying its result, then apply the generic
message-passing client. The selected source is not assumed to be row two. -/
theorem actual_payload :
    ∃ observed, Reads table.toCandidate 5 ⟨0⟩ observed ∧ observed = 0 ∧
      ∃ writer, ReadsFrom table.toCandidate 5 writer ∧ 153 ≤ table.rank writer := by
  have reading : (table.node payloadLoad).object = ⟨0⟩ ∧
      (table.node payloadLoad).access.readValue.isSome = true := by decide +kernel
  obtain ⟨observed, loaded⟩ := Option.isSome_iff_exists.mp reading.2
  have read : Reads table.toCandidate 5 ⟨0⟩ observed :=
    (table.reads_iff payloadLoad ⟨0⟩ observed).mpr ⟨reading.1, loaded⟩
  exact ⟨observed, read, message_passing_payload read⟩

end CrossCell

/-- The existing independent negative control retains the foreign plain-write
interruption even when a later RMW writes equal bits. -/
theorem foreign_plain_write_breaks_sequence :
    ¬ ReleaseMember C23AtomicEvents.interrupted 1 4 ∧
      ¬ SynchronizesWith C23AtomicEvents.interrupted 1 5 :=
  GraphHappensBefore.foreign_plain_write_breaks_sequence

end EDSL.Tests.GraphHBCoherence

#print axioms EDSL.Tests.GraphHBCoherence.ForeignRMW.hb_coherent
#print axioms EDSL.Tests.GraphHBCoherence.ForeignRMW.finite_fragment_legal
#print axioms EDSL.Tests.GraphHBCoherence.ForwardedLoads.hb_coherent
#print axioms EDSL.Tests.GraphHBCoherence.ForwardedLoads.finite_fragment_legal
#print axioms EDSL.Tests.GraphHBCoherence.CrossCell.built
#print axioms EDSL.Tests.GraphHBCoherence.CrossCell.executed
#print axioms EDSL.Tests.GraphHBCoherence.CrossCell.hb_coherent
#print axioms EDSL.Tests.GraphHBCoherence.CrossCell.finite_fragment_legal
#print axioms EDSL.Tests.GraphHBCoherence.CrossCell.literal_mapping
#print axioms EDSL.Tests.GraphHBCoherence.CrossCell.B_acquire_source
#print axioms EDSL.Tests.GraphHBCoherence.CrossCell.unchanged_B_not_initial
#print axioms EDSL.Tests.GraphHBCoherence.CrossCell.publication_hb
#print axioms EDSL.Tests.GraphHBCoherence.CrossCell.payload_last_write
#print axioms EDSL.Tests.GraphHBCoherence.CrossCell.message_passing_payload
#print axioms EDSL.Tests.GraphHBCoherence.CrossCell.actual_payload
#print axioms EDSL.Tests.GraphHBCoherence.foreign_plain_write_breaks_sequence
#audit_edsl
