/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Check
import tests.C23MessagePassing
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.C23AtomicCheck
open Concurrency.C23Atomic
open Concurrency.C23Atomic.Check

/-- A supplied finite certificate, with edges stated independently for each
litmus. No transitive closure or semantic relation is consulted by this helper. -/
def matrix (size : Nat) (edges : List (Nat × Nat)) : Matrix :=
  (List.range size).map fun first =>
    (List.range size).map fun second => edges.contains (first, second)

/-- A release, an unchanged-value foreign relaxed RMW, and an acquire from the
RMW. Modification ranks have gaps; list indices and ranks are distinct. -/
def sparseRMW : Table Nat Nat where
  events := [⟨none, 0, .initialize 0⟩, ⟨some 11, 0, .store .release 7⟩,
    ⟨some 12, 0, .rmw .relaxed 7 7⟩, ⟨some 13, 0, .load .acquire 7⟩]
  sources := [none, none, some 1, some 2]
  ranks := [0, 7, 19, 0]

def sparseHB : Matrix := matrix 4 [(1, 3)]

theorem sparse_unchanged_rmw_is_accepted : check sparseRMW sparseHB = true := by decide

/-- One shared soundness theorem replaces a client proof for every legality
field. The actual source writer is the RMW at event 2, despite unchanged bits. -/
theorem sparse_unchanged_rmw_is_legal : Legal sparseRMW.toCandidate :=
  check_sound sparseRMW sparseHB sparse_unchanged_rmw_is_accepted

theorem missing_required_synchronization_is_rejected :
    check sparseRMW (matrix 4 []) = false := by decide

/-- Each thread stores to one object and then reads the other's initial word.
A global sequentially consistent latest-write rule would reject this outcome. -/
def storeBuffering : Table Nat Nat where
  events := [⟨none, 0, .initialize 0⟩, ⟨none, 1, .initialize 0⟩,
    ⟨some 11, 0, .store .relaxed 1⟩, ⟨some 11, 1, .load .relaxed 0⟩,
    ⟨some 12, 1, .store .relaxed 1⟩, ⟨some 12, 0, .load .relaxed 0⟩]
  sources := [none, none, none, some 1, none, some 0]
  ranks := [0, 0, 7, 0, 19, 0]

theorem relaxed_store_buffering_is_accepted :
    check storeBuffering (matrix 6 [(2, 3), (4, 5)]) = true := by decide

/-- Constant relaxed stores permit this supplied source graph. The first read
selects event 5, so requiring writerIndex < readerIndex would reject it. This
is an atomic-source graph claim, without a TSO realizability claim. -/
def laterIndexRF : Table Nat Nat where
  events := [⟨none, 0, .initialize 0⟩, ⟨none, 1, .initialize 0⟩,
    ⟨some 11, 1, .load .relaxed 1⟩, ⟨some 11, 0, .store .relaxed 1⟩,
    ⟨some 12, 0, .load .relaxed 1⟩, ⟨some 12, 1, .store .relaxed 1⟩]
  sources := [none, none, some 5, none, some 3, none]
  ranks := [0, 0, 0, 7, 0, 19]

theorem source_rf_may_have_larger_list_index :
    check laterIndexRF (matrix 6 [(2, 3), (4, 5)]) = true := by decide

/-- The complete publication chain includes source SB, actual qualifying SW,
and their transitive consequences. Payload read selects the old initializer. -/
def stalePayload : Table Nat Nat where
  events := C23MessagePassing.stale.events
  sources := [none, none, none, none, some 3, some 0]
  ranks := [0, 0, 1, 1, 0, 0]

def publicationHB : Matrix := matrix 6 [(2, 3), (3, 4), (4, 5), (2, 4), (2, 5), (3, 5)]

theorem coherent_publication_rejects_stale_payload :
    checkWellFormed stalePayload = true ∧
    checkHappensBefore stalePayload publicationHB = true ∧
    check stalePayload publicationHB = false := by decide

/-- An RMW cannot read the initial value across a preceding actual write,
although the supplied read/write values and structural graph are consistent. -/
def skippedRMW : Table Nat Nat where
  events := C23MessagePassing.skippedPredecessor.events
  sources := [none, none, some 0]
  ranks := [0, 7, 19]

theorem actual_intervening_write_rejects_rmw_source :
    checkWellFormed skippedRMW = true ∧
    checkHappensBefore skippedRMW (matrix 3 []) = true ∧
    check skippedRMW (matrix 3 []) = false := by decide

/-- Two identical event records still denote separate writes. Sequencing the
later write before the read excludes the earlier source even when bits match. -/
def repeatedWrites (writer : Nat) : Table Nat Nat where
  events := [⟨none, 0, .initialize 0⟩, ⟨some 11, 0, .store .relaxed 0⟩,
    ⟨some 11, 0, .store .relaxed 0⟩, ⟨some 11, 0, .load .relaxed 0⟩]
  sources := [none, none, none, some writer]
  ranks := [0, 7, 19, 0]

def repeatedHB : Matrix := matrix 4 [(1, 2), (1, 3), (2, 3)]

theorem identical_records_keep_writer_identity :
    check (repeatedWrites 2) repeatedHB = true ∧
    checkWellFormed (repeatedWrites 1) = true ∧
    checkHappensBefore (repeatedWrites 1) repeatedHB = true ∧
    check (repeatedWrites 1) repeatedHB = false := by decide

/-- Extra RF entries outside the event domain must not disappear by truncation. -/
theorem unused_outside_source_is_rejected :
    check { sparseRMW with sources := sparseRMW.sources ++ [some 0] } sparseHB = false := by decide

theorem absent_writer_is_rejected :
    check { sparseRMW with sources := [none, none, some 99, some 2] } sparseHB = false := by decide

theorem truncated_relation_certificate_is_rejected : check sparseRMW [] = false := by decide

/-- Ordinary clients can supply only tables: the relation proposal is checked
through the same sound admission theorem before legality is exposed. -/
theorem generated_certificate_admits_sparse_rmw : Legal sparseRMW.toCandidate :=
  certify_sound sparseRMW (by decide)

theorem generated_certificates_preserve_weak_source_ordering :
    certify storeBuffering = true ∧ certify laterIndexRF = true := by decide

theorem generated_certificate_rejects_stale_publication : certify stalePayload = false := by decide

/-- Once a thread observes a modification, its next read cannot move backwards
in modification order. All stored and read bits agree, so only writer identity
and order distinguish these outcomes. Plain loads isolate read-read coherence. -/
def consecutiveReads (secondSource : Nat) : Table Nat Nat where
  events := [⟨none, 0, .initialize 0⟩, ⟨some 11, 0, .store .relaxed 0⟩,
    ⟨some 12, 0, .load .relaxed 0⟩, ⟨some 12, 0, .load .relaxed 0⟩]
  sources := [none, none, some 1, some secondSource]
  ranks := [0, 7, 0, 0]

theorem consecutive_reads_cannot_return_to_an_older_writer :
    check (consecutiveReads 1) (matrix 4 [(2, 3)]) = true ∧
    checkWellFormed (consecutiveReads 0) = true ∧
    checkHappensBefore (consecutiveReads 0) (matrix 4 [(2, 3)]) = true ∧
    checkConditions (consecutiveReads 0) (matrix 4 [(2, 3)]) = false ∧
    check (consecutiveReads 0) (matrix 4 [(2, 3)]) = false := by decide

/-- A read sequenced before a write must observe a strictly earlier
modification. The observed foreign store may have a later modification rank
despite occurring earlier in the supplied event list. -/
def readBeforeWrite (observed : Nat) : Table Nat Nat where
  events := [⟨none, 0, .initialize 0⟩, ⟨some 11, 0, .store .relaxed 0⟩,
    ⟨some 12, 0, .load .relaxed 0⟩, ⟨some 12, 0, .store .relaxed 0⟩]
  sources := [none, none, some observed, none]
  ranks := [0, 19, 0, 7]

theorem observed_writer_must_precede_the_later_hb_store :
    check (readBeforeWrite 0) (matrix 4 [(2, 3)]) = true ∧
    checkWellFormed (readBeforeWrite 1) = true ∧
    checkHappensBefore (readBeforeWrite 1) (matrix 4 [(2, 3)]) = true ∧
    checkConditions (readBeforeWrite 1) (matrix 4 [(2, 3)]) = false ∧
    check (readBeforeWrite 1) (matrix 4 [(2, 3)]) = false := by decide

/-- Sequencing two writes constrains their modification order even when they
store equal bits. Plain stores isolate write-write coherence. -/
def consecutiveWrites (firstRank secondRank : Nat) : Table Nat Nat where
  events := [⟨none, 0, .initialize 0⟩, ⟨some 11, 0, .store .relaxed 0⟩,
    ⟨some 11, 0, .store .relaxed 0⟩]
  sources := [none, none, none]
  ranks := [0, firstRank, secondRank]

theorem hb_writes_cannot_reverse_modification_order :
    check (consecutiveWrites 7 19) (matrix 3 [(1, 2)]) = true ∧
    checkWellFormed (consecutiveWrites 19 7) = true ∧
    checkHappensBefore (consecutiveWrites 19 7) (matrix 3 [(1, 2)]) = true ∧
    checkConditions (consecutiveWrites 19 7) (matrix 3 [(1, 2)]) = false ∧
    check (consecutiveWrites 19 7) (matrix 3 [(1, 2)]) = false := by decide

/-- Equal payloads do not let an RMW skip an actual preceding modification.
Distinct threads avoid adding a coherence edge that could mask this check. -/
def unchangedRMWSource (observed : Nat) : Table Nat Nat where
  events := [⟨none, 0, .initialize 0⟩, ⟨some 11, 0, .store .relaxed 0⟩,
    ⟨some 12, 0, .rmw .relaxed 0 0⟩]
  sources := [none, none, some observed]
  ranks := [0, 7, 19]

theorem equal_payloads_do_not_hide_a_skipped_rmw_predecessor :
    check (unchangedRMWSource 1) (matrix 3 []) = true ∧
    checkWellFormed (unchangedRMWSource 0) = true ∧
    checkHappensBefore (unchangedRMWSource 0) (matrix 3 []) = true ∧
    checkConditions (unchangedRMWSource 0) (matrix 3 []) = false ∧
    check (unchangedRMWSource 0) (matrix 3 []) = false := by decide

/-- The release/acquire edge followed by same-thread sequencing requires the
transitive release-to-store edge, even though both generating edges are present. -/
def synchronizationChain : Table Nat Nat where
  events := [⟨none, 0, .initialize 0⟩, ⟨some 11, 0, .store .release 1⟩,
    ⟨some 12, 0, .load .acquire 1⟩, ⟨some 12, 0, .store .relaxed 2⟩]
  sources := [none, none, some 1, none]
  ranks := [0, 7, 0, 19]

theorem generating_hb_edges_do_not_replace_transitive_closure :
    check synchronizationChain (matrix 4 [(1, 2), (2, 3), (1, 3)]) = true ∧
    checkWellFormed synchronizationChain = true ∧
    checkConditions synchronizationChain (matrix 4 [(1, 2), (2, 3)]) = true ∧
    checkHappensBefore synchronizationChain (matrix 4 [(1, 2), (2, 3)]) = false ∧
    check synchronizationChain (matrix 4 [(1, 2), (2, 3)]) = false := by decide

/-- Successful publication observes the payload written before the release.
Its certificate needs transitive edges spanning both threads; accepting it
tests that automatic proposal generation actually closes the generating edges. -/
def coherentPayload : Table Nat Nat where
  events := [⟨none, 0, .initialize 0⟩, ⟨none, 1, .initialize 0⟩,
    ⟨some 11, 0, .store .relaxed 42⟩, ⟨some 11, 1, .store .release 1⟩,
    ⟨some 12, 1, .load .acquire 1⟩, ⟨some 12, 0, .load .relaxed 42⟩]
  sources := [none, none, none, none, some 3, some 2]
  ranks := [0, 0, 1, 1, 0, 0]

theorem generated_certificate_admits_transitive_publication :
    check coherentPayload publicationHB = true ∧ certify coherentPayload = true := by decide

theorem relation_certificate_cannot_include_a_self_edge :
    checkWellFormed sparseRMW = true ∧
    checkHappensBefore sparseRMW (matrix 4 [(1, 3), (0, 0)]) = false ∧
    check sparseRMW (matrix 4 [(1, 3), (0, 0)]) = false := by decide

/-- Shortening an all-false row preserves every represented edge, but it is
still an invalid certificate: default-false lookup cannot repair its shape. -/
def raggedHB : Matrix :=
  [[false, false, false], [false, false, false, true],
    [false, false, false, false], [false, false, false, false]]

theorem relation_certificate_requires_every_column :
    checkWellFormed sparseRMW = true ∧
    checkConditions sparseRMW raggedHB = true ∧
    checkHappensBefore sparseRMW raggedHB = false ∧
    check sparseRMW raggedHB = false := by decide

/-- Dropped metadata would default to the same `none` source or zero read rank.
Exact table shape must reject it even when those defaults look harmless. -/
theorem default_metadata_does_not_admit_short_tables :
    checkWellFormed { consecutiveWrites 7 19 with sources := [none, none] } = false ∧
    checkWellFormed { sparseRMW with ranks := [0, 7, 19] } = false := by decide

end EDSL.Tests.C23AtomicCheck

#print axioms EDSL.Concurrency.C23Atomic.Check.check_sound
#print axioms EDSL.Tests.C23AtomicCheck.sparse_unchanged_rmw_is_legal
#audit_edsl
