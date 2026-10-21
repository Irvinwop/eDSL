/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphCapture

/-!
Raw initialized capture from actual production execution. Scanner erasure
preserves every scheduler result and fault, so a successful schedule supplies
its own successful annotated scan. Current world resources enable complete
initial registry/RAM enumeration without a supplied value table.

Graph capture retains explicit empty initial and final FIFO boundaries and an
empty incoming writer map. Stream offsets and initial store counters remain
arbitrary. This module establishes neither completion of arbitrary schedules,
graph construction, separate legality-checker success nor native/source
correspondence. Nonempty incoming FIFO histories require a separate boundary.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace

/-- Lift any actual successful schedule to its exact annotated result.
No world invariant, source classifier or scanner success is supplied. The
offset and incoming publication map are unrestricted execution annotations. -/
theorem scan_of_schedule {initial : State} {actions : List Action}
    {profile : Profile} {result : State × List Observation}
    (success : schedule initial actions profile = .ok result)
    (offset : Nat) (incoming : PublishedHistory.Writers) :
    ∃ run, scan initial actions profile offset incoming = .ok run ∧
      run.execution = result := by
  cases scanned : scan initial actions profile offset incoming with
  | error fault =>
      have failed := (scan_error_iff initial actions profile offset incoming fault).mp scanned
      rw [success] at failed
      cases failed
  | ok run =>
      exact ⟨run, rfl, Except.ok.inj ((scan_scheduled scanned).symm.trans success)⟩

namespace Graph

/-- Initial resource validity and actual closed queue endpoints construct raw
initialized capture. Every live registered initial cell is enumerated with its
actual RAM word; the caller supplies no initializer subset or graph metadata. -/
theorem captured_of_schedule {initial : State} {actions : List Action}
    {profile : Profile} {result : State × List Observation}
    (valid : WellFormed initial profile) (initialEmpty : Quiescent initial)
    (success : schedule initial actions profile = .ok result)
    (finalEmpty : Quiescent result.1) (offset : Nat) :
    ∃ (run : Result) (initials : List Initials.Entry),
      run.execution = result ∧ Captured initial actions profile offset run initials := by
  obtain ⟨run, scanned, execution⟩ := scan_of_schedule success offset PublishedHistory.empty
  obtain ⟨initials, enumerated⟩ := Initials.enumerate_success valid.1
  have finalQueues : Quiescent run.state := by
    have stateEq : run.state = result.1 := congrArg Prod.fst execution
    rw [stateEq]
    exact finalEmpty
  exact ⟨run, initials, execution, valid, initialEmpty, scanned, finalQueues, enumerated⟩

end Graph
end EDSL.OS.TSO64.C23Projection.AtomicTrace

#audit_edsl
