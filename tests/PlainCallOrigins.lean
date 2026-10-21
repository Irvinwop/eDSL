/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.PlainMethodAdmission
import EDSL.X86.VCGen.PlainMethods.Calls
import EDSL.X86.VCGen.PlainMethods.AtomicEvents

set_option autoImplicit false

namespace EDSL.Tests.PlainCallOrigins
open X86 OS.TSO64 X86.VCGen.PlainMethods
open OS.TSO64.C23Projection

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

def actions : List Action := [.issue 0 true, .issue 0 false]

def execute (kind : PlainMethodAdmission.Kind) := schedule (PlainMethodAdmission.initial kind) actions .sharedCell

theorem execute_succeeds (kind : PlainMethodAdmission.Kind) : (execute kind).toOption.isSome = true := by
  cases kind <;> decide +kernel

def run (kind : PlainMethodAdmission.Kind) : OS.TSO64.State × List Observation :=
  checked (execute kind) (execute_succeeds kind)

theorem actual (kind : PlainMethodAdmission.Kind) :
    schedule (PlainMethodAdmission.initial kind) actions .sharedCell = .ok (run kind) :=
  checked_ok (execute kind) (execute_succeeds kind)

theorem final_exists (kind : PlainMethodAdmission.Kind) : ((run kind).1.workers[0]?).isSome = true := by
  cases kind <;> decide +kernel

def final (kind : PlainMethodAdmission.Kind) : Worker := ((run kind).1.workers[0]?).get (final_exists kind)

private theorem option_get {α : Type} (value : Option α) (present : value.isSome = true) :
    value = some (value.get present) := by
  cases value with
  | none => cases present
  | some value => rfl

theorem final_live (kind : PlainMethodAdmission.Kind) : (run kind).1.workers[0]? = some (final kind) :=
  option_get _ (final_exists kind)

theorem final_returned (kind : PlainMethodAdmission.Kind) : (final kind).phase = .returned := by
  cases kind <;> decide +kernel

/-- The adapter consumes present resource admission and an actual production
run, rather than a desired response or a supplied completed-call assertion. -/
theorem extracted (kind : PlainMethodAdmission.Kind) :
    Nonempty (CompletedCall (PlainMethodAdmission.method kind) 0 (PlainMethodAdmission.initial kind) actions (run kind)) :=
  completed_call (PlainMethodAdmission.present kind) (PlainMethodAdmission.live kind) (PlainMethodAdmission.entry kind)
    (actual kind) (final_live kind) (final_returned kind)

/-- Original action indices are observed, not supplied to the extraction API.
This catches an adapter that moves the response to the access position or
compresses the two distinct retiring instructions into one history position. -/
theorem extracted_positions (kind : PlainMethodAdmission.Kind)
    (completed : CompletedCall (PlainMethodAdmission.method kind) 0 (PlainMethodAdmission.initial kind) actions (run kind)) :
    completed.performed = 0 ∧ completed.returned = 1 := by
  obtain ⟨before, action, next, prefixRun, selected, observed, rest⟩ := completed.response
  have bound : completed.returned < (run kind).2.length := (List.getElem_of_getElem? observed).1
  have length := OS.TSO64.ScheduleTrace.length (actual kind)
  have beforeReturn := completed.beforeReturn
  change (run kind).2.length = 2 at length
  omega

theorem initial_sequenced (kind : PlainMethodAdmission.Kind) : Sequenced (PlainMethodAdmission.initial kind) := by
  intro worker member
  change worker ∈ [PlainMethodAdmission.worker kind] at member
  have same := List.mem_singleton.mp member
  subst worker
  exact makeWorker_sequenced (PlainMethodAdmission.made kind)

def scan (kind : PlainMethodAdmission.Kind) :=
  AtomicTrace.scan (PlainMethodAdmission.initial kind) actions .sharedCell 0 PublishedHistory.empty

theorem scan_succeeds (kind : PlainMethodAdmission.Kind) : (scan kind).toOption.isSome = true := by
  cases kind <;> decide +kernel

def scanned (kind : PlainMethodAdmission.Kind) : AtomicTrace.Result :=
  checked (scan kind) (scan_succeeds kind)

theorem scan_actual (kind : PlainMethodAdmission.Kind) :
    AtomicTrace.scan (PlainMethodAdmission.initial kind) actions .sharedCell 0 PublishedHistory.empty =
      .ok (scanned kind) := checked_ok (scan kind) (scan_succeeds kind)

def expectedEvents : PlainMethodAdmission.Kind → List AtomicTrace.Event
  | .load => [⟨0, 0, .load PlainMethodAdmission.reference 0x1122334455667788 (.initial ⟨0⟩)⟩]
  | .store => [⟨0, 0, .store PlainMethodAdmission.reference 0xfedcba9876543210 0⟩]

/-- Independent literal event expectations distinguish initialized RF identity,
full-width operands, managed occurrence zero, thread and original action index.
RET must not appear as another managed data access. -/
theorem scanner_events (kind : PlainMethodAdmission.Kind) :
    (scan kind).toOption.map AtomicTrace.Result.events = some (expectedEvents kind) := by
  cases kind <;> decide +kernel

/-- Real RET responses differ between the load and store machine interfaces;
the store's logical unit reply must not replace the original machine RAX=5. -/
structure RuntimeView where
  response : Option (Nat × Word)
  kinds : List (Nat × Nat)
  retired : List Nat
  words : List (Option Word)
  deriving DecidableEq

theorem runtime_responses (kind : PlainMethodAdmission.Kind) :
    (execute kind).toOption.map (fun result =>
      ({ response := (result.2[1]?).bind fun observation => Return.returnValue (result.1, observation)
         kinds := result.2.map PlainMethods.eventKind
         retired := result.2.map Observation.retired
         words := [65536, 65544, 262144].map fun address =>
           (loadQWord (published result.1.world) address).toOption } : RuntimeView)) =
    some ⟨some (0, match kind with | .load => 0x1122334455667788 | .store => 5),
      [(0, 0), (1, 0)], [1, 1],
      [some 0x1122334455667788, some 0xabcdef0123456789, some 0x7000]⟩ := by
  cases kind <;> decide +kernel

private theorem scanner_bridge {method : Method} {tid : Nat} {state : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation} {scanned : AtomicTrace.Result}
    (completed : CompletedCall method tid state actions result)
    (valid : WellFormed state .sharedCell) (sequenced : Sequenced state)
    (scheduled : schedule state actions .sharedCell = .ok result)
    (scannedRun : AtomicTrace.scan state actions .sharedCell 0 PublishedHistory.empty = .ok scanned) :
    ∃ source, AtomicEvents.event method tid completed.performed completed.reply source ∈ scanned.events ∧
      (AtomicEvents.event method tid completed.performed completed.reply source).toSource
        AtomicEvents.orders = (completed.call 0).event := by
  have execution : scanned.execution = result :=
    Except.ok.inj ((AtomicTrace.scan_scheduled scannedRun).symm.trans scheduled)
  have access : AccessAt method tid state actions scanned.execution
      completed.performed completed.reply := by
    simpa only [execution] using completed.access
  obtain ⟨source, member⟩ := AtomicEvents.scan_coverage valid sequenced scannedRun access
  refine ⟨source, ?_, ?_⟩
  · simpa only [Nat.zero_add] using member
  · exact AtomicEvents.event_toSource _ _ _ _ _

/-- Call and scanner coverage refer to the very same production execution.
This does not invoke the C23 graph verifier or assume a legal history. -/
theorem same_run_event (kind : PlainMethodAdmission.Kind) :
    ∃ completed : CompletedCall (PlainMethodAdmission.method kind) 0 (PlainMethodAdmission.initial kind) actions (run kind),
      ∃ source,
        AtomicEvents.event (PlainMethodAdmission.method kind) 0 completed.performed completed.reply source ∈
          (scanned kind).events ∧
        (AtomicEvents.event (PlainMethodAdmission.method kind) 0 completed.performed completed.reply source).toSource
          AtomicEvents.orders = (completed.call 0).event := by
  obtain ⟨completed⟩ := extracted kind
  exact ⟨completed, scanner_bridge completed (PlainMethodAdmission.present kind).valid
    (initial_sequenced kind) (actual kind) (scan_actual kind)⟩

end EDSL.Tests.PlainCallOrigins

#print axioms EDSL.X86.VCGen.PlainMethods.completed_call
#print axioms EDSL.X86.VCGen.PlainMethods.AtomicEvents.scan_converse
#print axioms EDSL.Tests.PlainCallOrigins.extracted
#print axioms EDSL.Tests.PlainCallOrigins.same_run_event
#audit_edsl
