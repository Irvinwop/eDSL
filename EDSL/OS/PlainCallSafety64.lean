/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Safety
import EDSL.OS.PlainCallFrames64

/-!
Transport production plain-method progress to independent prefix safety.
The only dynamic input is the actual successful schedule from a current-only
Pre. Static shapes are separate proof-side evidence; current instruction points
and queue progress are obtained from schedule_preserves, never caller oracles.
Exact original/current resources, references, flags, code and protected caller
reads survive every prefix, including arbitrary valid incoming FIFO drains.
-/

set_option autoImplicit false

namespace EDSL.OS.PlainCallSafety64
open X86 TSO64 Grading.ConcurrentTask.Plain64
open X86.VCGen

/-- Retain the independent observational queue fields of the engine frame. -/
theorem queue_frame {expected actual : Queue.Cursor}
    (frame : PlainMethods.QueueFrame expected actual) :
    Grading.ConcurrentTask.Plain64.QueueFrame expected actual :=
  ⟨frame.counter, frame.suffix⟩

/-- The admitted fixed operation's complete queue effect is precisely the
independently selected input's one possible allocation. -/
theorem queue_after {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : PlainCallAdmission64.Admitted input before tid) :
    admitted.invocation.method.queueAfter admitted.invocation.method.initialQueue =
      ⟨admitted.invocation.initial.pending ++ extra input admitted.invocation.method.reference
          admitted.invocation.initial,
        admitted.invocation.initial.nextStore + writes input⟩ := by
  cases input with
  | loadAcquire image target cell occurrence =>
    simp only [PlainMethods.Method.queueAfter, admitted.operation,
      PlainCallAdmission64.fixedOperation, Input.site, admitted.initialQueue, extra, writes,
      List.append_nil, Nat.add_zero]
  | storeRelease image target cell value occurrence =>
    have source : admitted.invocation.method.entry .rsi = value :=
      (congrFun admitted.registers .rsi).trans admitted.entryFacts.arguments.store_rsi
    simp only [PlainMethods.Method.queueAfter, admitted.operation,
      PlainCallAdmission64.fixedOperation, Input.site, admitted.initialQueue, Queue.Cursor.enqueueManaged,
      source, extra, writes]

/-- Every actual current point gives stage-free independent queue progress.
The initial FIFO/counter is the actual admitted worker, not a chosen boundary. -/
theorem queue_progress {input : Input} {before : TSO64.State} {tid : Nat}
    (admitted : PlainCallAdmission64.Admitted input before tid)
    {point : PlainMethods.Point admitted.invocation.method.operation} {current : Worker}
    (located : PlainMethods.At admitted.invocation.method point current) :
    QueueProgress input admitted.invocation.method.reference admitted.invocation.initial current := by
  cases point with
  | preamble offset padding =>
    refine ⟨false, fun _ => rfl, ?_⟩
    have frame := located.queue
    simp only [PlainMethods.Method.queueAt, admitted.initialQueue] at frame
    simpa only [Bool.false_eq_true, ite_false, List.append_nil, Nat.add_zero] using
      queue_frame frame
  | ret offset reply | done reply =>
    have frame := located.queue
    rw [PlainMethods.Method.queueAt, queue_after admitted] at frame
    cases input with
    | loadAcquire image target cell occurrence =>
      refine ⟨false, fun _ => rfl, ?_⟩
      simpa only [extra, writes, Bool.false_eq_true, ite_false, List.append_nil,
        Nat.add_zero] using queue_frame frame
    | storeRelease image target cell value occurrence =>
      refine ⟨true, ?_, ?_⟩
      · intro impossible
        cases impossible
      · simpa only [extra, writes, Bool.true_eq, ite_true] using queue_frame frame

/-- Any current checked point preserves every GPR other than RAX/RSP. This
fact is derived for the actual point rather than assumed in admission. -/
theorem registers_other {method : PlainMethods.Method}
    {point : PlainMethods.Point method.operation} {worker : Worker}
    (located : PlainMethods.At method point worker)
    (register : Register) (notRax : register ≠ .rax) (notRsp : register ≠ .rsp) :
    worker.context.registers register = method.entry register := by
  cases point with
  | preamble offset padding => exact congrFun located.location.2.2.1 register
  | ret offset reply =>
    rw [located.location.2.2.1]
    exact method.operation.registers_other method.entry reply register notRax
  | done reply =>
    rw [located.location.2.2, AtomicMethods.written_other _ .rsp _ register notRsp]
    exact method.operation.registers_other method.entry reply register notRax

/-- Every actual successful prefix has the complete independent safety frame.
No future execution, cutpoint, loaded value, response or history is a premise. -/
theorem safe_prefix {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog)
    {before : TSO64.State} {inputs : Fin before.workers.length → Input}
    (pre : Pre catalog before inputs) {actions : List Action}
    {result : TSO64.State × List Observation}
    (success : schedule before actions .sharedCell = .ok result) :
    SafePrefix before result.1 inputs where
  toPrefixFrame := PlainCallFrames64.prefix_frame static pre success
  frames := by
    intro tid initial initialLive
    let admitted := PlainCallAdmission64.admission static pre tid
    have original : admitted.invocation.initial = initial := admitted.initial_eq initialLive
    obtain ⟨current, point, worker, _emissions, live, located, _progress, _replies, _trace⟩ :=
      PlainMethods.schedule_preserves admitted.invocation.current admitted.invocation.live
        admitted.invocation.entry success
    have resources : worker.resources = initial.resources :=
      (located.resources.trans admitted.resources).trans (congrArg Worker.resources original)
    have valid : WellFormed result.1 .sharedCell := schedule_wellFormed pre.valid success
    refine ⟨worker, admitted.invocation.method.reference, live, resources,
      (valid.2 worker (List.mem_of_getElem? live)).1, admitted.descriptor,
      admitted.target, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [original] using admitted.selected
    · rw [located.resources, ← admitted.address]
      exact current.selected
    · simpa only [original] using queue_progress admitted located
    · exact (located.flags.trans admitted.flags).trans
        (congrArg (fun originalWorker => originalWorker.context.flags) original)
    · intro register member
      have notRax : register ≠ .rax := by
        cases register <;> simp_all [PureCall.calleeSaved]
      have notRsp : register ≠ .rsp := by
        cases register <;> simp_all [PureCall.calleeSaved]
      exact ((registers_other located register notRax notRsp).trans
        (congrFun admitted.registers register)).trans
          (congrArg (fun originalWorker => originalWorker.context.registers register) original)
    · simpa only [admitted.base, admitted.bytes] using current.code
    · intro continuation read
      have oldCaller : Borrowing.loadWord64 before.world.legacy.shared initial.resources.actor
          initial.resources.caller.identifier initial.resources.callerAddress =
            .ok admitted.invocation.method.returnAddress := by
        rw [← original, ← admitted.resources]
        exact admitted.invocation.current.caller
      have same : admitted.invocation.method.returnAddress = continuation :=
        Except.ok.inj (oldCaller.symm.trans read)
      rw [located.resources, ← same]
      exact current.caller

end EDSL.OS.PlainCallSafety64

#audit_edsl
