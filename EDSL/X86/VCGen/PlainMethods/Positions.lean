/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Batch

/-!
Exact own-issue counts at independently recognized accesses and observed RETs
of the original admitted invocation. Positions are indices in the actual full
schedule, including every peer issue and FIFO drain. The current cutpoint is
recovered from that run; no intermediate point, reply or history is supplied.

These results retain the method model's environmental contracts and admit
arbitrary padding, resources, values and initial queues. They do not establish
publication, a read source, or a graph edge.
-/

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen.PlainMethods
open OS OS.TSO64 AtomicMethods

private theorem padding_no_access (padding : Padding) : ¬ IsAccess padding.instruction := by
  cases padding <;> simp [AtomicMethods.Padding.instruction, IsAccess]

private theorem padding_no_ret (padding : Padding) : padding.instruction ≠ .legacy .ret := by
  cases padding <;> simp [AtomicMethods.Padding.instruction]

private theorem operation_no_ret (operation : Operation) :
    operation.instruction ≠ .legacy .ret := by
  cases operation <;> simp [Operation.instruction]

/-- Successful own data dispatch can occur only at the access body. In
particular decoding alone cannot admit an issue from a returned worker. -/
private theorem access_remaining {method : Method} {tid : Nat}
    {state : OS.TSO64.State} {worker : Worker} {point : Point method.operation}
    {action : Action} {result : OS.TSO64.State × Observation}
    (current : Current method state) (live : state.workers[tid]? = some worker)
    (located : At method point worker)
    (actual : OS.TSO64.step state action .sharedCell = .ok result)
    (own : OwnAccess tid state action) : point.remaining = 2 := by
  obtain ⟨_af, issuing, instruction, _issuingAction, issuingLive, fetched, access⟩ := own
  have same : issuing = worker := Option.some.inj (issuingLive.symm.trans live)
  subst issuing
  subst action
  cases point with
  | preamble _offset _padding =>
    obtain ⟨_, pc, _, shape⟩ := located.location
    cases shape with
    | body => rfl
    | @pad _offset padding _rest node _tail =>
      have decoded := (current.decode_node live located.resources node pc).1
      have sameInstruction : padding.instruction = instruction :=
        OS.TSO64.Decoded.ordinary.inj (Except.ok.inj (decoded.symm.trans fetched))
      rw [← sameInstruction] at access
      exact False.elim (padding_no_access padding access)
  | ret _offset _reply =>
    have decoded := (current.decode_node live located.resources
      located.location.2.2.2.1 located.location.2.1).1
    have sameInstruction : (Sequential.Instruction.legacy .ret) = instruction :=
      OS.TSO64.Decoded.ordinary.inj (Except.ok.inj (decoded.symm.trans fetched))
    rw [← sameInstruction] at access
    exact False.elim access
  | done _reply =>
    have returned := located.location.1
    simp [OS.TSO64.step, issue, live, returned] at actual

/-- A real response supplies the issuing worker and production RET decode.
The checked shape excludes both padding and the MOV64 body at that cut. -/
private theorem return_remaining {method : Method} {tid : Nat}
    {state after : OS.TSO64.State} {worker : Worker} {point : Point method.operation}
    {action : Action} (current : Current method state)
    (live : state.workers[tid]? = some worker) (located : At method point worker)
    (actual : OS.TSO64.step state action .sharedCell = .ok (after, .returned tid)) :
    point.remaining = 1 := by
  obtain ⟨_, _, origin⟩ := Return.returned_origin current.valid actual
  obtain ⟨_, issuing, _, _, _, issuingLive, running, _, _, _, _, _, fetched, _⟩ := origin
  have same : issuing = worker := Option.some.inj (issuingLive.symm.trans live)
  subst issuing
  cases point with
  | preamble _offset _padding =>
    obtain ⟨_, pc, _, shape⟩ := located.location
    cases shape with
    | @body _offset node _ret _extent =>
      have decoded := (current.decode_node live located.resources node pc).1
      have sameInstruction : method.operation.instruction = .legacy .ret :=
        OS.TSO64.Decoded.ordinary.inj (Except.ok.inj (decoded.symm.trans fetched))
      exact False.elim (operation_no_ret method.operation sameInstruction)
    | @pad _offset padding _rest node _tail =>
      have decoded := (current.decode_node live located.resources node pc).1
      have sameInstruction : padding.instruction = .legacy .ret :=
        OS.TSO64.Decoded.ordinary.inj (Except.ok.inj (decoded.symm.trans fetched))
      exact False.elim (padding_no_ret padding sameInstruction)
  | ret _offset _reply => rfl
  | done _reply => exact False.elim (running located.location.1)

/-- At any actual own MOV64 dispatch in the successful full schedule, exactly
the original invocation's padding instructions have issued for this worker. -/
theorem Invocation.dispatched_ownIssues {state : OS.TSO64.State} {tid : Nat}
    (invocation : Invocation state tid) {actions : List Action}
    {result : OS.TSO64.State × List Observation} {index : Nat}
    (success : schedule state actions .sharedCell = .ok result)
    (dispatched : DispatchedAt tid state actions result index) :
    AtomicMethods.ownIssues tid (actions.take index) = invocation.padding.length := by
  obtain ⟨dispatchBefore, _action, _first, dispatchPrefix, _, actual, own⟩ := dispatched
  obtain ⟨before, prefixRun, _⟩ := ScheduleTrace.cut success index
  have same : dispatchBefore = before :=
    congrArg Prod.fst (Except.ok.inj (dispatchPrefix.symm.trans prefixRun))
  subst dispatchBefore
  obtain ⟨current, point, _, _, live, located, progress, _, _⟩ :=
    schedule_preserves invocation.current invocation.live invocation.entry prefixRun
  have remaining := access_remaining current live located actual own
  change point.remaining + AtomicMethods.ownIssues tid (actions.take index) =
    invocation.padding.length + 2 at progress
  omega

/-- At an actually observed RET in the successful full schedule, exactly the
original padding and the single MOV64 have issued before that action index. -/
theorem Invocation.returned_ownIssues {state : OS.TSO64.State} {tid : Nat}
    (invocation : Invocation state tid) {actions : List Action}
    {result : OS.TSO64.State × List Observation} {index : Nat}
    (success : schedule state actions .sharedCell = .ok result)
    (observed : result.2[index]? = some (.returned tid)) :
    AtomicMethods.ownIssues tid (actions.take index) = invocation.padding.length + 1 := by
  obtain ⟨_before, _action, _next, prefixRun, _, actual⟩ :=
    ScheduleTrace.observation_at success observed
  obtain ⟨current, point, _, _, live, located, progress, _, _⟩ :=
    schedule_preserves invocation.current invocation.live invocation.entry prefixRun
  have remaining := return_remaining current live located actual
  change point.remaining + AtomicMethods.ownIssues tid (actions.take index) =
    invocation.padding.length + 2 at progress
  omega

/-- Crossing a selected own issue strictly increases the own-issue count.
The later index may be an arbitrary prefix cut, including the list's end. -/
theorem own_issue_count_lt_of_lt {actions : List Action} {tid first last : Nat} {af : Bool}
    (selected : actions[first]? = some (.issue tid af)) (earlier : first < last) :
    AtomicMethods.ownIssues tid (actions.take first) <
      AtomicMethods.ownIssues tid (actions.take last) := by
  induction actions generalizing first last with
  | nil => simp at selected
  | cons action rest ih =>
    cases first with
    | zero =>
      have same : action = .issue tid af := by
        simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
      subst action
      cases last with
      | zero => omega
      | succ last =>
        simp only [List.take_zero, List.take_succ_cons, AtomicMethods.ownIssues,
          AtomicMethods.ownIssue, ite_true]
        omega
    | succ first =>
      cases last with
      | zero => omega
      | succ last =>
        have tailSelected : rest[first]? = some (.issue tid af) := by
          simpa only [List.getElem?_cons_succ] using selected
        have tailEarlier : first < last := by omega
        have strict := ih tailSelected tailEarlier
        simpa only [List.take_succ_cons, AtomicMethods.ownIssues] using
          Nat.add_lt_add_left strict (AtomicMethods.ownIssue tid action)

/-- Two own issues with the same preceding own-issue count have the same
original action index. AF choices and all intervening peer/drain actions are
arbitrary. This identifies positions without equating completed-call records. -/
theorem own_issue_index_unique {actions : List Action} {tid first last : Nat}
    {firstAF lastAF : Bool}
    (atFirst : actions[first]? = some (.issue tid firstAF))
    (atLast : actions[last]? = some (.issue tid lastAF))
    (same : AtomicMethods.ownIssues tid (actions.take first) =
      AtomicMethods.ownIssues tid (actions.take last)) : first = last := by
  rcases Nat.lt_trichotomy first last with earlier | equal | later
  · have strict := own_issue_count_lt_of_lt atFirst earlier
    omega
  · exact equal
  · have strict := own_issue_count_lt_of_lt atLast later
    omega

end EDSL.X86.VCGen.PlainMethods

#audit_edsl
