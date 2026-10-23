/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.StructuralCFG
import EDSL.X86.Sequential.CFGChoices

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Control laws for actual successful production execution of structurally
authenticated CFG nodes, without a read-only instruction policy. Ordinary and
atomic continuations follow static ISA targets; syscall and returned results are
boundaries and do not continue inside the graph. Unsupported instructions and
execution errors cannot satisfy the success premises.

These laws establish only the destination edge and RIP. Stores may change code
when the consumer lacks a proper effect/resource frame. Preserving executable
text and interpreting actual atomic events remain separate mandatory future
obligations. No post-state memory equality or code binding, OS authority,
scheduler, termination, linearizability, or public coverage result is provided.
No source effect semantics are changed here.
-/

namespace EDSL.X86.Sequential.CFG.Structural

/-- Results that carry a successor state within sequential execution. Atomic
events are retained in the actual observation; this predicate does not interpret
them. A syscall request or returned state is a boundary, not a continuation. -/
def Continues (observation : Sequential.Observation) (after : State) : Prop :=
  observation.result = .next after ∨ ∃ event, observation.result = .atomic event after

private theorem next_continuation_state {state after : State} {reads : List Read}
    (continued : Continues ⟨.next state, reads⟩ after) : after = state := by
  rcases continued with next | ⟨_, atomic⟩
  · exact (StepResult.next.inj next).symm
  · cases atomic

private theorem atomic_continuation_state {state after : State} {event : AtomicEvent}
    {reads : List Read} (continued : Continues ⟨.atomic event state, reads⟩ after) :
    after = state := by
  rcases continued with next | ⟨_, atomic⟩
  · cases next
  · exact (StepResult.atomic.inj atomic).2.symm

/-- A successful continuing Bool execution follows a static ISA successor,
including ordinary stores and the actual legacy XCHG/XADD atomic results. The
read-only ordinary cases reuse `CFG.execute_next_target`; no memory frame is
assumed or concluded. Failed execution supplies no continuation premise. -/
theorem execute_continuation_target {initial after : State} {instruction : Instruction}
    {af : Bool} {observation : Observation}
    (actual : execute initial instruction af = .ok observation)
    (continued : Continues observation after) :
    after.rip ∈ CFG.Targets initial.rip instruction := by
  by_cases allowed : CFG.readOnly instruction = true
  · rcases continued with next | ⟨_, atomic⟩
    · exact CFG.execute_next_target allowed actual next
    · obtain ⟨_, next | ⟨returned, _⟩⟩ := CFG.execute_result allowed actual
      · rw [atomic] at next
        cases next
      · rw [atomic] at returned
        cases returned
  · cases instruction <;> try exact False.elim (allowed rfl)
    case legacy old =>
      cases old <;> try exact False.elim (allowed rfl)
      case storeEsiRdi =>
        obtain ⟨memory, _, rfl⟩ :=
          (execute_storeIntent_success_iff (instruction := .legacy .storeEsiRdi) rfl).mp actual
        rw [next_continuation_state continued]
        simp [CFG.Targets]
      case storeEaxRsi =>
        obtain ⟨memory, _, rfl⟩ :=
          (execute_storeIntent_success_iff (instruction := .legacy .storeEaxRsi) rfl).mp actual
        rw [next_continuation_state continued]
        simp [CFG.Targets]
      case exchangeEaxRdi =>
        cases exchanged : executeExchange initial with
        | error fault => simp [execute, X86.executeInstruction, exchanged] at actual
        | ok output =>
          simp [execute, X86.executeInstruction, exchanged] at actual
          cases actual
          rw [atomic_continuation_state continued]
          simpa only [CFG.Targets, Instruction.length, List.mem_singleton,
            BitVec.ofNat_eq_ofNat] using
            (executeExchange_sound exchanged).2.2.2.2.2
      case fetchAddEaxRdi =>
        cases added : executeFetchAdd initial with
        | error fault => simp [execute, X86.executeInstruction, added] at actual
        | ok output =>
          simp [execute, X86.executeInstruction, added] at actual
          cases actual
          rw [atomic_continuation_state continued]
          simpa only [CFG.Targets, Instruction.length, List.mem_singleton,
            BitVec.ofNat_eq_ofNat] using
            (executeFetchAdd_sound added).2.2.2.2.2
      case syscall =>
        cases actual
        rcases continued with next | ⟨_, atomic⟩
        · cases next
        · cases atomic
    case storeMem32 address source =>
      obtain ⟨memory, _, rfl⟩ :=
        (execute_storeIntent_success_iff (instruction := .storeMem32 address source) rfl).mp actual
      rw [next_continuation_state continued]
      simp [CFG.Targets]
    case storeMem64 address source =>
      obtain ⟨memory, _, rfl⟩ :=
        (execute_storeIntent64_success_iff (instruction := .storeMem64 address source) rfl).mp actual
      rw [next_continuation_state continued]
      simp [CFG.Targets]

/-- Derive a fallthrough target for any effect returned by the current production
registration. The registered families supply their existing RIP laws here;
`RegisterChoiceEffect` and the production registration interface are unchanged.
Adding a registered family requires discharging this control law as well. -/
theorem registerChoiceEffect_fallthrough {instruction : Instruction}
    {effect : RegisterChoiceEffect instruction}
    (registered : instruction.registerChoiceEffect = some effect)
    (initial : State) (choices : FlagChoices) :
    (effect.apply initial choices).rip ∈ CFG.Targets initial.rip instruction := by
  cases instruction <;>
    simp only [Instruction.registerChoiceEffect, Option.some.injEq, reduceCtorEq] at registered
  case imulReg64 destination source =>
    cases registered
    simpa only [CFG.Targets, Instruction.length, List.mem_singleton,
      BitVec.ofNat_eq_ofNat] using
      imulReg64State_rip initial destination source choices
  case shiftRightImm32 operation destination immediate prefixed =>
    cases registered
    simpa only [CFG.Targets, Instruction.length, List.mem_singleton] using
      shiftRightImm32State_rip initial operation destination immediate prefixed choices

/-- A successful continuing vector execution follows a static ISA successor.
Unregistered instructions reuse the Bool control law with the production choice
projection; registered effects use their shared registration fallthrough law.
This imposes no read-only policy and interprets no atomic event. -/
theorem executeWith_continuation_target {initial after : State} {instruction : Instruction}
    {choices : FlagChoices} {observation : Observation}
    (actual : executeWith initial instruction choices = .ok observation)
    (continued : Continues observation after) :
    after.rip ∈ CFG.Targets initial.rip instruction := by
  cases registered : instruction.registerChoiceEffect with
  | none =>
    have executed : execute initial instruction (instruction.selectedChoice initial choices) =
        .ok observation := by
      simpa only [executeWith, registered] using actual
    exact execute_continuation_target executed continued
  | some effect =>
    simp only [executeWith, registered, Except.ok.injEq] at actual
    cases actual
    rw [next_continuation_state continued]
    exact registerChoiceEffect_fallthrough registered initial choices

variable {profile : Profile}

/-- Authenticate the current node in executable RAM and transport its actual
continuing vector step to a certified graph edge and destination RIP. `CodeAt`
is required only for the initial memory. A consumer must separately preserve
executable text across effects and interpret actual atomic events before using
this control law as part of any further effectful verification. -/
theorem Valid.continues {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph profile)
    {base : Word} {initial after : State} (code : CodeAt initial.memory base bytes)
    (index : graph.Index)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node index).offset)
    {choices : FlagChoices} {observation : Observation}
    (actual : stepWith choices initial = .ok observation)
    (continued : Continues observation after) :
    ∃ destination : graph.Index, graph.Edge index destination ∧
      after.rip = base + BitVec.ofNat 64 (graph.node destination).offset := by
  have decoded := valid.decoded code index initial rfl pc
  have executed : executeWith initial (graph.node index).instruction choices = .ok observation := by
    rwa [stepWith_eq_executeWith choices decoded] at actual
  have target := executeWith_continuation_target executed continued
  rw [pc, CFG.targets_translate] at target
  obtain ⟨offset, member, address⟩ := List.mem_map.mp target
  obtain ⟨destination, same⟩ := valid.closed index offset member
  refine ⟨destination, ?_, ?_⟩
  · change BitVec.ofNat 64 (graph.node destination).offset ∈ (graph.node index).successors
    rw [same]
    exact member
  · exact address.symm.trans (congrArg (fun value => base + value) same.symm)

#print axioms Continues
#print axioms execute_continuation_target
#print axioms registerChoiceEffect_fallthrough
#print axioms executeWith_continuation_target
#print axioms Valid.continues

end EDSL.X86.Sequential.CFG.Structural

#audit_edsl
