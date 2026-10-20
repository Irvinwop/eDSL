/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO.Effects
import EDSL.OS.TSO.Trace
import EDSL.Audit

namespace EDSL.OS.TSO.Counter
open X86

/-- Independent sequential fetch-add interface: the argument and the returned
old value. Addition is modulo 2^32, rather than unbounded integer addition. -/
structure Operation where
  thread : Nat
  delta : BitVec 32
  result : BitVec 32
  deriving DecidableEq, Repr

/-- The sequential specification does not execute machine code. -/
inductive Sequential : BitVec 32 → List Operation → BitVec 32 → Prop where
  | nil (value) : Sequential value [] value
  | cons {before middle after operation operations}
      (returned : operation.result = before)
      (updated : middle = before + operation.delta)
      (tail : Sequential middle operations after) :
      Sequential before (operation :: operations) after

def totalDelta : List Operation → BitVec 32
  | [] => 0
  | operation :: operations => operation.delta + totalDelta operations

theorem Sequential.total {before after : BitVec 32} {operations : List Operation}
    (history : Sequential before operations after) : after = before + totalDelta operations := by
  induction history with
  | nil value => simp [totalDelta]
  | cons returned updated tail ih =>
    rw [ih, updated]
    exact BitVec.add_assoc _ _ _

theorem totalDelta_units {operations : List Operation}
    (ones : ∀ operation ∈ operations, operation.delta = 1) :
    totalDelta operations = BitVec.ofNat 32 operations.length := by
  induction operations with
  | nil => rfl
  | cons operation operations ih =>
    have head := ones operation List.mem_cons_self
    have tail := ih (fun operation member => ones operation (List.mem_cons_of_mem _ member))
    simp only [totalDelta, head, tail, List.length_cons]
    rw [BitVec.ofNat_add]
    exact BitVec.add_comm _ _

/-- The no-lost-update count follows from the independent sequential contract;
it is valid across modular wraparound and has no termination premise. -/
theorem Sequential.unit_updates {before after : BitVec 32} {operations : List Operation}
    (history : Sequential before operations after)
    (ones : ∀ operation ∈ operations, operation.delta = 1) :
    after = before + BitVec.ofNat 32 operations.length := by
  rw [history.total, totalDelta_units ones]

def Operation.event (address : Word) (operation : Operation) : Nat × AtomicEvent :=
  (operation.thread, ⟨address, operation.result, operation.result + operation.delta⟩)

/-- Only actual retired atomic observations on this exact four-byte cell. -/
def eventsAt (address : Word) (observations : List Observation) : List (Nat × AtomicEvent) :=
  observations.filterMap fun observation => match observation with
    | .retired identifier (some event) =>
      if event.address = address then some (identifier, event) else none
    | _ => none

/-- An operation's input is captured from the issuing context, not reconstructed
by subtracting event values. Fetch, empty local FIFO, architectural execution,
installed context and observed event all come from the successful scheduler. -/
def Origin (address : Word) (before : State) (action : Action)
    (result : State × Observation) (operation : Operation) : Prop :=
  ∃ worker event output,
    action = .issue operation.thread ∧
    before.workers[operation.thread]? = some worker ∧ worker.returned = false ∧
    decodeAt (sharedState before worker) = .ok .fetchAddEaxRdi ∧ worker.buffer = [] ∧
    executeInstruction (sharedState before worker) .fetchAddEaxRdi = .ok (.atomic event output) ∧
    result.1 = install before operation.thread output.memory (.ofState output) false [] ∧
    result.2 = .retired operation.thread (some event) ∧ event.address = address ∧
    operation.delta = (worker.context.registers .rax).setWidth 32 ∧
    operation.result = event.before

/-- The independent sequential interface agrees with current RAM, the actual
old-value register result and the exact scheduler observation. -/
theorem Origin.effects {address : Word} {before : State} {action : Action}
    {result : State × Observation} {operation : Operation}
    (origin : Origin address before action result operation) :
    loadDWord before.memory address = .ok operation.result ∧
    loadDWord result.1.memory address = .ok (operation.result + operation.delta) ∧
    result.2 = .retired operation.thread (some (operation.event address).2) ∧
    ∃ worker, result.1.workers[operation.thread]? = some worker ∧
      worker.context.registers .rax = operation.result.setWidth 64 := by
  obtain ⟨worker, event, output, actionEq, live, returned, decoded, empty, executed,
    installed, observed, addressEq, deltaEq, resultEq⟩ := origin
  have sound := executeInstruction_fetchAdd_sound executed
  have update : event.after = operation.result + operation.delta := by
    rw [resultEq, deltaEq]
    exact sound.2.2.1
  have eventEq : event = (operation.event address).2 := by
    cases event
    simp only [Operation.event] at *
    cases addressEq
    cases resultEq
    cases update
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [resultEq, ← addressEq]
    exact sound.1.2.2.1
  · rw [installed, ← update, ← addressEq]
    exact sound.1.readback
  · exact observed.trans (congrArg (fun e => Observation.retired operation.thread (some e)) eventEq)
  · refine ⟨⟨.ofState output, false, []⟩, ?_, ?_⟩
    · rw [installed]
      exact List.getElem?_set_self (List.getElem_of_getElem? live).1
    · change output.registers .rax = _
      rw [resultEq]
      exact sound.2.2.2.1

/-- Rich history in chronological scheduler order. Quiet actions may include
ordinary buffered stores, loads, RET, blocked locked issues, disjoint RMWs and
disjoint FIFO publication. Every addition is an actual decoded LOCK XADD. -/
inductive MachineHistory (address : Word) :
    State → List Action → List Observation → State → List Operation → Prop where
  | nil {state} : MachineHistory address state [] [] state []
  | quiet {before middle after action observation actions observations operations}
      (step : TSO.step before action = .ok (middle, observation))
      (unchanged : loadDWord middle.memory address = loadDWord before.memory address)
      (unobserved : eventsAt address [observation] = [])
      (tail : MachineHistory address middle actions observations after operations) :
      MachineHistory address before (action :: actions) (observation :: observations) after operations
  | addition {before middle after action observation actions observations operation operations}
      (step : TSO.step before action = .ok (middle, observation))
      (origin : Origin address before action (middle, observation) operation)
      (tail : MachineHistory address middle actions observations after operations) :
      MachineHistory address before (action :: actions) (observation :: observations) after
        (operation :: operations)

theorem MachineHistory.trace {address : Word} {before after : State} {actions : List Action}
    {observations : List Observation} {operations : List Operation}
    (history : MachineHistory address before actions observations after operations) :
    TSO.Trace before actions observations after := by
  induction history with
  | nil => exact .nil
  | quiet step _ _ _ ih | addition step _ _ ih => exact .cons step ih

theorem MachineHistory.events {address : Word} {before after : State} {actions : List Action}
    {observations : List Observation} {operations : List Operation}
    (history : MachineHistory address before actions observations after operations) :
    operations.map (Operation.event address) = eventsAt address observations := by
  induction history with
  | nil => rfl
  | @quiet before middle after action observation actions observations operations
      step unchanged unobserved tail ih =>
    have head : (match observation with
        | .retired identifier (some event) =>
          if event.address = address then some (identifier, event) else none
        | _ => none) = none := by
      simpa [eventsAt] using unobserved
    simp [eventsAt, head] at ih ⊢
    exact ih
  | @addition before middle after action observation actions observations operation operations
      step origin tail ih =>
    have observed := origin.effects.2.2.1
    dsimp only at observed
    rw [observed]
    simpa [eventsAt, Operation.event] using congrArg (operation.event address :: ·) ih

/-- Issue selections in actual schedule order, including instructions that do
not access the counter. -/
def issuedThreads (actions : List Action) : List Nat :=
  actions.filterMap fun action => match action with
    | .issue identifier => some identifier
    | .drain _ => none

/-- Every linearized operation embeds in the actual instruction-issue order.
This also rules out inserting or permuting operations with the same arithmetic
result: the rich origin is tied to that concrete issue and current context. -/
theorem MachineHistory.issued_sublist {address : Word} {before after : State}
    {actions : List Action} {observations : List Observation} {operations : List Operation}
    (history : MachineHistory address before actions observations after operations) :
    (operations.map Operation.thread).Sublist (issuedThreads actions) := by
  induction history with
  | nil => exact .slnil
  | @quiet before middle after action observation actions observations operations
      step unchanged unobserved tail ih =>
    cases action with
    | issue identifier => exact .cons identifier ih
    | drain identifier => exact ih
  | @addition before middle after action observation actions observations operation operations
      step origin tail ih =>
    obtain ⟨worker, event, output, actionEq, rest⟩ := origin
    rw [actionEq]
    exact .cons_cons operation.thread ih

/-- Filtering the exact chronological observation sequence preserves each
thread's operation order. No permutation or commutativity premise is used. -/
theorem MachineHistory.thread_order {address : Word} {before after : State} {actions : List Action}
    {observations : List Observation} {operations : List Operation}
    (history : MachineHistory address before actions observations after operations) (identifier : Nat) :
    (operations.map (Operation.event address)).filter (fun entry => entry.1 == identifier) =
      (eventsAt address observations).filter (fun entry => entry.1 == identifier) := by
  rw [history.events]

end EDSL.OS.TSO.Counter

#audit_edsl
