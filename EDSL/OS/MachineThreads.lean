/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Threads.Core
import EDSL.X86.Machine

namespace EDSL.OS.MachineThreads
open X86

/-- A function-call observation stops this worker at its actual RET. No mutex
phase, guard, loan, expected opcode, or protocol check enters this state. -/
structure Worker where
  context : Threads.Context
  returned : Bool

structure State where
  memory : X86.Memory
  workers : List Worker

inductive Fault where
  | machine (error : X86.Error)
  | missingThread | alreadyReturned | syscallBoundary
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

def contextState (context : Threads.Context) (memory : X86.Memory) : X86.State :=
  ⟨context.registers, context.rip, context.flags, memory⟩

def install (state : State) (identifier : Nat) (output : X86.State) (returned : Bool) : State :=
  ⟨output.memory, state.workers.set identifier ⟨Threads.Context.ofState output, returned⟩⟩

/-- One architectural instruction on current shared memory. Every byte,
permission, flag and register effect comes directly from X86.step. The only
scheduler gates select an existing call that has not already returned. -/
def dispatch (state : State) (identifier : Nat) : Except Fault (State × Option AtomicEvent) := do
  let some worker := state.workers[identifier]? | throw .missingThread
  if worker.returned then throw .alreadyReturned
  match ← (X86.step (contextState worker.context state.memory)).mapError Fault.machine with
  | .next output => return (install state identifier output false, none)
  | .atomic event output => return (install state identifier output false, some event)
  | .returned output => return (install state identifier output true, none)
  | .syscall _ => throw .syscallBoundary

def recordEvent (identifier : Nat) (event : Option AtomicEvent) (tail : List (Nat × AtomicEvent)) : List (Nat × AtomicEvent) :=
  match event with | none => tail | some actual => (identifier, actual) :: tail

def schedule (state : State) : List Nat → Except Fault (State × List (Nat × AtomicEvent))
  | [] => .ok (state, [])
  | identifier :: rest => do
    let first ← dispatch state identifier
    let tail ← schedule first.1 rest
    return (tail.1, recordEvent identifier first.2 tail.2)

theorem dispatch_live (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (success : dispatch state identifier = .ok result) :
    ∃ worker, state.workers[identifier]? = some worker ∧ worker.returned = false := by
  cases live : state.workers[identifier]? with
  | none => simp [dispatch, live] at success
  | some worker =>
    cases returned : worker.returned with
    | true => simp [dispatch, live, returned] at success
    | false => exact ⟨worker, rfl, returned⟩

theorem schedule_cons_ok (state : State) (identifier : Nat) (rest : List Nat)
    (result : State × List (Nat × AtomicEvent))
    (success : schedule state (identifier :: rest) = .ok result) :
    ∃ first tail, dispatch state identifier = .ok first ∧ schedule first.1 rest = .ok tail ∧
      result = (tail.1, recordEvent identifier first.2 tail.2) := by
  cases head : dispatch state identifier with
  | error fault => simp [schedule, head] at success
  | ok first =>
    cases next : schedule first.1 rest with
    | error fault => simp [schedule, head, next] at success
    | ok tail =>
      simp [schedule, head, next] at success
      exact ⟨first, tail, rfl, next, success.symm⟩

/-- Finite architectural traces retain the exact chosen worker and RMW event.
They contain no resource/protocol premise beyond the instruction-only dispatch. -/
inductive Trace : State → List Nat → List (Nat × AtomicEvent) → State → Prop where
  | nil {state} : Trace state [] [] state
  | cons {before middle after identifier event selections events}
      (step : dispatch before identifier = .ok (middle, event))
      (tail : Trace middle selections events after) :
      Trace before (identifier :: selections) (recordEvent identifier event events) after

theorem schedule_trace (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (success : schedule state selections = .ok result) : Trace state selections result.2 result.1 := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact .nil
  | cons identifier rest induction =>
    obtain ⟨first, tail, head, next, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact .cons head (induction first.1 tail next)

theorem Trace.schedule {before after : State} {selections : List Nat} {events : List (Nat × AtomicEvent)}
    (trace : Trace before selections events after) : schedule before selections = .ok (after, events) := by
  induction trace with
  | nil => rfl
  | cons step _ induction => simp [MachineThreads.schedule, step, induction]

def Finished (state : State) : Prop := ∀ worker ∈ state.workers, worker.returned = true

end EDSL.OS.MachineThreads
