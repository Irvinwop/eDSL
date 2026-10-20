/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Syscall

namespace EDSL.OS.LinuxExit
open X86

/-- Raw Linux x86-64 exit number, not libc _exit or exit_group. This contract's
process interpretation assumes a single-threaded process without interception. -/
def supported (request : SyscallRequest) : Prop := request.number = 60

def status (request : SyscallRequest) : Byte := (request.argument .first).setWidth 8

/-- Observable cleanup phase only. File closure, scheduling and privileged kernel
execution are external; arbitrary waiting is permitted before completion. -/
inductive Phase where
  | pending (request : SyscallRequest)
  | exited (status : Byte)

def isPending : Phase → Bool
  | .pending _ => true
  | .exited _ => false

inductive Step : Phase → Phase → Prop where
  | wait {request} (allowed : supported request) : Step (.pending request) (.pending request)
  | finish {request} (allowed : supported request) : Step (.pending request) (.exited (status request))
  | stopped {code} : Step (.exited code) (.exited code)

/-- Kernel contract after entry; stopped observations may stutter forever. -/
def Trace (request : SyscallRequest) (trace : Nat → Phase) : Prop :=
  supported request ∧ trace 0 = .pending request ∧ ∀ index, Step (trace index) (trace (index + 1))

/-- Weak progress assumption for the enabled completion action. It specifies a
state change under persistent pending work, without assuming its result/status. -/
def Fair (trace : Nat → Phase) : Prop :=
  ∀ start, (∀ index, start ≤ index → isPending (trace index) = true) →
    ∃ index, start ≤ index ∧ trace (index + 1) ≠ trace index

theorem Step.preserves {request : SyscallRequest} {before after : Phase}
    (transition : Step before after)
    (invariant : before = .pending request ∨ before = .exited (status request)) :
    after = .pending request ∨ after = .exited (status request) := by
  cases transition with
  | wait _ => exact invariant
  | stopped => exact invariant
  | finish _ =>
    rcases invariant with same | impossible
    · exact Or.inr (congrArg (fun call => Phase.exited (status call)) (Phase.pending.inj same))
    · cases impossible

theorem trace_state (request : SyscallRequest) (trace : Nat → Phase)
    (execution : Trace request trace) (index : Nat) :
    trace index = .pending request ∨ trace index = .exited (status request) := by
  induction index with
  | zero => exact Or.inl execution.2.1
  | succ index induction =>
    exact Step.preserves (execution.2.2 index) induction

theorem exited_status (request : SyscallRequest) (trace : Nat → Phase)
    (execution : Trace request trace) (index : Nat) (code : Byte)
    (exited : trace index = .exited code) : code = status request := by
  rcases trace_state request trace execution index with pending | result
  · rw [exited] at pending
    cases pending
  · exact Phase.exited.inj (exited.symm.trans result)

theorem fair_eventually_exits (request : SyscallRequest) (trace : Nat → Phase)
    (execution : Trace request trace) (fair : Fair trace) :
    ∃ index, trace index = .exited (status request) := by
  classical
  apply Classical.byContradiction
  intro never
  have pending : ∀ index, trace index = .pending request := by
    intro index
    rcases trace_state request trace execution index with waiting | exited
    · exact waiting
    · exact False.elim (never ⟨index, exited⟩)
  have persistent : ∀ index, 0 ≤ index → isPending (trace index) = true := by
    intro index _
    rw [pending index]
    rfl
  obtain ⟨index, _, changed⟩ := fair 0 persistent
  exact changed ((pending (index + 1)).trans (pending index).symm)

/-- An admitted infinite wait witnesses why termination needs progress. -/
theorem indefinite_wait (request : SyscallRequest) (allowed : supported request) :
    Trace request (fun _ => .pending request) ∧ ¬ Fair (fun _ => .pending request) := by
  refine ⟨⟨allowed, rfl, fun _ => .wait allowed⟩, ?_⟩
  intro fair
  obtain ⟨_, _, changed⟩ := fair 0 (by intros; rfl)
  exact changed rfl

/-- There is a terminating fair trace for every admitted request, so the fair
trace guarantee is not made vacuous by an impossible kernel contract. -/
def immediate (request : SyscallRequest) : Nat → Phase
  | 0 => .pending request
  | _ + 1 => .exited (status request)

theorem immediate_admitted (request : SyscallRequest) (allowed : supported request) :
    Trace request (immediate request) ∧ Fair (immediate request) := by
  refine ⟨⟨allowed, rfl, ?_⟩, ?_⟩
  · intro index
    cases index with
    | zero => exact .finish allowed
    | succ index => exact .stopped
  · intro start persistent
    have impossible := persistent (start + 1) (by omega)
    simp [immediate, isPending] at impossible

end EDSL.OS.LinuxExit
