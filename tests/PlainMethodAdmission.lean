/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.PlainMethods
import EDSL.X86.CodeCheck
import tests.TSO64Fixtures
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.PlainMethodAdmission
open X86 OS.TSO64 X86.VCGen.PlainMethods

/-!
Nonvacuous use of the reusable plain-method engine. Both synthetic programs
are installed by the checked allocation/initialization/borrowing operations in
TSO64.fixture. The worker is attached using present authority. Admission does
not assume a successful next instruction, a returned worker, or a future At.

The constructive completion below uses the caller's exact AF choices, then
obtains the full body contract and unique actual access from all_completed.
These witnesses start with empty queues and use no interfering peer; the
separate PlainMethods tests exercise nonempty queues and peer publication.
There is no whole-machine call-history, physical x86, or source-C23 claim.
-/

inductive Kind where
  | load | store

def operation : Kind → Operation
  | .load => .load (.base .rdi)
  | .store => .store (.base .rdi) .rsi

def bytes : Kind → List Byte
  | .load => [0x48, 0x8b, 0x07, 0xc3]
  | .store => [0x48, 0x89, 0x37, 0xc3]

def programWord : Kind → Word
  | .load => 0xc3078b48
  | .store => 0xc3378948

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

def setup (kind : Kind) : Except OS.Atomics64.Fault TSO64.Ready :=
  TSO64.fixture (programWord kind) 0 0x1122334455667788

theorem setup_succeeds (kind : Kind) : (setup kind).toOption.isSome = true := by
  cases kind <;> decide +kernel

def ready (kind : Kind) : TSO64.Ready := checked (setup kind) (setup_succeeds kind)

/-- This checked object retains the manager's preservation proof, including
the actual registered cell, initialized bytes, code loans and original caller.
It is not a hand-constructed assumed well-formed endpoint. -/
theorem setup_world_valid (kind : Kind) : OS.Atomics64.WellFormed (ready kind).checked.world :=
  (ready kind).checked.valid

def context : Context := TSO64.context 262144 131072 0xfedcba9876543210 5

def make (kind : Kind) : Except Fault Worker :=
  makeWorker (ready kind).checked.world 11 context
    (ready kind).codeA (ready kind).callerA [(ready kind).dataA] [(ready kind).atomicA]

theorem make_succeeds (kind : Kind) : (make kind).toOption.isSome = true := by
  cases kind <;> decide +kernel

def worker (kind : Kind) : Worker := checked (make kind) (make_succeeds kind)

theorem made (kind : Kind) : make kind = .ok (worker kind) :=
  checked_ok (make kind) (make_succeeds kind)

def initial (kind : Kind) : OS.TSO64.State := ⟨(ready kind).checked.world, [worker kind]⟩

private theorem attach_singleton {world : World} {actor : Nat} {entry : Context}
    {code caller : Nat} {grants : List OS.Ownership.Ticket}
    {atomics : List OS.Atomics64.HandleId64} {madeWorker : Worker}
    (made : makeWorker world actor entry code caller grants atomics = .ok madeWorker) :
    attach ⟨world, []⟩ actor entry code caller grants atomics =
      .ok ⟨world, [madeWorker]⟩ := by
  simp only [attach, made, ok_bind, pure_ok, List.nil_append]

private theorem empty_valid (world : World) (valid : OS.Atomics64.WellFormed world) :
    WellFormed ⟨world, []⟩ .sharedCell := by
  refine ⟨valid, ?_⟩
  intro worker absent
  cases absent

theorem attached (kind : Kind) :
    attach ⟨(ready kind).checked.world, []⟩ 11 context
      (ready kind).codeA (ready kind).callerA [(ready kind).dataA] [(ready kind).atomicA] =
        .ok (initial kind) :=
  attach_singleton (made kind)

theorem initial_valid (kind : Kind) : WellFormed (initial kind) .sharedCell :=
  attach_valid_for .sharedCell
    (empty_valid (ready kind).checked.world (setup_world_valid kind)) (attached kind)

theorem live (kind : Kind) : (initial kind).workers[0]? = some (worker kind) := rfl

private theorem worker_entry (kind : Kind) : (worker kind).context = context :=
  (makeWorker_valid_for .sharedCell (made kind)).2.2.2

private theorem worker_running (kind : Kind) : (worker kind).phase = .running :=
  (makeWorker_valid_for .sharedCell (made kind)).2.1

private theorem worker_empty (kind : Kind) : (worker kind).pending = [] :=
  (makeWorker_valid_for .sharedCell (made kind)).2.2.1

private theorem worker_counter (kind : Kind) : (worker kind).nextStore = 0 :=
  makeWorker_nextStore (made kind)

private theorem empty_queue_frame (worker : Worker) (empty : worker.pending = [])
    (counter : worker.nextStore = 0) : QueueFrame ⟨[], 0⟩ ⟨worker.pending, worker.nextStore⟩ :=
  ⟨counter, [], empty.symm⟩

def reference : Queue.ManagedRef := ⟨⟨0⟩, ⟨11, ⟨0⟩⟩, ⟨7, ⟨0, 0⟩, 65536⟩⟩

def method (kind : Kind) : Method where
  bytes := bytes kind
  operation := operation kind
  base := 393216
  entry := context.registers
  entryFlags := context.flags
  resources := (worker kind).resources
  reference := reference
  returnAddress := 0x7000
  initialQueue := ⟨[], 0⟩
  size := by cases kind <;> decide +kernel
  codeNoWrap := by cases kind <;> decide +kernel
  originalRsp := by cases kind <;> decide +kernel
  returnCanonical := by decide +kernel
  stackNoWrap := by decide +kernel

theorem present (kind : Kind) : Current (method kind) (initial kind) := by
  refine ⟨initial_valid kind, ?_, ?_, ?_, ?_⟩
  · apply checkCode_sound
    cases kind <;> decide +kernel
  · cases kind <;> decide +kernel
  · cases kind <;> decide +kernel
  · cases kind <;> decide +kernel

theorem entry (kind : Kind) : At (method kind) (.preamble 0 []) (worker kind) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [method]
  · dsimp only [method]
    exact congrArg Context.flags (worker_entry kind)
  · dsimp only [Method.queueAt, method]
    exact empty_queue_frame (worker kind) (worker_empty kind) (worker_counter kind)
  · refine ⟨worker_running kind, ?_, ?_, ?_⟩
    · dsimp only [method]
      rw [worker_entry]
      rfl
    · dsimp only [method]
      exact congrArg Context.registers (worker_entry kind)
    · apply (check_sound (bytes := bytes kind) (operation := operation kind) (padding := []) _).2
      cases kind <;> decide +kernel

/-- Real checked admission enables both MOV directions for either supplied AF,
without assuming an execution result or a successful future action. -/
theorem admitted_access_enabled (kind : Kind) (af : Bool) :
    ∃ result, step (initial kind) (.issue 0 af) .sharedCell = .ok result ∧
      result.2.retired = 1 :=
  enabled (present kind) (live kind) (entry kind)
    (by simp only [Point.remaining, List.length_nil]; omega) af

/-- The generic engine constructs a real two-instruction run, preserving the
exact selected AF at each position. The unique access has an actual machine
origin; the return has the full register/resource/FIFO contract. Literal stack,
caller and flag conclusions are independent observable fixture requirements. -/
theorem admitted_method_completes (kind : Kind) (choices : Nat → Bool) :
    ∃ result final reply,
      schedule (initial kind) [.issue 0 (choices 0), .issue 0 (choices 1)] .sharedCell =
        .ok result ∧
      result.1.workers[0]? = some final ∧
      BodyPost (method kind) final reply ∧
      OneAccess (method kind) 0 (initial kind)
        [.issue 0 (choices 0), .issue 0 (choices 1)] result reply ∧
      X86.VCGen.AtomicMethods.ownIssues 0 [.issue 0 (choices 0), .issue 0 (choices 1)] = 2 ∧
      final.context.registers .rsp = 262152 ∧ final.context.rip = 0x7000 ∧
      final.context.flags = 0x200202 ∧
      OS.TSO64.Return.returnValue (result.1, .returned 0) =
        some (0, (method kind).responded reply .rax) := by
  obtain ⟨actions, result, final, reply, plan, _, _, scheduled, finalLive, located⟩ :=
    complete (present kind) (live kind) (entry kind) choices
  have exactPlan : actions = [.issue 0 (choices 0), .issue 0 (choices 1)] := by
    simpa only [Point.remaining, List.length_nil, List.range_succ, List.range_zero,
      List.map_append, List.map_nil, List.map_cons, List.nil_append,
      List.singleton_append] using plan
  subst actions
  obtain ⟨_, actualReply, post, one, count, returned⟩ :=
    all_completed (present kind) (live kind) (entry kind) scheduled finalLive located.location.1
  exact ⟨result, final, actualReply, scheduled, finalLive, post, one, count,
    post.rsp, post.rip, post.flags, returned⟩

end EDSL.Tests.PlainMethodAdmission

#print axioms EDSL.Tests.PlainMethodAdmission.present
#print axioms EDSL.Tests.PlainMethodAdmission.entry
#print axioms EDSL.Tests.PlainMethodAdmission.admitted_access_enabled
#print axioms EDSL.Tests.PlainMethodAdmission.admitted_method_completes
#audit_edsl
