/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Runtime
import EDSL.OS.Futex.Lifecycle
import EDSL.Examples.FutexStubs

namespace EDSL.Examples.Futex
open X86 OS OS.AddressSpace

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The publisher performs an actual locked exchange before its actual wake
stub. The separate worker's ordinary write deliberately remains buffered. -/
def publisherBytes : List Byte := [0xb8, 1, 0, 0, 0, 0x87, 0x07] ++ FutexStubs.Profile.wakeOne.bytes
def payloadBytes : List Byte := [0xb8, 0x44, 0x33, 0x22, 0x11, 0x89, 0x06, 0xc3]

def space : AddressSpace.Space where
  cells address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4109 then
      (FutexStubs.Profile.wait.bytes[address.toNat - 4096]?).map fun byte => ⟨byte, readExecute⟩
    else if 8192 ≤ address.toNat ∧ address.toNat < 8217 then
      (publisherBytes[address.toNat - 8192]?).map fun byte => ⟨byte, readExecute⟩
    else if 16384 ≤ address.toNat ∧ address.toNat < 16392 then
      (payloadBytes[address.toNat - 16384]?).map fun byte => ⟨byte, readExecute⟩
    else if (32768 ≤ address.toNat ∧ address.toNat < 32776) ∨
        (32800 ≤ address.toNat ∧ address.toNat < 32808) ∨
        (32832 ≤ address.toNat ∧ address.toNat < 32840) ∨
        (32864 ≤ address.toNat ∧ address.toNat < 32872) then
      some ⟨if address.toNat % 32 = 1 then 0x60 else 0, readOnly⟩
    else if (65536 ≤ address.toNat ∧ address.toNat < 65540) ∨
        (131072 ≤ address.toNat ∧ address.toNat < 131076) then some ⟨0, readWrite⟩
    else if 196608 ≤ address.toNat ∧ address.toNat < 196612 then some ⟨0xa5, readOnly⟩
    else none

inductive PrepareAction where
  | mutate (operation : Ownership.Mutation)
  | issue (owner : Nat) (ticket : Ownership.Ticket) (actor : Nat) (address : Word)
  | loan (lender : Nat) (ticket : Ownership.Ticket) (borrower : Nat) (region : Region)

def prepareStep (state : Atomics.State) : PrepareAction → Except Atomics.Fault Atomics.State
  | .mutate operation => do return (← Atomics.mutate state operation).1
  | .issue owner ticket actor address => do return (← Atomics.issue state owner ticket actor address).1
  | .loan lender ticket borrower region => do return (← Atomics.readBorrow state lender ticket borrower region).1

def prepareRun (state : Atomics.State) : List PrepareAction → Except Atomics.Fault Atomics.State
  | [] => .ok state
  | action :: rest => do prepareRun (← prepareStep state action) rest

theorem prepareStep_history {state after : Atomics.State} {action : PrepareAction}
    (success : prepareStep state action = .ok after) : Atomics.History state after := by
  cases action with
  | mutate operation =>
    cases performed : Atomics.mutate state operation with
    | error fault => simp [prepareStep, performed] at success
    | ok result => simp [prepareStep, performed] at success; subst after; exact .next (.mutate performed) .refl
  | issue owner ticket actor address =>
    cases performed : Atomics.issue state owner ticket actor address with
    | error fault => simp [prepareStep, performed] at success
    | ok result => simp [prepareStep, performed] at success; subst after; exact .next (.issue performed) .refl
  | loan lender ticket borrower region =>
    cases performed : Atomics.readBorrow state lender ticket borrower region with
    | error fault => simp [prepareStep, performed] at success
    | ok result => simp [prepareStep, performed] at success; subst after; exact .next (.readBorrow performed) .refl

theorem history_trans {before middle after : Atomics.State}
    (head : Atomics.History before middle) (tail : Atomics.History middle after) : Atomics.History before after := by
  induction head with
  | refl => exact tail
  | next first _ ih => exact .next first (ih tail)

theorem prepareRun_history {state after : Atomics.State} {actions : List PrepareAction}
    (success : prepareRun state actions = .ok after) : Atomics.History state after := by
  induction actions generalizing state with
  | nil => simp [prepareRun] at success; subst after; exact .refl
  | cons action rest ih =>
    cases first : prepareStep state action with
    | error fault => simp [prepareRun, first] at success
    | ok middle =>
      exact history_trans (prepareStep_history first) (ih (by simpa [prepareRun, first] using success))

/-- Actual adoption preserves loader bytes. Code and complete return words
have separate loans; W has compatible atomic handles and no read loan. The
last read loan is unrelated and must survive the worker cohort's lifetime. -/
def prepareActions : List PrepareAction :=
  [.mutate (.adopt 7 ⟨65536, 4⟩), .mutate (.adopt 7 ⟨131072, 4⟩),
   .mutate (.adopt 7 ⟨4096, 13⟩), .mutate (.adopt 7 ⟨8192, 25⟩),
   .mutate (.adopt 7 ⟨16384, 8⟩),
   .mutate (.adopt 7 ⟨32768, 8⟩), .mutate (.adopt 7 ⟨32800, 8⟩),
   .mutate (.adopt 7 ⟨32832, 8⟩), .mutate (.adopt 7 ⟨32864, 8⟩),
   .mutate (.adopt 8 ⟨196608, 4⟩),
   .issue 7 ⟨0, 0⟩ 90 65536, .issue 7 ⟨0, 0⟩ 11 65536,
   .loan 7 ⟨2, 0⟩ 10 ⟨4096, 13⟩, .loan 7 ⟨5, 0⟩ 10 ⟨32768, 8⟩,
   .loan 7 ⟨3, 0⟩ 11 ⟨8192, 25⟩, .loan 7 ⟨6, 0⟩ 11 ⟨32800, 8⟩,
   .loan 7 ⟨4, 0⟩ 12 ⟨16384, 8⟩, .loan 7 ⟨7, 0⟩ 12 ⟨32832, 8⟩,
   .loan 7 ⟨2, 0⟩ 13 ⟨4096, 13⟩, .loan 7 ⟨8, 0⟩ 13 ⟨32864, 8⟩,
   .loan 8 ⟨9, 0⟩ 99 ⟨196608, 4⟩]

def seed : Atomics.State := Atomics.empty (Borrowing.empty (Ownership.empty space))

def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

def authority : Atomics.State := checked (prepareRun seed prepareActions) (by rfl)

theorem authority_valid : Atomics.WellFormed authority :=
  (prepareRun_history (checked_ok (prepareRun seed prepareActions) (by rfl))).wellFormed
    (Atomics.empty_wellFormed _ (Borrowing.empty_wellFormed _ (Ownership.empty_wellFormed space)))

def registration : OS.Futex.Resources.Registration := ⟨7, ⟨0, 0⟩, 90, 65536, 0⟩

def profile : OS.Futex.Physical.Profile :=
  { service := ⟨0, 90, ⟨4096, 2^47⟩⟩
    payload := fun worker => if worker = 2 then some ⟨7, ⟨1, 0⟩, 131072⟩ else none
    atomic := fun worker => if worker = 1 then some ⟨11, 1⟩ else none }

def context (worker : Nat) : Threads.Context where
  registers register :=
    if register = .rsp then BitVec.ofNat 64 (32768 + 32 * worker)
    else if register = .rdi then 65536
    else if register = .rsi ∧ worker = 2 then 131072
    else if register = .rdx ∨ register = .r10 ∨ register = .r8 ∨ register = .r9 then 0
    else 0xdeadbeefabcdef01
  rip := if worker = 1 then 8192 else if worker = 2 then 16384 else 4096
  flags := 0x246

def initial : OS.Futex.State :=
  ⟨OS.Suspend.initial ⟨toMemory authority.shared.resources.space,
    [⟨context 0, false, []⟩, ⟨context 1, false, []⟩,
     ⟨context 2, false, []⟩, ⟨context 3, false, []⟩]⟩,
    authority, some registration, fun _ => none, []⟩

theorem initial_valid : OS.Futex.WellFormed profile.service initial := by
  have buffers : TSO.BuffersValid initial.suspended.machine := by
    intro worker member store queued
    change worker ∈ [⟨context 0, false, []⟩, ⟨context 1, false, []⟩,
      ⟨context 2, false, []⟩, ⟨context 3, false, []⟩] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> cases queued
  refine ⟨OS.Suspend.WellFormed.initial buffers, authority_valid, ?_, ?_, by simp [initial], ?_, ?_⟩
  · intro identifier call found
    cases found
  · intro worker saved pending
    cases pending
  · intro identifier
    simp [initial]
  · intro left a right b found
    cases found

theorem initial_registration_live : OS.Futex.Resources.Valid initial.authority registration := by rfl

theorem initial_memory_coupled :
    toMemory initial.authority.shared.resources.space = initial.suspended.machine.memory := rfl

def waiterEntry (worker : Nat) : List OS.Futex.Runtime.Action := [.issue worker, .issue worker, .issue worker]
def publisherExchange : List OS.Futex.Runtime.Action := [.issue 1, .issue 1]
def publisherEntry : List OS.Futex.Runtime.Action := [.issue 1, .issue 1, .issue 1, .issue 1]
def queuePayload : List OS.Futex.Runtime.Action := [.issue 2, .issue 2]

/-- Current-RAM mismatch after actual entry and peer XCHG. The completion
uses service-derived full-width EAGAIN and the actual RET. -/
def mismatchActions (flags rcx r11 : Word) : List OS.Futex.Runtime.Action :=
  waiterEntry 0 ++ publisherExchange ++
    [.service (.compare 0), .service (.resume 0 flags rcx r11), .issue 0]

def mismatch : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule profile initial (mismatchActions 0x8d7 0x1234 0x5678)) (by rfl)

theorem mismatch_ok :
    OS.Futex.Runtime.schedule profile initial (mismatchActions 0x8d7 0x1234 0x5678) = .ok mismatch :=
  checked_ok _ _

theorem mismatch_result :
    ∃ worker, mismatch.1.suspended.machine.workers[0]? = some worker ∧
      worker.returned = true ∧ worker.context.registers .rax = -(BitVec.ofNat 64 11) ∧
      worker.context.registers .rsp = 32776 ∧ worker.context.rip = 24576 ∧
      loadDWord mismatch.1.suspended.machine.memory 65536 = .ok 1 := by
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A third worker's disjoint FIFO survives entry, queuing, peer publication,
wake, both resumptions and both actual returns. No syscall flush is inserted. -/
def wokenActions : List OS.Futex.Runtime.Action :=
  queuePayload ++ waiterEntry 0 ++ [.service (.compare 0)] ++
  publisherExchange ++ publisherEntry ++
  [.service (.wake 1 (some 0)), .service (.resume 0 0x8d7 0x1234 0x5678), .issue 0,
   .service (.resume 1 0x246 0x9876 0x5432), .issue 1]

def woken : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule profile initial wokenActions) (by rfl)

theorem woken_ok : OS.Futex.Runtime.schedule profile initial wokenActions = .ok woken := checked_ok _ _

def drained : OS.Futex.State × OS.Suspend.Observation :=
  checked (OS.Futex.Physical.drain profile woken.1 2) (by rfl)

theorem drained_ok : OS.Futex.Physical.drain profile woken.1 2 = .ok drained := checked_ok _ _

theorem woken_results :
    ∃ waiter publisher buffered,
      woken.1.suspended.machine.workers[0]? = some waiter ∧ waiter.returned = true ∧
      waiter.context.registers .rax = 0 ∧
      woken.1.suspended.machine.workers[1]? = some publisher ∧ publisher.returned = true ∧
      publisher.context.registers .rax = 1 ∧
      woken.1.suspended.machine.workers[2]? = some buffered ∧
      buffered.buffer = [⟨131072, 0x11223344⟩] ∧
      loadDWord woken.1.suspended.machine.memory 65536 = .ok 1 ∧
      loadDWord woken.1.suspended.machine.memory 131072 = .ok 0 ∧
      loadDWord drained.1.suspended.machine.memory 65536 = .ok 1 ∧
      loadDWord drained.1.suspended.machine.memory 131072 = .ok 0x11223344 := by
  exact ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Both waiters begin with actual SYSCALL capture and comparison, before an
actual WAKE1 capture. Either eligible invocation can be selected. -/
def twoQueuedActions : List OS.Futex.Runtime.Action :=
  waiterEntry 0 ++ [.service (.compare 0)] ++ waiterEntry 3 ++ [.service (.compare 1)] ++
    publisherExchange ++ publisherEntry

def twoQueued : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule profile initial twoQueuedActions) (by rfl)

theorem twoQueued_ok : OS.Futex.Runtime.schedule profile initial twoQueuedActions = .ok twoQueued := checked_ok _ _

def choice (target : Nat) (accepted : (OS.Futex.wakeOne twoQueued.1 2 (some target)).toOption.isSome = true) : OS.Futex.State :=
  checked (OS.Futex.wakeOne twoQueued.1 2 (some target)) accepted

theorem either_waiter_enabled :
    ∃ first second, OS.Futex.wakeOne twoQueued.1 2 (some 0) = .ok first ∧
      OS.Futex.wakeOne twoQueued.1 2 (some 1) = .ok second ∧
      first.queue = [1] ∧ second.queue = [0] := by
  exact ⟨choice 0 (by rfl), choice 1 (by rfl), checked_ok _ _, checked_ok _ _, rfl, rfl⟩

def retryActions : List OS.Futex.Runtime.Action :=
  waiterEntry 0 ++ [.service (.compare 0)] ++ publisherExchange ++
    [.service (.retry 0), .service (.compare 0), .service (.resume 0 0 0 0), .issue 0]

def retried : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule profile initial retryActions) (by rfl)

def spuriousActions : List OS.Futex.Runtime.Action :=
  waiterEntry 0 ++ [.service (.compare 0), .service (.spurious 0), .service (.resume 0 0 0 0), .issue 0]

def spurious : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule profile initial spuriousActions) (by rfl)

theorem retry_and_spurious_results :
    ∃ retryWorker spuriousWorker,
      retried.1.suspended.machine.workers[0]? = some retryWorker ∧ retryWorker.returned = true ∧
      retryWorker.context.registers .rax = -(BitVec.ofNat 64 11) ∧
      spurious.1.suspended.machine.workers[0]? = some spuriousWorker ∧ spuriousWorker.returned = true ∧
      spuriousWorker.context.registers .rax = 0 ∧
      loadDWord spurious.1.suspended.machine.memory 65536 = .ok 0 := by
  exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem consumed_call_rejected :
    OS.Futex.resumeReady profile.service spurious.1 0 0 0 0 = .error .missingCall := by rfl

def parkedActions : List OS.Futex.Runtime.Action := waiterEntry 0 ++ [.service (.compare 0)]
def parked : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule profile initial parkedActions) (by rfl)

/-- Actual pending syscall selection may stutter forever. Queue membership
does not entail fairness, notification, acquisition, or eventual return. -/
theorem parked_forever :
    OS.Futex.Runtime.Infinite profile (fun _ => parked.1) (fun _ => .issue 0)
      (fun _ => .physical (.parked 0 0)) := by
  intro _
  rfl

def completedActions : List OS.Futex.Runtime.Action :=
  waiterEntry 3 ++ [.service (.compare 2), .service (.resume 2 0 0 0), .issue 3, .issue 2, .drain 2]

/-- All four workers actually execute RET; the last payload drain remains
necessary after its producer returns. This supplies a finite teardown witness. -/
def completed : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule profile woken.1 completedActions) (by rfl)

theorem completed_ok : OS.Futex.Runtime.schedule profile woken.1 completedActions = .ok completed := checked_ok _ _

def cleanupPlan : OS.Futex.Lifecycle.Plan :=
  ⟨[(10, 0), (10, 1), (11, 2), (11, 3), (12, 4), (12, 5), (13, 6), (13, 7)], [(11, 1)]⟩

def collected : OS.Futex.State :=
  checked (OS.Futex.Lifecycle.collect cleanupPlan completed.1) (by rfl)

theorem collected_ok : OS.Futex.Lifecycle.collect cleanupPlan completed.1 = .ok collected := checked_ok _ _

/-- The general positive collection theorem applies to these current live
records. Future cleanup success is not part of the premise. -/
theorem collection_enabled_from_current : ∃ after, OS.Futex.Lifecycle.collect cleanupPlan completed.1 = .ok after := by
  apply OS.Futex.Lifecycle.collect_enabled cleanupPlan completed.1 registration (by rfl) (by rfl) (by decide)
  · intro borrower identifier member
    simp only [cleanupPlan, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with a | a | a | a | a | a | a | a
    all_goals rcases a with ⟨rfl, rfl⟩; exact ⟨_, rfl, rfl⟩
  · decide
  · intro actor identifier member
    change (actor, identifier) ∈ [(11, 1), (90, 0)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with a | a
    all_goals rcases a with ⟨rfl, rfl⟩; exact ⟨_, rfl, rfl⟩

theorem collection_frames :
    collected.suspended = completed.1.suspended ∧
      collected.authority.shared.resources = completed.1.authority.shared.resources ∧
      collected.authority.nextHandle = completed.1.authority.nextHandle ∧
      collected.authority.shared.nextLoan = completed.1.authority.shared.nextLoan ∧
      collected.authority.shared.loans 8 = completed.1.authority.shared.loans 8 ∧
      collected.authority.shared.loans 8 ≠ none ∧
      collected.registration = none := by
  obtain ⟨_, _, _, registrationCleared, machine, _, _, resources, loanFrontier, handleFrontier, loans, _, _⟩ :=
    OS.Futex.Lifecycle.collect_effect collected_ok
  refine ⟨machine, resources, handleFrontier, loanFrontier, ?_, ?_, registrationCleared⟩
  · simpa [cleanupPlan] using loans 8
  · intro absent
    have live : (collected.authority.shared.loans 8).isSome = true := rfl
    rw [absent] at live
    cases live

def enteredOnly : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule profile initial (waiterEntry 0)) (by rfl)

def readyOnly : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule profile initial
    (waiterEntry 0 ++ [.service (.compare 0)] ++ publisherExchange ++ publisherEntry ++
      [.service (.wake 1 (some 0))])) (by rfl)

theorem active_collection_rejected :
    OS.Futex.Lifecycle.collect cleanupPlan enteredOnly.1 = .error .busy ∧
      OS.Futex.Lifecycle.collect cleanupPlan parked.1 = .error .busy ∧
      OS.Futex.Lifecycle.collect cleanupPlan readyOnly.1 = .error .busy := by
  exact ⟨rfl, rfl, rfl⟩

def wakeOnlyInitial : OS.Futex.State :=
  { initial with
    suspended := { initial.suspended with
      machine := { initial.suspended.machine with
        workers := initial.suspended.machine.workers.set 1
          ⟨{ (context 1) with rip := 8199 }, false, []⟩ } } }

def noCreditActions : List OS.Futex.Runtime.Action :=
  publisherEntry ++ [.service (.wake 0 none), .service (.resume 0 0 0 0), .issue 1] ++
    waiterEntry 0 ++ [.service (.compare 1)]

def noCredit : OS.Futex.State × List OS.Futex.Runtime.Observation :=
  checked (OS.Futex.Runtime.schedule profile wakeOnlyInitial noCreditActions) (by rfl)

/-- A completed empty WAKE saves no future credit: a later equal WAIT can
stay queued indefinitely while the word remains zero. -/
theorem wake_before_wait_no_credit :
    loadDWord noCredit.1.suspended.machine.memory 65536 = .ok 0 ∧
      noCredit.1.queue = [1] ∧
      OS.Futex.Runtime.Infinite profile (fun _ => noCredit.1) (fun _ => .issue 0)
        (fun _ => .physical (.parked 0 1)) := by
  exact ⟨rfl, rfl, fun _ => rfl⟩

end EDSL.Examples.Futex
