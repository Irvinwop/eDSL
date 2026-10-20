/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Lifecycle
import EDSL.OS.Mutex

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

def accumulator (worker : Worker) : BitVec 32 :=
  (worker.context.registers .rax).setWidth 32

/-- The loop's private control fact, independent of a final-value checker. -/
def Control (worker : Worker) : Prop :=
  match worker.phase with
  | .entry => worker.guard = none
  | .acquiring => worker.guard = none ∧ worker.context.registers .rax = 1
  | .comparing => match worker.guard with
    | none => worker.context.registers .rax = 1
    | some _ => worker.context.registers .rax = 0
  | .branching =>
    worker.context.flags.getLsbD 6 = worker.guard.isSome ∧
    match worker.guard with
    | none => worker.context.registers .rax = 1
    | some _ => worker.context.registers .rax = 0
  | .loading | .incrementingFirst | .storingFirst | .incrementingSecond
  | .storingSecond | .preparingRelease => worker.guard.isSome = true
  | .releasing => worker.guard.isSome = true ∧ worker.context.registers .rax = 0
  | .finishing => worker.guard = none
  | .returning | .completed => worker.guard = none ∧ worker.context.registers .rax = 0

/-- The saved payload is recoverable from EAX until release preparation, so
this proof invariant needs no ghost register or extra execution operation. -/
def Payload (shared : Mutex.State) (config : Mutex.Config) (worker : Worker) : Prop :=
  let observed := loadDWord (toMemory shared.shared.resources.space) config.dataAddress
  let value := accumulator worker
  match worker.phase with
  | .comparing | .branching | .loading | .releasing => Mutex.Closed shared.shared config
  | .incrementingFirst => observed = .ok value ∧ config.invariant value = true
  | .storingFirst => observed = .ok (value - 1) ∧ config.invariant (value - 1) = true
  | .incrementingSecond => observed = .ok value ∧ config.invariant (value - 1) = true
  | .storingSecond => observed = .ok (value - 1) ∧ config.invariant (value - 2) = true
  | .preparingRelease => observed = .ok value ∧ config.invariant value = true
  | _ => True

structure WorkerInvariant (shared : Mutex.State) (config : Mutex.Config) (identifier : Nat) (worker : Worker) : Prop where
  context : contextValid worker = true
  operands : worker.entry.registers .rdi = config.lockAddress ∧ worker.entry.registers .rsi = config.dataAddress
  control : Control worker
  authority : ∀ lease, worker.guard = some lease →
    ∃ record, Mutex.authorize shared (principal identifier) lease = .ok record ∧ record.config = config
  payload : ∀ lease, worker.guard = some lease → Payload shared config worker

def Registered (shared : Mutex.State) (config : Mutex.Config) : Prop :=
  ∃ record, shared.mutex = some record ∧ record.config = config

def Tracked (state : State) : Prop :=
  ∀ record lease, state.shared.mutex = some record → record.holder = some lease →
    ∃ (identifier : Nat) (worker : Worker), state.workers[identifier]? = some worker ∧ worker.guard = some lease

structure Invariant (config : Mutex.Config) (state : State) : Prop where
  shared : Mutex.WellFormed state.shared
  registered : Registered state.shared config
  workers : ∀ identifier worker, state.workers[identifier]? = some worker → WorkerInvariant state.shared config identifier worker
  tracked : Tracked state

def ClosedUnderTwo (config : Mutex.Config) : Prop :=
  ∀ value, config.invariant value = true → config.invariant (value + 2) = true

theorem lsb_add_two (value : BitVec 32) : (value + 2).getLsbD 0 = value.getLsbD 0 := by
  rw [BitVec.getLsbD_add (by decide)]
  simp

theorem even_closed (config : Mutex.Config)
    (predicate : config.invariant = fun value => !value.getLsbD 0) : ClosedUnderTwo config := by
  intro value satisfied
  simpa only [predicate, lsb_add_two] using satisfied

/-- Number of actual protected stores already performed by this worker. -/
def credit (worker : Worker) : Nat :=
  match worker.phase with
  | .incrementingSecond | .storingSecond => 1
  | .preparingRelease | .releasing | .finishing | .returning | .completed => 2
  | _ => 0

def credits (state : State) : Nat := (state.workers.map credit).sum

def Accounted (config : Mutex.Config) (initial : BitVec 32) (state : State) : Prop :=
  loadDWord (toMemory state.shared.shared.resources.space) config.dataAddress =
    .ok (initial + BitVec.ofNat 32 (credits state))

end EDSL.OS.MutexReplay
