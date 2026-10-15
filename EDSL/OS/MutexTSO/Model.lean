/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO
import EDSL.OS.MutexReplay.Coverage
import EDSL.OS.MutexReplay.Footprints

namespace EDSL.OS.MutexTSO
open X86

abbrev Physical := TSO.State
abbrev Logical := MutexReplay.State

def logicalMemory (state : Logical) : Memory :=
  AddressSpace.toMemory state.shared.shared.resources.space

/-- The actual queues, without a second ghost copy. Guard exclusivity will
establish that at most one constituent is nonempty. -/
def pending (state : Physical) : StoreBuffer.Buffer :=
  state.workers.flatMap (fun worker => worker.buffer)

def overlay (state : Physical) : Memory := StoreBuffer.view state.memory (pending state)

def architecture (worker : TSO.Worker) : MachineThreads.Worker :=
  ⟨worker.context, worker.returned⟩

def physicalErase (state : Physical) : MachineThreads.State :=
  ⟨state.memory, state.workers.map architecture⟩

/-- Additional target-profile facts, beyond the existing mutex admission.
Ownership alone implies neither payload alignment nor absence of execute permission. -/
structure Profile (config : Mutex.Config) (memory : Memory) : Prop where
  payload : MutexReplay.PayloadAddressable config
  lockData : TSO.dataOnly memory config.lockAddress = true
  payloadData : TSO.dataOnly memory config.dataAddress = true

/-- Relates current architectural state to one current checked OS witness.
Retired stores are already applied to that witness; drains and stalls leave it
unchanged. Every field describes present data, without a future-success or
endpoint premise. -/
structure Rel (config : Mutex.Config) (physical : Physical) (logical : Logical) : Prop where
  invariant : MutexReplay.Invariant config logical
  ready : MutexReplay.ExecutionReady logical
  contexts : physical.workers.map architecture = logical.workers.map MutexReplay.eraseWorker
  buffers : TSO.BuffersValid physical
  payloads : ∀ worker ∈ physical.workers, ∀ store ∈ worker.buffer, store.address = config.dataAddress
  unguarded : ∀ (identifier : Nat) (before : TSO.Worker) (after : MutexReplay.Worker),
    physical.workers[identifier]? = some before → logical.workers[identifier]? = some after →
    after.guard = none → before.buffer = []
  memory : logicalMemory logical = overlay physical
  profile : Profile config physical.memory

structure Admission (config : Mutex.Config) (logical : Logical) (initial : BitVec 32) : Prop where
  invariant : MutexReplay.Invariant config logical
  ready : MutexReplay.ExecutionReady logical
  profile : Profile config (logicalMemory logical)
  closed : MutexReplay.ClosedUnderTwo config
  entry : ∀ worker ∈ logical.workers, worker.phase = .entry
  observed : loadDWord (logicalMemory logical) config.dataAddress = .ok initial

/-- Selection of retired user instructions only; stalls and storage drains
are kept in the physical trace but contribute no replay instruction. -/
def retiredSelections (observations : List TSO.Observation) : List Nat :=
  observations.filterMap fun observation => match observation with
    | .retired identifier _ => some identifier
    | _ => none

/-- Physical drains and blocked issues stutter on the entire logical OS state.
Every retired instruction performs one actual checked dispatch. -/
inductive Lift (before : Logical) : TSO.Action → TSO.Observation → Logical → Prop where
  | retired {identifier : Nat} {event : Option AtomicEvent} {after : Logical}
      (checked : MutexReplay.dispatch before identifier = .ok (after, event)) :
      Lift before (.issue identifier) (.retired identifier event) after
  | blocked (identifier : Nat) : Lift before (.issue identifier) (.blocked identifier) before
  | drained (identifier : Nat) (store : StoreBuffer.Store) :
      Lift before (.drain identifier) (.drained identifier store) before

end EDSL.OS.MutexTSO
