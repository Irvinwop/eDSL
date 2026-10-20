/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Mutex.Memory

namespace EDSL.OS.Mutex
open X86 AddressSpace

/-- A logical guard identity, never recycled by admitted histories. Principal
labels are proof data rather than authenticated native thread identities. -/
structure Lease where
  identifier : Nat
  actor : Nat
  deriving DecidableEq, Repr

/-- One lock word protects a word in a distinct allocation. The closed
invariant is local to the actual payload value, so unrelated memory can change. -/
structure Config where
  owner : Nat
  lockTicket : Ownership.Ticket
  lockAddress : Word
  dataTicket : Ownership.Ticket
  dataAddress : Word
  invariant : BitVec 32 → Bool

structure Registered where
  config : Config
  holder : Option Lease

/-- This first mutex layer admits one registration at a time. The guard-ID
frontier survives unregister/register cycles. Raw lower-layer updates are not
admitted operations of this protocol. -/
structure State where
  shared : Borrowing.State
  nextLease : Nat
  mutex : Option Registered

def empty (shared : Borrowing.State) : State := ⟨shared, 0, none⟩

def NoReaders (shared : Borrowing.State) (config : Config) : Prop :=
  ∀ identifier loan, shared.loans identifier = some loan →
    loan.ticket.identifier ≠ config.lockTicket.identifier ∧
    loan.ticket.identifier ≠ config.dataTicket.identifier

def Closed (shared : Borrowing.State) (config : Config) : Prop :=
  ∃ value, loadDWord (toMemory shared.resources.space) config.dataAddress = .ok value ∧ config.invariant value = true

structure ValidMutex (state : State) (registered : Registered) : Prop where
  lock : WordValid state.shared registered.config.owner registered.config.lockTicket registered.config.lockAddress
  data : WordValid state.shared registered.config.owner registered.config.dataTicket registered.config.dataAddress
  separate : registered.config.lockTicket.identifier ≠ registered.config.dataTicket.identifier
  atomic : atomicAddressable registered.config.lockAddress = true
  noReaders : NoReaders state.shared registered.config
  phase : match registered.holder with
    | none => loadDWord (toMemory state.shared.resources.space) registered.config.lockAddress = .ok 0 ∧ Closed state.shared registered.config
    | some lease => lease.identifier < state.nextLease ∧
        loadDWord (toMemory state.shared.resources.space) registered.config.lockAddress = .ok 1

def WellFormed (state : State) : Prop :=
  Borrowing.WellFormed state.shared ∧ ∀ registered, state.mutex = some registered → ValidMutex state registered

inductive Fault where
  | authority (fault : Borrowing.Fault)
  | exchange (fault : AtomicExchange.Fault)
  | machine (fault : X86.Error)
  | alreadyRegistered | missingMutex | sameAllocation | reserved
  | invalidInvariant | initiallyLocked | wrongOwner | busy
  | missingGuard | staleGuard | wrongActor
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

def registered (state : State) : Except Fault Registered :=
  match state.mutex with | none => .error .missingMutex | some record => .ok record

/-- Registration validates existing authority and cells without replacing them.
The invariant check is an admissibility gate, not code supplied by XCHG. -/
def register (state : State) (config : Config) : Except Fault State := do
  if state.mutex.isSome then throw .alreadyRegistered
  if config.lockTicket.identifier = config.dataTicket.identifier then throw .sameAllocation
  let lock ← (Ownership.authorize state.shared.resources config.owner config.lockTicket).mapError (fun fault => Fault.authority (.ownership fault))
  let data ← (Ownership.authorize state.shared.resources config.owner config.dataTicket).mapError (fun fault => Fault.authority (.ownership fault))
  if !Ownership.containsWord lock config.lockAddress then throw (.authority (.ownership .outsideAllocation))
  if !Ownership.containsWord data config.dataAddress then throw (.authority (.ownership .outsideAllocation))
  if !atomicAddressable config.lockAddress then throw (.machine (.unsupportedAtomicAddress config.lockAddress))
  if !canStoreDWord (toMemory state.shared.resources.space) config.lockAddress then throw (.machine (.writeDenied config.lockAddress))
  if !canStoreDWord (toMemory state.shared.resources.space) config.dataAddress then throw (.machine (.writeDenied config.dataAddress))
  if !Borrowing.allowed state.shared (.store config.owner config.lockTicket config.lockAddress 0) then throw (.authority .borrowed)
  if !Borrowing.allowed state.shared (.store config.owner config.dataTicket config.dataAddress 0) then throw (.authority .borrowed)
  let lockValue ← (loadDWord (toMemory state.shared.resources.space) config.lockAddress).mapError Fault.machine
  if lockValue ≠ 0 then throw .initiallyLocked
  let value ← (loadDWord (toMemory state.shared.resources.space) config.dataAddress).mapError Fault.machine
  if !config.invariant value then throw .invalidInvariant
  return { state with mutex := some ⟨config, none⟩ }

/-- Every attempt executes its actual XCHG, including 1→1 contention and
reentrant attempts. Only an observed zero grants a fresh guard. -/
structure Attempt where
  state : State
  acquired : Option Lease
  event : AtomicEvent

def tryAcquire (state : State) (actor : Nat) : Except Fault Attempt := do
  let record ← registered state
  let result ← (AtomicExchange.exchangeWord state.shared record.config.owner record.config.lockTicket record.config.lockAddress 1).mapError Fault.exchange
  if result.2 = 0 then
    let lease := { identifier := state.nextLease, actor := actor : Lease }
    return ⟨{ shared := result.1, nextLease := state.nextLease + 1, mutex := some { record with holder := some lease } },
      some lease, ⟨record.config.lockAddress, result.2, 1⟩⟩
  else
    return ⟨{ state with shared := result.1 }, none, ⟨record.config.lockAddress, result.2, 1⟩⟩

def authorize (state : State) (actor : Nat) (lease : Lease) : Except Fault Registered := do
  let record ← registered state
  if lease.actor ≠ actor then throw .wrongActor
  let some current := record.holder | throw .missingGuard
  if current ≠ lease then throw .staleGuard
  return record

def guardLoad (state : State) (actor : Nat) (lease : Lease) : Except Fault (BitVec 32) := do
  let record ← authorize state actor lease
  (loadDWord (toMemory state.shared.resources.space) record.config.dataAddress).mapError Fault.machine

/-- The holder may open the invariant while modifying its protected word.
No arbitrary callback or unchecked lower-layer mutation is admitted. -/
def guardStore (state : State) (actor : Nat) (lease : Lease) (value : BitVec 32) : Except Fault State := do
  let record ← authorize state actor lease
  let result ← (Borrowing.mutate state.shared (.store record.config.owner record.config.dataTicket record.config.dataAddress value)).mapError Fault.authority
  return { state with shared := result.1 }

/-- Successful release checks the actual current payload, closes its invariant,
executes XCHG of the lock with zero, and revokes the guard. The check represents
protocol admission; the binary bridge requires this premise separately. -/
def release (state : State) (actor : Nat) (lease : Lease) : Except Fault (State × AtomicEvent) := do
  let record ← authorize state actor lease
  let value ← (loadDWord (toMemory state.shared.resources.space) record.config.dataAddress).mapError Fault.machine
  if !record.config.invariant value then throw .invalidInvariant
  let result ← (AtomicExchange.exchangeWord state.shared record.config.owner record.config.lockTicket record.config.lockAddress 0).mapError Fault.exchange
  return ({ state with shared := result.1, mutex := some { record with holder := none } },
    ⟨record.config.lockAddress, result.2, 0⟩)

def unregister (state : State) (owner : Nat) : Except Fault State := do
  let record ← registered state
  if record.config.owner ≠ owner then throw .wrongOwner
  if record.holder.isSome then throw .busy
  return { state with mutex := none }

def allowed (state : State) (target : Option Nat) : Bool :=
  match state.mutex with
  | none => true
  | some record => decide (target ≠ some record.config.lockTicket.identifier ∧ target ≠ some record.config.dataTicket.identifier)

def mutate (state : State) (operation : Ownership.Mutation) : Except Fault (State × Option Ownership.Ticket) := do
  if !allowed state operation.target then throw .reserved
  let result ← (Borrowing.mutate state.shared operation).mapError Fault.authority
  return ({ state with shared := result.1 }, result.2)

def readBorrow (state : State) (lender : Nat) (ticket : Ownership.Ticket) (borrower : Nat) (region : Region) : Except Fault (State × Nat) := do
  if !allowed state (some ticket.identifier) then throw .reserved
  let result ← (Borrowing.readBorrow state.shared lender ticket borrower region).mapError Fault.authority
  return ({ state with shared := result.1 }, result.2)

def finishLoan (state : State) (borrower identifier : Nat) : Except Fault State := do
  let result ← (Borrowing.finishLoan state.shared borrower identifier).mapError Fault.authority
  return { state with shared := result }

end EDSL.OS.Mutex
