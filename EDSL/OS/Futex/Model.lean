/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Resources
import EDSL.OS.Suspend

namespace EDSL.OS.Futex
open X86

/-- One address space and one service principal. The executable client cohort
is a separate admission contract, rather than an instruction decoder gate. -/
structure Config where
  spaceId : Nat
  serviceActor : Nat
  userInterval : Resources.UserInterval
  deriving DecidableEq, Repr

inductive Op where
  | wait (expected : BitVec 32)
  | wakeOne
  deriving DecidableEq, Repr

/-- Registered WAIT admits zero or EAGAIN; registered WAKE1 admits zero or one.
No fault, timeout, signal, or restart outcome exists in this profile. -/
inductive Outcome : Op → Type where
  | waitZero : Outcome (.wait expected)
  | waitAgain : Outcome (.wait expected)
  | wakeZero : Outcome .wakeOne
  | wakeOne : Outcome .wakeOne
  deriving DecidableEq, Repr

def Outcome.raw : Outcome op → Word
  | .waitZero => 0
  | .waitAgain => -(BitVec.ofNat 64 11)
  | .wakeZero => 0
  | .wakeOne => 1

inductive Origin where
  | mismatch | emptyWake | wake (invocation : Nat) | spurious
  deriving DecidableEq, Repr

inductive Phase : Op → Type where
  | entered : Phase op
  | queued : Phase (.wait expected)
  | ready (outcome : Outcome op) (origin : Origin) : Phase op
  deriving DecidableEq, Repr


def Phase.isQueued : {op : Op} → Phase op → Bool
  | _, .entered => false
  | _, .queued => true
  | _, .ready _ _ => false

structure Call where
  worker : Nat
  op : Op
  pin : Nat
  phase : Phase op
  deriving DecidableEq, Repr

structure State where
  suspended : Suspend.State
  authority : Atomics.State
  registration : Option Resources.Registration
  calls : Nat → Option Call
  queue : List Nat

inductive Fault where
  | suspended (fault : Suspend.Fault)
  | resources (fault : Atomics.Fault)
  | unregistered | noPending | staleCall | wrongWorker | unsupportedABI
  | missingCall | identityCollision | wrongPhase | ineligible | queueNotEmpty
  | unsupportedAddress
  deriving DecidableEq, Repr

@[simp] theorem throw_error (fault : Fault) : (throw fault : Except Fault α) = .error fault := rfl

/-- Full registers are checked, including zero extension of expected32. This
is deliberately narrower than Linux's general futex ABI. -/
def classify (request : SyscallRequest) : Except Fault Op := do
  if request.user.registers .rax ≠ 202 then throw .unsupportedABI
  if request.user.registers .r10 ≠ 0 ∨ request.user.registers .r8 ≠ 0 ∨
      request.user.registers .r9 ≠ 0 then throw .unsupportedABI
  if request.user.registers .rsi = 128 then
    let expected := (request.user.registers .rdx).setWidth 32
    if request.user.registers .rdx ≠ expected.setWidth 64 then throw .unsupportedABI
    return .wait expected
  else if request.user.registers .rsi = 129 ∧ request.user.registers .rdx = 1 then
    return .wakeOne
  else throw .unsupportedABI

def putCall (state : State) (identifier : Nat) (call : Call) : State :=
  { state with calls := fun query => if query = identifier then some call else state.calls query }

def setPhase (state : State) (identifier : Nat) (call : Call) (phase : Phase call.op) : State :=
  putCall state identifier { call with phase := phase }

/-- Linux-profile admission checks the complete lower-userspace word and
excludes executable storage. Kernel access_ok and physical mappings remain
external conformance obligations for the selected target interval. -/
def targetSupported (config : Config) (authority : Atomics.State) (address : Word) : Bool :=
  decide (config.userInterval.AdmitsWord address) &&
    TSO.dataOnly (AddressSpace.toMemory authority.shared.resources.space) address

/-- The input already contains an actual Suspend entry. Capture checks that
exact Saved record and retains its pin atomically with adding the service record.
There is no second invocation allocator and no copied request memory. -/
def captureEntered (config : Config) (state : State) (worker invocation : Nat) : Except Fault State := do
  let some saved := state.suspended.pending worker | throw .noPending
  if saved.identifier ≠ invocation then throw .staleCall
  if saved.worker ≠ worker then throw .wrongWorker
  if (state.calls invocation).isSome then throw .identityCollision
  let operation ← classify saved.request
  let some registration := state.registration | throw .unregistered
  if saved.request.user.registers .rdi ≠ registration.address then throw .unsupportedABI
  if !targetSupported config state.authority registration.address then throw .unsupportedAddress
  let retained ← (Resources.retainCall state.authority registration config.serviceActor).mapError Fault.resources
  return putCall { state with authority := retained.1 } invocation
    ⟨worker, operation, retained.2, .entered⟩

end EDSL.OS.Futex
