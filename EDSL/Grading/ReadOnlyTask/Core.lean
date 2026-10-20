/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Policy

set_option autoImplicit false

namespace EDSL.Grading
open X86 X86.Sequential

/-- Versioned interpretation of a callable x86 function in the current
sequential decoder/executor. The caller supplies the complete return slot and
full-width ABI arguments. Memory is stable ordinary RAM, with no asynchronous
interference, MMIO, signals, or concurrent agents between modeled steps.
The underlying memory profile assumes alignment checking is disabled and
four-level canonical addresses; LA57, CET, exception handling, and privilege
transitions are outside this callable model.

OS loans authorize logical `Threads.principal worker` identities within the
managed resource model; they do not authenticate a native thread. Relating
native loading, CPU behavior, mappings, calling convention, and interference
control to this model remains an environmental boundary. AF choice streams
model the executor's AF nondeterminism, not arbitrary hardware scheduling. -/
inductive Profile where
  | sequentialReadOnlyX86CallableV1
  | sequentialOwnedWord32X86CallableV1
  | sequentialOwnedWord64X86CallableV1
  deriving DecidableEq, Repr

/-- Original read-only registration contract, retained to state exact
compatibility with the policy-parametric registry. Trusted registration fixes the entire mathematical and resource
contract. Submission checking must apply `Claim` to a trusted task ID and
literal candidate bytes; candidates do not supply this record or premises. -/
structure ReadOnlyTask where
  profile : Profile
  Input : Type
  pre : List Byte → Input → State → Prop
  post : Input → State → State → Prop
  useful : Input → Prop
  Resource : Type
  input : Resource → Input
  resourcePre : List Byte → Resource → State → Prop
  current : Resource → State → Prop
  permission : Resource → State → Read → Prop

/-- Total correctness for every raw mathematical input/state and every AF
stream, plus the current reachable read-only policy. The independent resource
domain additionally retains its admission at return and before every step.
No validity checker, graph, trace, cost, or future-run callback is a premise. -/
structure ReadOnlySemanticClaim (task : ReadOnlyTask) (bytes : List Byte) : Prop where
  machine : ∀ input initial, task.pre bytes input initial →
    AllExecutions initial (fun result => task.post input initial result.state) ∧
      ReadOnlyPolicy initial (fun _ => True) (fun _ _ => True)
  resource : ∀ resource initial, task.resourcePre bytes resource initial →
    AllExecutions initial (fun result =>
      task.post (task.input resource) initial result.state ∧ task.current resource result.state) ∧
      ReadOnlyPolicy initial (task.current resource) (task.permission resource)

/-- Useful nonempty machine and current-resource inputs are separate evidence
from semantic correctness. Independent domain constructors establish this from
admitted bytes without executing them. They do not restrict either universal
domain in `ReadOnlySemanticClaim`. -/
structure ReadOnlyNonvacuous (task : ReadOnlyTask) (bytes : List Byte) : Prop where
  machine : ∃ input initial, task.useful input ∧ task.pre bytes input initial
  resource : ∃ resource initial, task.useful (task.input resource) ∧ task.resourcePre bytes resource initial

end EDSL.Grading
