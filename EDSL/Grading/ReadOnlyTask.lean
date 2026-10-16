/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Policy
import EDSL.Pair32.Resources
import EDSL.Stride32.Resources

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
  deriving DecidableEq, Repr

structure PairInput where
  valuesA : List (BitVec 32)
  valuesB : List (BitVec 32)
  target : Word

structure StrideInput where
  values : List (BitVec 32)
  count : Nat
  target : Word

structure PairResources where
  shared : OS.Borrowing.State
  callA : OS.ArrayResources.Call
  callB : OS.ArrayResources.Call

structure StrideResources where
  shared : OS.Borrowing.State
  call : OS.ArrayResources.Call
  count : Nat

/-- Exactly the published pair admission and ABI binding premises. Compatible
read-only A/B aliases, including shared input loan IDs, remain admitted. -/
structure PairResourcePre (bytes : List Byte) (resource : PairResources)
    (initial : State) : Prop where
  code : resource.callA.bytes = bytes
  admitted : Pair32.PairAdmission resource.shared resource.callA resource.callB initial
  entry : initial.rip = resource.callA.code
  stack : initial.registers .rsp = resource.callA.stack
  baseA : initial.registers .rdi = resource.callA.base
  countA : initial.registers .rsi = BitVec.ofNat 64 resource.callA.values.length
  baseB : initial.registers .rdx = resource.callB.base
  countB : initial.registers .rcx = BitVec.ofNat 64 resource.callB.values.length

/-- Exactly the published stride admission, contiguous logical array length,
and ABI binding premises. Empty inputs impose no input-loan requirement. -/
structure StrideResourcePre (bytes : List Byte) (resource : StrideResources)
    (initial : State) : Prop where
  code : resource.call.bytes = bytes
  admitted : OS.ArrayResources.Admission resource.shared resource.call initial
  entry : initial.rip = resource.call.code
  stack : initial.registers .rsp = resource.call.stack
  base : initial.registers .rdi = resource.call.base
  length : resource.call.values.length = 2 * resource.count
  count : initial.registers .rsi = BitVec.ofNat 64 resource.count

/-- Current resources imply the unchanged raw mathematical machine domain,
without assuming decoding, CFG validity, or any future successful run. -/
theorem PairResourcePre.machine {bytes : List Byte} {resource : PairResources} {initial : State}
    (pre : PairResourcePre bytes resource initial) :
    Pair32.Pre bytes initial resource.callA.values resource.callB.values resource.callA.target := by
  have machine := Pair32.pre_of_admission pre.admitted pre.entry pre.stack pre.baseA
    pre.countA pre.baseB pre.countB
  rwa [pre.code] at machine

theorem StrideResourcePre.machine {bytes : List Byte} {resource : StrideResources} {initial : State}
    (pre : StrideResourcePre bytes resource initial) :
    Stride32.Pre bytes initial resource.call.values resource.count resource.call.target := by
  have machine := Stride32.pre_of_admission pre.admitted pre.entry pre.stack pre.base pre.length pre.count
  rwa [pre.code] at machine

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

/-- Independent modular sum of both lists, with the published full memory,
return, register, and nonarithmetic-flag frame. No trace order or cost is fixed. -/
def pairReadOnlyTask : ReadOnlyTask where
  profile := .sequentialReadOnlyX86CallableV1
  Input := PairInput
  pre bytes input initial := Pair32.Pre bytes initial input.valuesA input.valuesB input.target
  post input initial final := Pair32.Post initial input.valuesA input.valuesB input.target final
  useful input := input.valuesA ≠ [] ∧ input.valuesB ≠ []
  Resource := PairResources
  input resource := ⟨resource.callA.values, resource.callB.values, resource.callA.target⟩
  resourcePre := PairResourcePre
  current resource := Pair32.PairAdmission resource.shared resource.callA resource.callB
  permission resource _ := OS.ArrayResources.ReadPermission resource.shared resource.callA.worker

/-- Independent even-index modular sum of the contiguous logical input, with
the published return and ABI frame. The odd payload words remain in the input
domain; implementations need not use the published instruction selection. -/
def strideReadOnlyTask : ReadOnlyTask where
  profile := .sequentialReadOnlyX86CallableV1
  Input := StrideInput
  pre bytes input initial := Stride32.Pre bytes initial input.values input.count input.target
  post input initial final := Stride32.Post initial input.values input.count input.target final
  useful input := 0 < input.count
  Resource := StrideResources
  input resource := ⟨resource.call.values, resource.count, resource.call.target⟩
  resourcePre := StrideResourcePre
  current resource := OS.ArrayResources.Admission resource.shared resource.call
  permission resource _ := OS.ArrayResources.ReadPermission resource.shared resource.call.worker

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
