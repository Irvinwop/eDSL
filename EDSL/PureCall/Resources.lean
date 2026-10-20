/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.PureCall.Contract
import EDSL.OS.CallResources
import EDSL.Grading.ReadOnlyTask.Core

set_option warningAsError true

namespace EDSL.PureCall
open X86 X86.Sequential OS

structure Resources (spec : Spec) where
  shared : Borrowing.State
  call : CallResources.Call
  value : spec.Input

def resourceInput {spec : Spec} (resource : Resources spec) : Invocation spec :=
  ⟨resource.value, resource.call.returnAddress⟩

/-- Current original resources and ABI bindings. The resource contract has no
future-success premise, instruction decoder or mathematical output premise. -/
structure ResourcePre (spec : Spec) (bytes : List Byte)
    (resource : Resources spec) (initial : State) : Prop where
  current : CallResources.Current resource.call resource.shared initial
  code : resource.call.bytes = bytes
  entry : initial.rip = resource.call.code
  stack : initial.registers .rsp = resource.call.stack
  domain : spec.domain resource.value
  arguments : Bound spec resource.value initial

theorem ResourcePre.machine {spec bytes resource initial}
    (pre : ResourcePre spec bytes resource initial) :
    Pre spec bytes (resourceInput resource) initial := by
  have contract := pre.current.contract
  refine ⟨pre.domain, pre.arguments, ?_, ?_, contract.returnCanonical, ?_, ?_⟩
  · rw [pre.current.coupled, pre.entry, ← pre.code]
    exact contract.code
  · rw [pre.current.coupled, pre.stack]
    exact contract.stack
  · rw [pre.stack]
    exact contract.stackBound
  · rw [pre.stack]
    exact contract.postStackCanonical

/-- Registration owns spec; this adapter adds no compiler, encoding, cost or
trace restriction. Current resources retain the original code/caller loans,
owner/epoch metadata and complete memory in the same modeled OS world. -/
def readOnlyTask (spec : Spec) : Grading.ReadOnlyTask where
  profile := .sequentialReadOnlyX86CallableV1
  Input := Invocation spec
  pre := Pre spec
  post := Post spec
  useful input := spec.useful input.value
  Resource := Resources spec
  input := resourceInput
  resourcePre := ResourcePre spec
  current resource := CallResources.Current resource.call resource.shared
  permission resource _ := CallResources.ReadAllowed resource.call resource.shared

/-- Only the original STACK8 loan supplies operand authority. Equal bytes at
another address, a replacement RSP or a DATA read do not gain permission. -/
theorem ResourcePre.read_permission {spec bytes resource initial}
    (pre : ResourcePre spec bytes resource initial) {read : Read}
    (allowed : RawRead initial read) :
    CallResources.ReadAllowed resource.call resource.shared read := by
  have same : read = ⟨.stack, resource.call.stack, 8⟩ := by
    cases read with
    | mk kind address bytes =>
      change kind = .stack ∧ address = initial.registers .rsp ∧ bytes = 8 at allowed
      rcases allowed with ⟨rfl, addressEq, rfl⟩
      rw [addressEq, pre.stack]
  rw [same]
  exact CallResources.stackRead_permission pre.current.contract

/-- Bridge raw correctness/policy to resource correctness once. Whole-memory
equality transports present authority at every actual prefix and real return;
no callback predicting a successful run is part of admission. -/
theorem semantics_of_raw {spec : Spec} {bytes : List Byte}
    (raw : ∀ input initial, Pre spec bytes input initial →
      AllExecutions initial (fun result => Post spec input initial result.state) ∧
        RawPolicy initial) :
    Grading.ReadOnlySemanticClaim (readOnlyTask spec) bytes := by
  constructor
  · intro input initial pre
    obtain ⟨executions, policy⟩ := raw input initial pre
    exact ⟨executions, policy.mono (by intros; trivial) (by intros; trivial)⟩
  · intro resource initial pre
    obtain ⟨executions, policy⟩ := raw (resourceInput resource) initial pre.machine
    refine ⟨?_, policy.mono ?_ ?_⟩
    · intro choices
      obtain ⟨result, execution, post⟩ := executions choices
      exact ⟨result, execution, post, pre.current.sameMemory post.memory⟩
    · intro before memory
      exact pre.current.sameMemory memory
    · intro before read allowed
      exact pre.read_permission allowed

/-- Useful raw and current-resource witnesses from present resources alone.
The trusted spec's usefulness is reviewed independently; no result, decode or
execution premise is needed to establish either inhabited domain. -/
theorem nonvacuous_of_resource {spec : Spec} {bytes : List Byte}
    (resource : Resources spec) (initial : State)
    (useful : spec.useful resource.value)
    (pre : ResourcePre spec bytes resource initial) :
    Grading.ReadOnlyNonvacuous (readOnlyTask spec) bytes :=
  ⟨⟨resourceInput resource, initial, useful, pre.machine⟩,
    ⟨resource, initial, useful, pre⟩⟩

end EDSL.PureCall
