/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Logical64.Contract
import EDSL.Grading.ReadOnlyTask

set_option warningAsError true

namespace EDSL.Logical64
open X86 X86.Sequential OS

structure Resources where
  shared : Borrowing.State
  call : CallResources.Call
  left : Word
  right : Word

def resourceInput (resource : Resources) : Input :=
  ⟨resource.left,resource.right,resource.call.returnAddress⟩

structure ResourcePre (bytes : List Byte) (resource : Resources) (initial : State) : Prop where
  current : CallResources.Current resource.call resource.shared initial
  code : resource.call.bytes = bytes
  entry : initial.rip = resource.call.code
  stack : initial.registers .rsp = resource.call.stack
  left : initial.registers .rdi = resource.left
  right : initial.registers .rsi = resource.right

theorem ResourcePre.machine {bytes resource initial} (pre : ResourcePre bytes resource initial) :
    Pre bytes (resourceInput resource) initial := by
  have contract := pre.current.contract
  refine ⟨?_,pre.left,pre.right,?_,contract.returnCanonical,?_,?_⟩
  · rw [pre.current.coupled,pre.entry,← pre.code]
    exact contract.code
  · rw [pre.current.coupled,pre.stack]
    exact contract.stack
  · rw [pre.stack]
    exact contract.stackBound
  · rw [pre.stack]
    exact contract.postStackCanonical

/-- Independent bit-set results and present code/caller resources are fixed.
No compiler, opcode, CFG, trace ordering or instruction budget is required. -/
def readOnlyTask (operation : Operation) : Grading.ReadOnlyTask where
  profile := .sequentialReadOnlyX86CallableV1
  Input := Input
  pre := Pre
  post := Post operation
  useful := Useful
  Resource := Resources
  input := resourceInput
  resourcePre := ResourcePre
  current resource := CallResources.Current resource.call resource.shared
  permission resource _ := CallResources.ReadAllowed resource.call resource.shared

theorem ResourcePre.read_permission {bytes resource initial} (pre : ResourcePre bytes resource initial)
    {read : Read} (allowed : read.kind = .stack ∧
      read.address = initial.registers .rsp ∧ read.bytes = 8) :
    CallResources.ReadAllowed resource.call resource.shared read := by
  have same : read = ⟨.stack,resource.call.stack,8⟩ := by
    cases read with
    | mk kind address bytes =>
      simp only at allowed
      rcases allowed with ⟨rfl,addressEq,rfl⟩
      rw [addressEq,pre.stack]
  rw [same]
  exact CallResources.stackRead_permission pre.current.contract

/-- Proved raw execution and reachable-prefix policies retain the complete
current borrowing world, owner/epoch metadata, permissions and original loans.
These are consequences of correctness, not future-success admission oracles. -/
theorem readOnly_semantics_of_raw {operation : Operation} {bytes : List Byte}
    (raw : ∀ input initial, Pre bytes input initial →
      AllExecutions initial (fun result => Post operation input initial result.state) ∧ RawPolicy initial) :
    Grading.ReadOnlySemanticClaim (readOnlyTask operation) bytes := by
  constructor
  · intro input initial pre
    obtain ⟨executions,policy⟩ := raw input initial pre
    exact ⟨executions,policy.mono (by intros; trivial) (by intros; trivial)⟩
  · intro resource initial pre
    obtain ⟨executions,policy⟩ := raw (resourceInput resource) initial pre.machine
    refine ⟨?_,policy.mono ?_ ?_⟩
    · intro choices
      obtain ⟨result,execution,post⟩ := executions choices
      exact ⟨result,execution,post,pre.current.sameMemory post.memory⟩
    · intro before memory
      exact pre.current.sameMemory memory
    · intro before read allowed
      exact pre.read_permission allowed

end EDSL.Logical64
