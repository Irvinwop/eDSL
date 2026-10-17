/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ArrayMaximum64.Contract
import EDSL.OS.ArrayResources64
import EDSL.Grading.ReadOnlyTask

set_option warningAsError true

namespace EDSL.ArrayMaximum64
open X86 X86.Sequential OS

structure Resources where
  shared : Borrowing.State
  call : ArrayResources64.Call

def resourceInput (resource : Resources) : Input :=
  ⟨resource.call.values,resource.call.returnAddress⟩

structure ResourcePre (bytes : List Byte) (resource : Resources) (initial : State) : Prop where
  current : ArrayResources64.Current resource.call resource.shared initial
  code : resource.call.bytes = bytes
  entry : initial.rip = resource.call.code
  stack : initial.registers .rsp = resource.call.stack
  base : initial.registers .rdi = resource.call.base
  count : initial.registers .rsi = BitVec.ofNat 64 resource.call.values.length

theorem ResourcePre.machine {bytes resource initial} (pre : ResourcePre bytes resource initial) :
    Pre bytes initial (resourceInput resource).values (resourceInput resource).target := by
  have contract := pre.current.contract
  refine ⟨?_,?_,?_,pre.count,?_,contract.pureCall.returnCanonical,?_,?_⟩
  · rw [pre.current.coupled,pre.entry,← pre.code]
    exact contract.pureCall.code
  · rw [pre.current.coupled,pre.base]
    exact contract.array
  · rw [pre.base]
    exact contract.bound
  · rw [pre.current.coupled,pre.stack]
    exact contract.pureCall.stack
  · rw [pre.stack]
    exact contract.pureCall.stackBound
  · rw [pre.stack]
    exact contract.pureCall.postStackCanonical

/-- A useful witness requires a nonzero mathematical result. This is separate
from admission: empty lists, zero-only lists and equal values remain admitted. -/
def Useful (input : Input) : Prop := 0 < maximumNat input.values

/-- Registration fixes the independent result and current-resource policies.
It fixes no compiler, loop shape, instruction count or operand-read order.
Every resource read must fit a current authorized worker loan. -/
def readOnlyTask : Grading.ReadOnlyTask where
  profile := .sequentialReadOnlyX86CallableV1
  Input := Input
  pre bytes input initial := Pre bytes initial input.values input.target
  post input initial final := Post initial input.values input.target final
  useful := Useful
  Resource := Resources
  input := resourceInput
  resourcePre := ResourcePre
  current resource := ArrayResources64.Current resource.call resource.shared
  permission resource _ := ArrayResources.ReadPermission resource.shared resource.call.worker

theorem ResourcePre.read_permission {bytes resource initial} (pre : ResourcePre bytes resource initial)
    {read : Read} (allowed : ReadAllowed initial resource.call.values read) :
    ArrayResources.ReadPermission resource.shared resource.call.worker read := by
  rcases allowed with data | stack
  · obtain ⟨kind,width,index,inside,address⟩ := data
    apply ArrayResources64.arrayRead_permission pre.current.contract
    exact ⟨kind,width,index,inside,by simpa only [pre.base] using address⟩
  · have same : read = ⟨.stack,resource.call.stack,8⟩ := by
      cases read with
      | mk kind address bytes =>
        rcases stack with ⟨rfl,addressEq,rfl⟩
        change address = initial.registers .rsp at addressEq
        rw [addressEq,pre.stack]
    rw [same]
    exact ArrayResources64.stackRead_permission pre.current.contract

/-- Exact full RAM equality transports the same coherent OS world at every
actual prefix and return. Resource admission contains no execution callback. -/
theorem readOnly_semantics_of_raw {bytes : List Byte}
    (raw : ∀ initial values target, Pre bytes initial values target →
      AllExecutions initial (fun result => Post initial values target result.state) ∧
        RawPolicy initial values) :
    Grading.ReadOnlySemanticClaim readOnlyTask bytes := by
  constructor
  · intro input initial pre
    obtain ⟨executions,policy⟩ := raw initial input.values input.target pre
    exact ⟨executions,policy.mono (by intros; trivial) (by intros; trivial)⟩
  · intro resource initial pre
    obtain ⟨executions,policy⟩ := raw initial resource.call.values resource.call.returnAddress pre.machine
    refine ⟨?_,policy.mono ?_ ?_⟩
    · intro choices
      obtain ⟨result,execution,post⟩ := executions choices
      exact ⟨result,execution,post,pre.current.sameMemory post.memory⟩
    · intro before memory
      exact pre.current.sameMemory memory
    · intro before read allowed
      exact pre.read_permission allowed

end EDSL.ArrayMaximum64
