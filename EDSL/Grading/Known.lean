/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Task
import EDSL.Grading.Domain
import EDSL.Grading.Write32.Domain
import EDSL.Grading.Write32.Correctness
import EDSL.Pair32.Correctness
import EDSL.Stride32.Correctness
import EDSL.StoreReturn32.Resources

namespace EDSL.Grading
open X86 X86.Sequential

/-- Independently constructed current inputs inhabit all registered domains
for every admitted selected byte span, including unsupported instructions.
The positive bound is needed for the OS code loan; it is not a machine
precondition or a decoder-validity assumption. No execution proof is used. -/
theorem domain_nonvacuous (id : TaskID) (bytes : List Byte)
    (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096) :
    Nonvacuous (registered id) bytes := by
  cases id with
  | pair32 =>
    let witness := Domain.pair bytes positive bound
    let resource : PairResources := ⟨witness.shared, witness.callA, witness.callB⟩
    have pre : PairResourcePre bytes resource witness.initial :=
      ⟨witness.code, witness.admitted, witness.entry, witness.stack,
        witness.baseA, witness.countA, witness.baseB, witness.countB⟩
    have useful : pairTask.useful (pairTask.input resource) := ⟨witness.usefulA, witness.usefulB⟩
    exact ⟨⟨pairTask.input resource, witness.initial, useful, pre.machine⟩,
      ⟨resource, witness.initial, useful, pre⟩⟩
  | stride32 =>
    let witness := Domain.stride bytes positive bound
    let resource : StrideResources := ⟨witness.shared, witness.call, witness.count⟩
    have pre : StrideResourcePre bytes resource witness.initial :=
      ⟨witness.code, witness.admitted, witness.entry, witness.stack,
        witness.base, witness.length, witness.counter⟩
    have useful : strideTask.useful (strideTask.input resource) := witness.useful
    exact ⟨⟨strideTask.input resource, witness.initial, useful, pre.machine⟩,
      ⟨resource, witness.initial, useful, pre⟩⟩
  | write32 | storeReturn32 =>
    let witness := Write32.Domain.candidate bytes positive bound
    let resource : Write32.Resources :=
      ⟨witness.shared, witness.call, witness.initial.registers .rsi, witness.oldValue⟩
    have pre : Write32.ResourcePre bytes resource witness.initial :=
      ⟨witness.current, witness.raw.codeBytes, witness.raw.entry, witness.raw.stackPointer,
        witness.raw.targetPointer, rfl, witness.raw.old⟩
    have useful : writeTask.useful (writeTask.input resource) := witness.raw.useful
    exact ⟨⟨writeTask.input resource, witness.initial, useful, pre.machine⟩,
      ⟨resource, witness.initial, useful, pre⟩⟩

/-- All admitted pair inputs and all AF streams satisfy the fixed semantic
contract. Graph validity is separately proved evidence used by the adapters. -/
theorem pair_semantics : SemanticClaim pairTask Pair32.bytes := by
  constructor
  · intro input initial pre
    let annotation := Pair32.annotations pre (fun _ => True) (by intros; trivial)
    constructor
    · intro choices
      obtain ⟨result, execution, post, _⟩ := annotation.execution Pair32.valid (.entry pre) choices
      exact ⟨result, execution, post⟩
    · exact (annotations_policy annotation Pair32.valid (.entry pre)
        (fun _ => True) (by intros; trivial)).mono
          (by intros; trivial) (by intros; trivial)
  · intro resource initial pre
    have machinePre := pre.machine
    let annotation := Pair32.annotations machinePre
      (OS.ArrayResources.ReadPermission resource.shared resource.callA.worker)
      (fun read member => Pair32.operandReads_permission pre.admitted pre.baseA pre.baseB pre.stack member)
    constructor
    · intro choices
      obtain ⟨result, execution, post, _⟩ := annotation.execution Pair32.valid (.entry machinePre) choices
      exact ⟨result, execution, post, pre.admitted.unchangedMemory post.memory⟩
    · exact (annotations_policy annotation Pair32.valid (.entry machinePre)
        (pairReadOnlyTask.current resource) (by
          intro source budget node before inside
          exact pre.admitted.unchangedMemory inside.memory)).mono
            (fun _ current => current) (fun _ _ allowed => allowed.1)

/-- The stride contract covers every admitted logical array and count, while
retaining current contiguous-array authority and the complete return slot. -/
theorem stride_semantics : SemanticClaim strideTask Stride32.bytes := by
  constructor
  · intro input initial pre
    let annotation := Stride32.annotations pre (fun _ => True) (by intros; trivial)
    constructor
    · intro choices
      obtain ⟨result, execution, post, _⟩ := annotation.execution Stride32.valid (.entry pre) choices
      exact ⟨result, execution, post⟩
    · exact (annotations_policy annotation Stride32.valid (.entry pre)
        (fun _ => True) (by intros; trivial)).mono
          (by intros; trivial) (by intros; trivial)
  · intro resource initial pre
    have machinePre := pre.machine
    let annotation := Stride32.annotations machinePre
      (OS.ArrayResources.ReadPermission resource.shared resource.call.worker)
      (fun read member => Stride32.operandReads_permission pre.admitted pre.length pre.base pre.stack member)
    constructor
    · intro choices
      obtain ⟨result, execution, post, _⟩ := annotation.execution Stride32.valid (.entry machinePre) choices
      exact ⟨result, execution, post, pre.admitted.unchangedMemory post.memory⟩
    · exact (annotations_policy annotation Stride32.valid (.entry machinePre)
        (strideReadOnlyTask.current resource) (by
          intro source budget node before inside
          exact pre.admitted.unchangedMemory inside.memory)).mono
            (fun _ current => current) (fun _ _ allowed => allowed.1)

/-- All raw arguments and current owned-resource inputs satisfy the same
independent store specification, including every actual-prefix OS effect. -/
theorem write_semantics : SemanticClaim writeTask Write32.bytes :=
  ⟨fun _ _ pre => Write32.raw_semantics pre,
    fun _ _ pre => Write32.resource_semantics pre⟩

/-- The registered pointer result follows from actual machine execution and
current-resource effects for each production shape. Accounting stays separate
from the registered mathematical task and its unchanged input domains. -/
theorem storeReturn_semantics (shape : StoreReturn32.Shape) :
    SemanticClaim storeReturnTask shape.bytes := by
  constructor
  · intro input initial pre
    have semantics := StoreReturn32.raw_semantics pre
    refine ⟨?_, semantics.2⟩
    intro choices
    obtain ⟨result, execution, contract⟩ := semantics.1 choices
    exact ⟨result, execution, contract.1⟩
  · intro resource initial pre
    have semantics := StoreReturn32.resource_semantics pre
    refine ⟨?_, semantics.2⟩
    intro choices
    obtain ⟨result, execution, contract, returned⟩ := semantics.1 choices
    exact ⟨result, execution, contract.1, returned⟩

namespace Known

/-- Full claim for the published pair bytes, combining universal semantic
correctness with independent useful machine and current-resource witnesses. -/
theorem pair : Claim .pair32 Pair32.bytes :=
  ⟨pair_semantics, domain_nonvacuous .pair32 Pair32.bytes (by decide) (by decide)⟩

/-- Full claim for the published stride bytes, under the same callable profile. -/
theorem stride : Claim .stride32 Stride32.bytes :=
  ⟨stride_semantics, domain_nonvacuous .stride32 Stride32.bytes (by decide) (by decide)⟩

/-- Full mutable task claim, with useful decoder-independent current inputs. -/
theorem write : Claim .write32 Write32.bytes :=
  ⟨write_semantics, domain_nonvacuous .write32 Write32.bytes (by decide) (by decide)⟩

/-- Each exact production shape proves the distinct registered task on its
full raw/current-resource domains, without changing the void-store task. -/
theorem storeReturn (shape : StoreReturn32.Shape) : Claim .storeReturn32 shape.bytes :=
  ⟨storeReturn_semantics shape, domain_nonvacuous .storeReturn32 shape.bytes
    (by cases shape <;> decide) (by cases shape <;> decide)⟩

/-- Closed export target for the store-before-copy compiler ordering. -/
theorem storeReturnStoreCopy : Claim .storeReturn32 StoreReturn32.Shape.storeCopy.bytes :=
  storeReturn .storeCopy

/-- Closed export target for the copy-before-store compiler ordering. -/
theorem storeReturnCopyStore : Claim .storeReturn32 StoreReturn32.Shape.copyStore.bytes :=
  storeReturn .copyStore

/-- Closed export target for the copied-pointer assembly store. -/
theorem storeReturnCopyStoreRax : Claim .storeReturn32 StoreReturn32.Shape.copyStoreRax.bytes :=
  storeReturn .copyStoreRax

end Known

end EDSL.Grading
