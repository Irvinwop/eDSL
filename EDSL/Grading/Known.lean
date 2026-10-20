/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Task
import EDSL.PureCall.Candidate
import EDSL.Comparison64.Domain
import EDSL.Logical64.Domain
import EDSL.ArrayMaximum64.Domain
import EDSL.ArraySum64.Domain
import EDSL.Grading.Domain
import EDSL.Grading.Write32.Domain
import EDSL.Grading.Write32.Correctness
import EDSL.Pair32.Correctness
import EDSL.Stride32.Correctness
import EDSL.StoreReturn32.Resources
import EDSL.Grading.StoreReturnValue64.Domain
import EDSL.Grading.StoreReturnValue64.Correctness
import EDSL.CountedStore64.Domain
import EDSL.CountedStore64.Proof
import EDSL.CountedStore64.Clang.Proof

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
  | storeReturnValue64 =>
    let witness := StoreReturnValue64.Domain.candidate bytes positive bound
    exact ⟨⟨StoreReturnValue64.resourceInput witness.resource, witness.initial,
      witness.useful, witness.pre.machine⟩,
      ⟨witness.resource, witness.initial, witness.useful, witness.pre⟩⟩
  | countedStore64 =>
    let witness := CountedStore64.Domain.candidate bytes positive bound
    exact ⟨⟨CountedStore64.resourceInput witness.resource, witness.initial,
      witness.useful, witness.pre.machine⟩,
      ⟨witness.resource, witness.initial, witness.useful, witness.pre⟩⟩
  | maximum64 =>
    exact (old_nonvacuous_iff _ _).mpr
      (Comparison64.Domain.nonvacuous .unsignedMaximum bytes positive bound)
  | minimum64 =>
    exact (old_nonvacuous_iff _ _).mpr
      (Comparison64.Domain.nonvacuous .unsignedMinimum bytes positive bound)
  | signedMaximum64 =>
    exact (old_nonvacuous_iff _ _).mpr
      (Comparison64.Domain.nonvacuous .signedMaximum bytes positive bound)
  | arrayMaximum64 =>
    exact (old_nonvacuous_iff _ _).mpr
      (ArrayMaximum64.Domain.nonvacuous bytes positive bound)
  | arraySum64 =>
    exact (old_nonvacuous_iff _ _).mpr
      (ArraySum64.Domain.nonvacuous bytes positive bound)

  | intersection64 =>
    exact (old_nonvacuous_iff _ _).mpr
      (Logical64.Domain.nonvacuous .intersection bytes positive bound)
  | union64 =>
    exact (old_nonvacuous_iff _ _).mpr
      (Logical64.Domain.nonvacuous .union bytes positive bound)
  | symmetricDifference64 =>
    exact (old_nonvacuous_iff _ _).mpr
      (Logical64.Domain.nonvacuous .symmetricDifference bytes positive bound)
  | addModulo64 =>
    let resource : PureCall.Resources Arithmetic64.addition :=
      ⟨Domain.shared bytes, Comparison64.Domain.call bytes, (0xffffffffffffffff, 1)⟩
    let initial := Comparison64.Domain.initial bytes 0xffffffffffffffff 1
    have pre : PureCall.ResourcePre Arithmetic64.addition bytes resource initial :=
      ⟨⟨Comparison64.Domain.contract bytes positive bound, rfl⟩, rfl, rfl, rfl,
        trivial, (Arithmetic64.bound_iff _ _).mpr ⟨rfl, rfl⟩⟩
    have useful : Arithmetic64.addition.useful resource.value := by
      change (0xffffffffffffffff : Word) ≠ 0 ∧ (1 : Word) ≠ 0
      exact ⟨by decide +kernel, by decide +kernel⟩
    exact (old_nonvacuous_iff _ _).mpr
      (PureCall.nonvacuous_of_resource resource initial useful pre)
  | clampSigned32 =>
    let value : Scalar32.ClampInput := ⟨0, 0xffffffff, 1⟩
    let resource : PureCall.Resources Scalar32.clampSigned :=
      ⟨Domain.shared bytes, Comparison64.Domain.call bytes, value⟩
    let initial := Comparison64.Domain.initial bytes 0 0xffffffff
      (fun register => if register = .rdx then 1 else 0)
    have pre : PureCall.ResourcePre Scalar32.clampSigned bytes resource initial :=
      ⟨⟨Comparison64.Domain.contract bytes positive bound, rfl⟩, rfl, rfl, rfl,
        by
          change (0xffffffff : BitVec 32).toInt ≤ (1 : BitVec 32).toInt
          decide +kernel,
        (Scalar32.clamp_bound_iff _ _).mpr ⟨rfl, rfl, rfl⟩⟩
    have useful : Scalar32.clampSigned.useful resource.value := by
      change (0xffffffff : BitVec 32).toInt < (0 : BitVec 32).toInt ∧
        (0 : BitVec 32).toInt < (1 : BitVec 32).toInt
      decide +kernel
    exact (old_nonvacuous_iff _ _).mpr
      (PureCall.nonvacuous_of_resource resource initial useful pre)

  | absSigned32 =>
    let resource : PureCall.Resources Scalar32.absoluteSigned :=
      ⟨Domain.shared bytes, Comparison64.Domain.call bytes, (0xffffffff : BitVec 32)⟩
    let initial := Comparison64.Domain.initial bytes 0xffffffff 0
    have pre : PureCall.ResourcePre Scalar32.absoluteSigned bytes resource initial :=
      ⟨⟨Comparison64.Domain.contract bytes positive bound, rfl⟩, rfl, rfl, rfl,
        by
          change (0xffffffff : BitVec 32).toInt ≠ -2147483648
          decide +kernel,
        (Scalar32.absolute_bound_iff _ _).mpr rfl⟩
    have useful : Scalar32.absoluteSigned.useful resource.value := by
      change (0xffffffff : BitVec 32).toInt < 0
      decide +kernel
    exact (old_nonvacuous_iff _ _).mpr
      (PureCall.nonvacuous_of_resource resource initial useful pre)

  | byteSwap64 =>
    let resource : PureCall.Resources Arithmetic64.byteSwap :=
      ⟨Domain.shared bytes, Comparison64.Domain.call bytes, (1 : Word)⟩
    let initial := Comparison64.Domain.initial bytes 1 0
    have pre : PureCall.ResourcePre Arithmetic64.byteSwap bytes resource initial :=
      ⟨⟨Comparison64.Domain.contract bytes positive bound, rfl⟩, rfl, rfl, rfl,
        trivial, (Arithmetic64.byteSwap_bound_iff _ _).mpr rfl⟩
    have useful : Arithmetic64.byteSwap.useful resource.value := by
      change WordMath.base256Digit (1 : Word).toNat 0 ≠ 0 ∧
        WordMath.base256Digit (1 : Word).toNat 7 = 0
      decide +kernel
    exact (old_nonvacuous_iff _ _).mpr
      (PureCall.nonvacuous_of_resource resource initial useful pre)

  | populationCount64 =>
    let resource : PureCall.Resources Arithmetic64.populationCount :=
      ⟨Domain.shared bytes, Comparison64.Domain.call bytes, (0x81 : Word)⟩
    let initial := Comparison64.Domain.initial bytes 0x81 0
    have pre : PureCall.ResourcePre Arithmetic64.populationCount bytes resource initial :=
      ⟨⟨Comparison64.Domain.contract bytes positive bound, rfl⟩, rfl, rfl, rfl,
        trivial, (Arithmetic64.populationCount_bound_iff _ _).mpr rfl⟩
    have useful : Arithmetic64.populationCount.useful resource.value :=
      Arithmetic64.populationCount_useful_asymmetric
    exact (old_nonvacuous_iff _ _).mpr
      (PureCall.nonvacuous_of_resource resource initial useful pre)

  | average64 =>
    exact (old_nonvacuous_iff _ _).mpr
      (PureCall.Candidate.nonvacuous Arithmetic64.average
        (0xffffffffffffffff, 0xfffffffffffffffd) trivial
        Arithmetic64.average_useful_overflow_asymmetric bytes positive bound)

  | parity64 =>
    exact (old_nonvacuous_iff _ _).mpr
      (PureCall.Candidate.nonvacuous Arithmetic64.parity64
        (0x8000000000000001 : Word) trivial Arithmetic64.parity64_useful_separated
        bytes positive bound)

  | rotateLeft64 =>
    exact (old_nonvacuous_iff _ _).mpr
      (PureCall.Candidate.nonvacuous Arithmetic64.rotateLeft
        ((0x8123456789abcdef, 4) : Word × BitVec 32) trivial
        Arithmetic64.rotateLeft_useful_wraparound bytes positive bound)

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

/-- The strict store/load program also satisfies the independent ordinary
full64 task. Its exact accounting is not part of this registered claim. -/
theorem storeReturnValue64_semantics :
    SemanticClaim storeReturnValue64Task StoreLoad64.bytes :=
  ⟨fun _ _ pre => StoreReturnValue64.raw_semantics pre,
    fun _ _ pre => StoreReturnValue64.resource_semantics pre⟩

/-- Both compiler loops satisfy the same registered mathematical contract.
Their instruction budgets are separate accounting, never part of acceptance. -/
theorem countedStore64_gcc_semantics :
    SemanticClaim countedStore64Task CountedStore64.GCC.bytes := by
  constructor
  · intro input initial pre
    refine ⟨?_, CountedStore64.GCC.raw_policy pre⟩
    intro choices
    obtain ⟨result, actual, post, _⟩ := CountedStore64.GCC.raw_semantics pre choices
    exact ⟨result, actual, post⟩
  · intro resource initial pre
    have semantics := CountedStore64.GCC.resource_semantics pre
    refine ⟨?_, semantics.2⟩
    intro choices
    obtain ⟨result, actual, post, returned, _⟩ := semantics.1 choices
    exact ⟨result, actual, post, returned⟩

theorem countedStore64_clang_semantics :
    SemanticClaim countedStore64Task CountedStore64.Clang.bytes := by
  constructor
  · intro input initial pre
    refine ⟨?_, CountedStore64.Clang.raw_policy pre⟩
    intro choices
    obtain ⟨result, actual, post, _⟩ := CountedStore64.Clang.raw_semantics pre choices
    exact ⟨result, actual, post⟩
  · intro resource initial pre
    have semantics := CountedStore64.Clang.resource_semantics pre
    refine ⟨?_, semantics.2⟩
    intro choices
    obtain ⟨result, actual, post, returned, _⟩ := semantics.1 choices
    exact ⟨result, actual, post, returned⟩

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

/-- Closed full64 value-return claim with independently constructed useful
raw and current-resource inputs. -/
theorem storeReturnValue64 : Claim .storeReturnValue64 StoreLoad64.bytes :=
  ⟨storeReturnValue64_semantics,
    domain_nonvacuous .storeReturnValue64 StoreLoad64.bytes (by decide) (by decide)⟩

theorem countedStore64GCC : Claim .countedStore64 CountedStore64.GCC.bytes :=
  ⟨countedStore64_gcc_semantics,
    domain_nonvacuous .countedStore64 CountedStore64.GCC.bytes (by decide) (by decide)⟩

theorem countedStore64Clang : Claim .countedStore64 CountedStore64.Clang.bytes :=
  ⟨countedStore64_clang_semantics,
    domain_nonvacuous .countedStore64 CountedStore64.Clang.bytes (by decide) (by decide)⟩

end Known

end EDSL.Grading
