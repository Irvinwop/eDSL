/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ReadOnlyTask
import EDSL.Grading.Write32.Resources

namespace EDSL.Grading
open X86 X86.Sequential

/-- A registration-owned extension of the original task shape. The resource
return predicate can refer to the actual Result and initial state, allowing
a mutable task to demand the returned lifted history instead of existentially
choosing a fresh final OS world. Only registration supplies these hooks.
Candidate bytes and proof terms never select Task, policy, or expected type. -/
structure Task where
  profile : Profile
  Input : Type
  pre : List Byte → Input → State → Prop
  post : Input → State → State → Prop
  useful : Input → Prop
  Resource : Type
  input : Resource → Input
  resourcePre : List Byte → Resource → State → Prop
  machinePolicy : List Byte → Input → State → Prop
  resourcePolicy : List Byte → Resource → State → Prop
  resourceReturn : List Byte → Resource → State → Result → Prop

/-- Total functional correctness plus independent raw and current-resource
trace policies. No policy appears in either admission predicate. The
registered return hook retains the resource witness from the actual trace. -/
structure SemanticClaim (task : Task) (bytes : List Byte) : Prop where
  machine : ∀ input initial, task.pre bytes input initial →
    AllExecutions initial (fun result => task.post input initial result.state) ∧
      task.machinePolicy bytes input initial
  resource : ∀ resource initial, task.resourcePre bytes resource initial →
    AllExecutions initial (fun result =>
      task.post (task.input resource) initial result.state ∧
        task.resourceReturn bytes resource initial result) ∧
      task.resourcePolicy bytes resource initial

structure Nonvacuous (task : Task) (bytes : List Byte) : Prop where
  machine : ∃ input initial, task.useful input ∧ task.pre bytes input initial
  resource : ∃ resource initial, task.useful (task.input resource) ∧ task.resourcePre bytes resource initial

/-- Exact legacy adapter: every-prefix current authority, operand read
permission, decoded read-only effects and terminal admission are unchanged. -/
def ofReadOnly (old : ReadOnlyTask) : Task where
  profile := .sequentialReadOnlyX86CallableV1
  Input := old.Input
  pre := old.pre
  post := old.post
  useful := old.useful
  Resource := old.Resource
  input := old.input
  resourcePre := old.resourcePre
  machinePolicy _ _ initial := Grading.ReadOnlyPolicy initial (fun _ => True) (fun _ _ => True)
  resourcePolicy _ resource initial :=
    Grading.ReadOnlyPolicy initial (old.current resource) (old.permission resource)
  resourceReturn _ resource _ result := old.current resource result.state

theorem old_semanticClaim_iff (old : ReadOnlyTask) (bytes : List Byte) :
    SemanticClaim (ofReadOnly old) bytes ↔ ReadOnlySemanticClaim old bytes := by
  constructor
  · intro claim
    exact ⟨claim.machine, claim.resource⟩
  · intro claim
    exact ⟨claim.machine, claim.resource⟩

theorem old_nonvacuous_iff (old : ReadOnlyTask) (bytes : List Byte) :
    Nonvacuous (ofReadOnly old) bytes ↔ ReadOnlyNonvacuous old bytes := by
  constructor
  · intro claim
    exact ⟨claim.machine, claim.resource⟩
  · intro claim
    exact ⟨claim.machine, claim.resource⟩

/-- Full equivalence, including separate useful raw/current-domain evidence.
This preserves every old contract without adding a premise to pair/stride. -/
theorem old_claim_iff (old : ReadOnlyTask) (bytes : List Byte) :
    (SemanticClaim (ofReadOnly old) bytes ∧ Nonvacuous (ofReadOnly old) bytes) ↔
      (ReadOnlySemanticClaim old bytes ∧ ReadOnlyNonvacuous old bytes) := by
  exact and_congr (old_semanticClaim_iff old bytes) (old_nonvacuous_iff old bytes)


/-- Existing registered tasks retain their complete read-only contracts. -/
def pairTask : Task := ofReadOnly pairReadOnlyTask

def strideTask : Task := ofReadOnly strideReadOnlyTask

/-- A fixed mathematical four-byte store with current owned-resource effects.
The task fixes policies; a submission supplies only code and checked proof data. -/
def writeTask : Task where
  profile := .sequentialOwnedWord32X86CallableV1
  Input := Write32.Input
  pre := Write32.Pre
  post := Write32.Post
  useful := Write32.Useful
  Resource := Write32.Resources
  input := Write32.resourceInput
  resourcePre := Write32.ResourcePre
  machinePolicy := Write32.RawPolicy
  resourcePolicy _ := Write32.ResourcePolicy
  resourceReturn _ := Write32.ResourceReturn

inductive TaskID where
  | pair32 | stride32 | write32
  deriving DecidableEq, Repr

def registered : TaskID → Task
  | .pair32 => pairTask
  | .stride32 => strideTask
  | .write32 => writeTask

/-- The trusted task ID and literal artifact bytes determine this type. -/
def Claim (id : TaskID) (bytes : List Byte) : Prop :=
  SemanticClaim (registered id) bytes ∧ Nonvacuous (registered id) bytes

/-- Policy generalization does not weaken either published legacy claim. -/
theorem pair_claim_iff (bytes : List Byte) :
    Claim .pair32 bytes ↔
      (ReadOnlySemanticClaim pairReadOnlyTask bytes ∧ ReadOnlyNonvacuous pairReadOnlyTask bytes) :=
  old_claim_iff pairReadOnlyTask bytes

theorem stride_claim_iff (bytes : List Byte) :
    Claim .stride32 bytes ↔
      (ReadOnlySemanticClaim strideReadOnlyTask bytes ∧ ReadOnlyNonvacuous strideReadOnlyTask bytes) :=
  old_claim_iff strideReadOnlyTask bytes

end EDSL.Grading
