/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.GradingStoreReturnValue64
open EDSL X86 X86.Sequential OS Grading
open Grading.StoreReturnValue64

/-- Unsupported bytes retain useful raw and current-resource inputs. -/
theorem unsupported_domain : Nonvacuous (registered .storeReturnValue64) [0xff] :=
  domain_nonvacuous .storeReturnValue64 [0xff] (by decide) (by decide)

/-- The inhabited unsupported domain fails actual execution; this is not
proof rejection being mistaken for evidence of a semantic failure. -/
theorem unsupported_not_claim : ¬Claim .storeReturnValue64 [0xff] := by
  intro claim
  let witness := StoreReturnValue64.Domain.unsupported
  have total := (claim.1.machine (resourceInput witness.resource)
    witness.initial witness.pre.machine).1
  have decoded : Sequential.decodeAt witness.initial = .error (.unsupportedOpcode 0xff) :=
    StoreReturnValue64.Domain.unsupported_rejected
  have fault : step false witness.initial = .error (.unsupportedOpcode 0xff) := by
    simp only [Sequential.step, decoded, error_bind]
  have impossible := total.no_fault_prefix (fun _ => false)
    (Sequential.run_fault (choices := fun _ => false) (fuel := 0) fault)
  cases impossible

/-- Equal low halves do not make the full64 change useless. The same input
has genuine current owner authority, live loans and complete RAM coupling. -/
theorem upper_half_only_admitted (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    ∃ resource initial, ResourcePre bytes resource initial ∧
      Useful (resourceInput resource) ∧
      (resourceInput resource).oldValue.setWidth 32 = (resourceInput resource).argument.setWidth 32 := by
  let witness := StoreReturnValue64.Domain.upperOnly bytes positive bound
  refine ⟨witness.resource, witness.initial, witness.pre, witness.useful, ?_⟩
  change (0 : Word).setWidth 32 = (0x100000000 : Word).setWidth 32
  decide

/-- Useful witnesses do not narrow universal admission: unchanged values,
arbitrary volatile register contents and arbitrary flags remain admitted. -/
theorem unchanged_value_admitted (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (registers : Register → Word) (flags : Word) :
    ResourcePre bytes (StoreReturnValue64.Domain.resource bytes 0)
      (StoreReturnValue64.Domain.initial bytes 0 registers flags) :=
  StoreReturnValue64.Domain.resource_pre bytes positive bound 0 registers flags

namespace Narrow

-- Owned synthetic candidate: full64 return but only a narrow low32 store.
def bytes : List Byte := [0x48, 0x89, 0xf0, 0x89, 0x37, 0xc3]
def initial : State := StoreReturnValue64.Domain.initial bytes 0x100000000
def resource : Resources := StoreReturnValue64.Domain.resource bytes 0x100000000

theorem admitted : ResourcePre bytes resource initial :=
  StoreReturnValue64.Domain.resource_pre bytes (by decide) (by decide) 0x100000000

def moved : State := { initial.writeRegister .rax 0x100000000 with rip := 4099 }
def stored : State :=
  { moved with memory := writeDWordUnchecked moved.memory 262144 0, rip := 4101 }
def returned : State := { stored.writeRegister .rsp 65552 with rip := 8192 }

theorem move_step (af : Bool) : step af initial = .ok ⟨.next moved, []⟩ := rfl
theorem store_step (af : Bool) : step af moved = .ok ⟨.next stored, []⟩ := rfl
theorem return_step (af : Bool) :
    step af stored = .ok ⟨.returned returned, [⟨.stack, 65544, 8⟩]⟩ := rfl

theorem actual_execution (choices : Choices) :
    Sequential.Executes choices initial ⟨returned, 3, [⟨.stack, 65544, 8⟩]⟩ := by
  have execution := Sequential.Executes.next (choices := choices) (move_step _)
    (Sequential.Executes.next (store_step _) (Sequential.Executes.ret (return_step _)))
  simpa only [Result.prepend, List.nil_append] using execution

/-- The actual trace is permitted by the raw span policy. Rejection below
therefore tests the full64 result obligation, not an invented width ban. -/
theorem raw_policy : RawPolicy bytes (resourceInput resource) initial := by
  refine ⟨fun _ before => before = initial ∨ before = moved ∨ before = stored,
    Or.inl rfl, ?_⟩
  intro shared before inside
  rcases inside with rfl | rfl | rfl
  · refine ⟨trivial, .movReg64 .rax .rsi, rfl, ?_⟩
    intro af
    exact ⟨⟨.next moved, []⟩, (), move_step af, by simp,
      ⟨by change 4096 ≤ 4096 ∧ 4096 + 3 ≤ 4096 + 6; decide,
        .readOnly rfl⟩, Or.inr (Or.inl rfl)⟩
  · refine ⟨trivial, .legacy .storeEsiRdi, rfl, ?_⟩
    intro af
    exact ⟨⟨.next stored, []⟩, (), store_step af, by simp,
      ⟨by change 4096 ≤ 4099 ∧ 4099 + 2 ≤ 4096 + 6; decide,
        .store32 rfl (by change 262144 ≤ 262144 ∧ 262144 + 4 ≤ 262144 + 8; decide)⟩,
      Or.inr (Or.inr rfl)⟩
  · refine ⟨trivial, .legacy .ret, rfl, ?_⟩
    intro af
    refine ⟨⟨.returned returned, [⟨.stack, 65544, 8⟩]⟩, (), return_step af,
      ?_, ⟨by change 4096 ≤ 4101 ∧ 4101 + 1 ≤ 4096 + 6; decide,
        .readOnly rfl⟩, trivial⟩
    intro read member
    simp only [List.mem_singleton] at member
    subst read
    exact ⟨⟨rfl, rfl⟩, rfl, 8192, rfl⟩

/-- Actual modeled execution returns the full64 argument but leaves its
nonzero upper half unwritten. No packet mismatch is used as evidence. -/
theorem actual_wrong_result (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      result.state.registers .rax = 0x100000000 ∧
      loadQWord result.state.memory 262144 = .ok 0 :=
  ⟨⟨returned, 3, [⟨.stack, 65544, 8⟩]⟩, actual_execution choices, rfl, rfl⟩

theorem not_claim : ¬Claim .storeReturnValue64 bytes := by
  intro claim
  obtain ⟨result, execution, _, value⟩ := actual_wrong_result (fun _ => false)
  have post := Sequential.AllExecutions.project
    (claim.1.machine (resourceInput resource) initial admitted.machine).1
    ⟨fun _ => false, execution⟩
  have wrong : (Except.ok (0 : Word) : Except Error Word) = .ok 0x100000000 :=
    value.symm.trans post.value
  exact (by decide : (0 : Word) ≠ 0x100000000) (Except.ok.inj wrong)

end Narrow

namespace Truncated

-- Independent RAX defect: the complete store succeeds, then MOV EAX,ESI
-- zeroes the high half of the result register.
def bytes : List Byte := [0x48, 0x89, 0x37, 0x89, 0xf0, 0xc3]
def initial : State := StoreReturnValue64.Domain.initial bytes 0x100000000
def resource : Resources := StoreReturnValue64.Domain.resource bytes 0x100000000

theorem admitted : ResourcePre bytes resource initial :=
  StoreReturnValue64.Domain.resource_pre bytes (by decide) (by decide) 0x100000000

def stored : State :=
  { initial with memory := writeQWordUnchecked initial.memory 262144 0x100000000, rip := 4099 }
def moved : State := { stored.writeRegister .rax 0 with rip := 4101 }
def returned : State := { moved.writeRegister .rsp 65552 with rip := 8192 }

theorem store_step (af : Bool) : step af initial = .ok ⟨.next stored, []⟩ := rfl
theorem move_step (af : Bool) : step af stored = .ok ⟨.next moved, []⟩ := rfl
theorem return_step (af : Bool) :
    step af moved = .ok ⟨.returned returned, [⟨.stack, 65544, 8⟩]⟩ := rfl

theorem actual_execution (choices : Choices) :
    Sequential.Executes choices initial ⟨returned, 3, [⟨.stack, 65544, 8⟩]⟩ := by
  have execution := Sequential.Executes.next (choices := choices) (store_step _)
    (Sequential.Executes.next (move_step _) (Sequential.Executes.ret (return_step _)))
  simpa only [Result.prepend, List.nil_append] using execution

theorem actual_wrong_result (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      result.state.registers .rax = 0 ∧
      loadQWord result.state.memory 262144 = .ok 0x100000000 :=
  ⟨⟨returned, 3, [⟨.stack, 65544, 8⟩]⟩, actual_execution choices, rfl, rfl⟩

theorem not_claim : ¬Claim .storeReturnValue64 bytes := by
  intro claim
  obtain ⟨result, execution, register, _⟩ := actual_wrong_result (fun _ => false)
  have post := Sequential.AllExecutions.project
    (claim.1.machine (resourceInput resource) initial admitted.machine).1
    ⟨fun _ => false, execution⟩
  have wrong : (0 : Word) = 0x100000000 := register.symm.trans post.result
  exact (by decide : (0 : Word) ≠ 0x100000000) wrong

end Truncated

end EDSL.Tests.GradingStoreReturnValue64

open Lean EDSL EDSL.Grading EDSLGrader EDSLGrader.Runtime

-- Check the real string parser, profile and trusted Expr mapping together.
-- Every existing CLI spelling must still kernel-check its original claim;
-- the new spelling must select the independent full64 mathematical task.
run_cmd do
  let env := (← getEnv).toKernelEnv
  let cases : List (String × List X86.Byte × Name × Grading.Profile) := [
    ("pair32", Pair32.bytes, ``Known.pair, .sequentialReadOnlyX86CallableV1),
    ("stride32", Stride32.bytes, ``Known.stride, .sequentialReadOnlyX86CallableV1),
    ("write32", Grading.Write32.bytes, ``Known.write, .sequentialOwnedWord32X86CallableV1),
    ("storeReturn32", StoreReturn32.Shape.storeCopy.bytes, ``Known.storeReturnStoreCopy,
      .sequentialOwnedWord32X86CallableV1),
    ("storeReturnValue64", StoreLoad64.bytes, ``Known.storeReturnValue64,
      .sequentialOwnedWord64X86CallableV1)]
  for (spelling, bytes, proof, profile) in cases do
    let some id := taskID spelling | throwError "registered task spelling rejected: {spelling}"
    unless (registered id).profile == profile do
      throwError "wrong registered callable profile for {spelling}"
    match checkExpr env {} (expectedClaim id bytes) (mkConst proof)
        `EDSLGrader.Internal.storeReturnValue64RegistryTest with
    | .error failure => throwError "wrong trusted task type for {spelling}: {failure}"
    | .ok _ => pure ()
  for spelling in ["", "unknown", "storeReturn64", "StoreReturnValue64", "storeReturnValue64 "] do
    unless (taskID spelling).isNone do
      throwError "unknown task spelling accepted: {spelling}"
  match checkExpr env {} (expectedClaim .storeReturn32 StoreLoad64.bytes)
      (mkConst ``Known.storeReturnValue64) `EDSLGrader.Internal.storeReturnValue64DistinctTest with
  | .ok _ => throwError "full64 value-return claim was accepted as the old pointer-return task"
  | .error _ => pure ()
  logInfo "All five task spellings, profiles and trusted claim types checked; unknown task spellings rejected"

namespace GradingStoreReturnValue64BudgetTests

/-- Replay a real valid full64 claim against a fresh fixed snapshot under
the unchanged default limits, then require resource failures when each
independent admission budget is exhausted. Both packet dialects are exercised. -/
def checkBudgets : IO Unit := do
  initSearchPath (← findSysroot)
  let trusted ← importModules #[{ module := `EDSL.Grading.Known },
    { module := `EDSL.Grading.Artifact }] {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  let env := trusted.toKernelEnv
  let artifact := Grading.Artifact.raw StoreLoad64.bytes
  let proof := mkConst ``Known.storeReturnValue64
  for (dialect, encoded) in [("v1", encodeTreePacket [] proof), ("v2", encodePacket [] proof)] do
    let packet ← match encoded with
      | .ok packet => pure packet
      | .error failure => throw (IO.userError s!"valid {dialect} packet encoding failed: {failure}")
    let accepted ← match grade env {} .storeReturnValue64 artifact packet with
      | .ok accepted => pure accepted
      | .error failure => throw (IO.userError s!"default {dialect} full64 grade failed: {failure}")
    let budgets : List (String × Limits) := [
      ("decoder", { maxNodes := 0 }),
      ("audit", { maxAuditSteps := 0 }),
      ("packet bytes", { maxInputBytes := packet.utf8ByteSize - 1 })]
    for (label, limits) in budgets do
      match grade env limits .storeReturnValue64 artifact packet with
      | .ok _ => throw (IO.userError s!"exhausted {dialect} {label} budget was accepted")
      | .error failure =>
        unless failure.kind == .resource && failureStatus failure.kind == 6 do
          throw (IO.userError s!"{dialect} {label} returned the wrong failure category: {failure}")
    IO.println s!"PASS {dialect} full64 default grade: decoder={accepted.decoderSteps}, audit={accepted.auditSteps}, kernelChecks={accepted.kernelChecks}; exhausted decoder/audit/packet-byte budgets return resource status6"

#eval checkBudgets

end GradingStoreReturnValue64BudgetTests

#print axioms EDSL.Grading.domain_nonvacuous
#print axioms EDSL.Grading.Known.storeReturnValue64
#print axioms EDSL.Grading.StoreReturnValue64.Domain.resource_pre
#print axioms EDSL.Tests.GradingStoreReturnValue64.unsupported_not_claim
#print axioms EDSL.Tests.GradingStoreReturnValue64.upper_half_only_admitted
#print axioms EDSL.Tests.GradingStoreReturnValue64.Narrow.actual_execution
#print axioms EDSL.Tests.GradingStoreReturnValue64.Narrow.raw_policy
#print axioms EDSL.Tests.GradingStoreReturnValue64.Narrow.not_claim
#print axioms EDSL.Tests.GradingStoreReturnValue64.Truncated.actual_execution
#print axioms EDSL.Tests.GradingStoreReturnValue64.Truncated.not_claim
#audit_edsl
