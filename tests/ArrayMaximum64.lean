/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.ArrayMaximum64
import EDSL.Grading.Driver
import EDSL.Audit

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace EDSL.Tests.ArrayMaximum64
open X86 X86.Sequential EDSL.ArrayMaximum64 Grading

private def variants : List (List Byte) := [GCC.bytes,Clang.bytes]

/-- Test input construction changes data only. The real decoder and executor
still fetch every instruction from the complete final compiler byte window. -/
private def sample (bytes : List Byte) (values : List Word) : State :=
  let initial := Domain.initial bytes
  { initial with
    registers := fun register => if register = .rsi then BitVec.ofNat 64 values.length
      else initial.registers register
    memory := (values.zipIdx).foldl (fun memory (value,index) =>
      writeQWordUnchecked memory (131072 + BitVec.ofNat 64 (8 * index)) value) initial.memory }

private def observe (bytes : List Byte) (values : List Word) (fuel : Nat) (af : Bool) :
    Except Error (Nat × Word × Word × Word × Word × List Read) := do
  let result ← Sequential.run (fun _ => af) fuel (sample bytes values)
  return (result.instructions,result.state.registers .rax,result.state.rip,
    result.state.registers .rsp,result.state.flags &&& ~~~arithmeticFlagMask,result.reads)

/-- Both high halves and unsigned order matter. A signed comparison chooses
0x100000001 and a narrowed comparison chooses one instead of this result. The
literal trace checks the final element and actual RET as well as the answer. -/
theorem unsigned_high_half (af : Bool) :
    variants.map (fun bytes => observe bytes [1,0x100000001,0x8000000000000000,1] 33 af) =
      [.ok (33,0x8000000000000000,8192,65552,0x602,
        [⟨.data,131072,8⟩,⟨.data,131080,8⟩,⟨.data,131088,8⟩,
          ⟨.data,131096,8⟩,⟨.stack,65544,8⟩]),
       .ok (29,0x8000000000000000,8192,65552,0x602,
        [⟨.data,131072,8⟩,⟨.data,131080,8⟩,⟨.data,131088,8⟩,
          ⟨.data,131096,8⟩,⟨.stack,65544,8⟩])] := by
  cases af <;> rfl

/-- Equal maxima do not end the loop early. The maximum 64-bit word remains
intact even when a later zero and a repeated maximum are present. -/
theorem repeated_maximum (af : Bool) :
    variants.map (fun bytes => observe bytes [0xffffffffffffffff,0,0xffffffffffffffff] 26 af) =
      [.ok (26,0xffffffffffffffff,8192,65552,0x602,
        [⟨.data,131072,8⟩,⟨.data,131080,8⟩,⟨.data,131088,8⟩,⟨.stack,65544,8⟩]),
       .ok (23,0xffffffffffffffff,8192,65552,0x602,
        [⟨.data,131072,8⟩,⟨.data,131080,8⟩,⟨.data,131088,8⟩,⟨.stack,65544,8⟩])] := by
  cases af <;> rfl

/-- The answer alone does not establish a returned execution. One less
instruction than each complete compiler execution must exhaust the evaluator. -/
theorem insufficient_return_fuel (af : Bool) :
    observe GCC.bytes [1,0x100000001,0x8000000000000000,1] 32 af = .error .exhaustedFuel ∧
    observe Clang.bytes [1,0x100000001,0x8000000000000000,1] 28 af = .error .exhaustedFuel := by
  cases af <;> exact ⟨rfl,rfl⟩

def emptyCall (bytes : List Byte) (unusedBase : Word) (unusedLoan : Nat) : OS.ArrayResources64.Call :=
  { toCall := (Domain.call bytes).toCall, base := unusedBase, values := [], inputLoan := unusedLoan }

def emptyResource (bytes : List Byte) (unusedBase : Word) (unusedLoan : Nat) : Resources :=
  ⟨(Domain.resource bytes).shared,emptyCall bytes unusedBase unusedLoan⟩

def emptyInitial (bytes : List Byte) (unusedBase : Word) : State :=
  let initial := Domain.initial bytes
  { initial with registers := fun register =>
      if register = .rdi then unusedBase else if register = .rsi then 0 else initial.registers register }

/-- Admission accepts every unused pointer and loan ID, independent of the
decoder and of useful nonempty witnesses. No data allocation is requested for
the empty input; code and the original caller slot remain current. -/
theorem empty_pre (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (unusedBase : Word) (unusedLoan : Nat) :
    ResourcePre bytes (emptyResource bytes unusedBase unusedLoan) (emptyInitial bytes unusedBase) := by
  refine ⟨⟨?_,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩
  exact OS.ArrayResources64.Contract.of_nil (Domain.contract bytes positive bound).pureCall rfl

private def observeEmpty (bytes : List Byte) (af : Bool) : Except Error (Nat × Word × List Read) := do
  let result ← Sequential.run (fun _ => af) 5 (emptyInitial bytes 0x8000000000000001)
  return (result.instructions,result.state.registers .rax,result.reads)

/-- This noncanonical unaligned base is not readable. Both final functions
nevertheless return zero and read only the original caller slot when count=0. -/
theorem empty_invalid_pointer (af : Bool) :
    variants.map (fun bytes => observeEmpty bytes af) =
      [.ok (5,0,[⟨.stack,65544,8⟩]),.ok (4,0,[⟨.stack,65544,8⟩])] := by
  cases af <;> rfl

theorem invalid_pointer_unmapped :
    canonical (0x8000000000000001 : Word) = false ∧
    (emptyInitial GCC.bytes 0x8000000000000001).memory.read 0x8000000000000001 = none ∧
    (emptyResource GCC.bytes 0x8000000000000001 999).shared.loans 999 = none := by
  exact ⟨rfl,rfl,rfl⟩

/-- The universal closed claims return exactly the same coherent resource
world. The current code, caller-slot and any nonempty input loans survive the
actual return, with all RAM/permission maps preserved by the postcondition. -/
theorem returned_resources {bytes resource initial}
    (claim : Grading.Claim .arrayMaximum64 bytes) (pre : ResourcePre bytes resource initial)
    (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      Post initial resource.call.values resource.call.returnAddress result.state ∧
      OS.ArrayResources64.Current resource.call resource.shared result.state ∧
      OS.Threads.HasLoan resource.shared resource.call.worker resource.call.codeLoan
        ⟨resource.call.code,resource.call.bytes.length⟩ ∧
      OS.Threads.HasLoan resource.shared resource.call.worker resource.call.stackLoan
        ⟨resource.call.stack,8⟩ ∧
      (resource.call.values ≠ [] →
        OS.Threads.HasLoan resource.shared resource.call.worker resource.call.inputLoan
          resource.call.inputRegion) := by
  obtain ⟨result,actual,post,current⟩ := (claim.1.resource resource initial pre).1 choices
  exact ⟨result,actual,post,current,current.contract.pureCall.codeLoan,
    current.contract.pureCall.stackLoan,current.contract.input⟩

def stackAlias (bytes : List Byte) : Resources :=
  ⟨(Domain.resource bytes).shared,
    { toCall := (Domain.call bytes).toCall, base := 65544, values := [8192], inputLoan := 1 }⟩

def stackAliasInitial (bytes : List Byte) : State :=
  let initial := Domain.initial bytes
  { initial with registers := fun register =>
      if register = .rdi then 65544 else if register = .rsi then 1 else initial.registers register }

/-- A compatible input/caller-slot alias can share the exact same current
loan ID. Neither the raw contract nor OS admission requires disjoint reads. -/
theorem stack_alias_pre (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    ResourcePre bytes (stackAlias bytes) (stackAliasInitial bytes) := by
  have pureCall := (Domain.contract bytes positive bound).pureCall
  refine ⟨⟨⟨pureCall,?_,?_,fun _ => pureCall.stackLoan⟩,rfl⟩,
    rfl,rfl,rfl,rfl,rfl⟩
  · intro index value present
    cases index with
    | zero =>
      simp [stackAlias] at present
      subst value
      change loadQWord (OS.AddressSpace.toMemory (Grading.Domain.space bytes)) 65544 = .ok 8192
      rw [loadQWord_congr _ (OS.AddressSpace.toMemory Grading.Domain.payload) _
        (Grading.Domain.memory_agrees_far bytes bound _ 8 (by decide) (by decide))]
      rfl
    | succ index => simp [stackAlias] at present
  · change (65544 : Word).toNat + 8 * 1 ≤ 2^64
    decide

/-- This is an actual all-choice execution of the compiler claim on the alias
above, preserving the shared loan and using it for both DATA8 and STACK8. -/
theorem stack_alias_returns {bytes : List Byte} (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (claim : Grading.Claim .arrayMaximum64 bytes)
    (choices : Choices) :
    ∃ result, Sequential.Executes choices (stackAliasInitial bytes) result ∧
      result.state.registers .rax = 8192 ∧
      OS.ArrayResources64.Current (stackAlias bytes).call (stackAlias bytes).shared result.state ∧
      OS.ArrayResources.ReadPermission (stackAlias bytes).shared 10 ⟨.data,65544,8⟩ ∧
      OS.ArrayResources.ReadPermission (stackAlias bytes).shared 10 ⟨.stack,65544,8⟩ := by
  have pre := stack_alias_pre bytes positive bound
  obtain ⟨result,actual,post,current,_,_,_⟩ := returned_resources claim pre choices
  have assigned : result.state.registers .rax = 8192 := by
    apply BitVec.eq_of_toNat_eq
    exact post.value
  exact ⟨result,actual,assigned,current,
    pre.read_permission (Or.inl ⟨rfl,rfl,0,by change 0 < 1; decide,rfl⟩),
    pre.read_permission (Or.inr ⟨rfl,rfl,rfl⟩)⟩

/-- Domain evidence does not silently restrict the other registers or flags
to the convenient defaults used by the concrete evaluator vectors. -/
theorem arbitrary_incoming_state (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (incoming : Register → Word) (flags : Word) :
    ∃ resource initial, ResourcePre bytes resource initial ∧ initial.flags = flags ∧
      ∀ register, register ∉ [.rdi,.rsi,.rsp] → initial.registers register = incoming register := by
  refine ⟨Domain.resource bytes,Domain.initial bytes incoming flags,
    Domain.resource_pre bytes positive bound incoming flags,rfl,?_⟩
  intro register outside
  cases register <;> simp_all [Domain.initial]

/-- Truncated FF group bytes retain useful present machine and OS inputs; decoder
failure is not hidden by the useful witness construction. -/
theorem unsupported_domain : Nonvacuous (registered .arrayMaximum64) [0xff] :=
  domain_nonvacuous .arrayMaximum64 [0xff] (by decide) (by decide)

/-- This refutation uses an actual decoder fault at a current admitted input.
A timeout, unsupported proof export or unsuccessful search is not a defect. -/
theorem unsupported_not_claim : ¬Grading.Claim .arrayMaximum64 [0xff] := by
  intro claim
  have pre := Domain.resource_pre [0xff] (by decide) (by decide)
  have executions := (claim.1.machine (resourceInput (Domain.resource [0xff]))
    (Domain.initial [0xff]) pre.machine).1
  have fault : step false (Domain.initial [0xff]) = .error (.inaccessibleInstruction 4097) := rfl
  have impossible := executions.no_fault_prefix (fun _ => false)
    (Sequential.run_fault (choices := fun _ => false) (fuel := 0) fault)
  cases impossible

end EDSL.Tests.ArrayMaximum64

open Lean EDSL EDSL.Grading EDSLGrader EDSLGrader.Runtime

-- Parser, quotation and registration are checked against the independent
-- array task. Reusing the scalar maximum registration must fail conversion.
run_cmd do
  let env := (← getEnv).toKernelEnv
  let some id := taskID "arrayMaximum64" | throwError "array maximum spelling rejected"
  unless (registered id).profile == .sequentialReadOnlyX86CallableV1 do
    throwError "wrong array maximum callable profile"
  let idType := mkConst ``TaskID
  let expectedID := mkConst ``TaskID.arrayMaximum64
  let idEquality := mkApp3 (mkConst ``Eq [1]) idType (taskExpr id) expectedID
  let idProof := mkApp2 (mkConst ``Eq.refl [1]) idType expectedID
  match checkExpr env {} idEquality idProof `EDSLGrader.Internal.arrayMaximumIDTest with
  | .error failure => throwError "wrong array maximum task ID: {failure}"
  | .ok _ => pure ()
  let taskType := mkConst ``Grading.Task
  let actual := mkApp (mkConst ``registered) (taskExpr id)
  let specification := mkApp (mkConst ``ofReadOnly) (mkConst ``ArrayMaximum64.readOnlyTask)
  let equality := mkApp3 (mkConst ``Eq [2]) taskType actual specification
  let proof := mkApp2 (mkConst ``Eq.refl [2]) taskType specification
  match checkExpr env {} equality proof `EDSLGrader.Internal.arrayMaximumRegistrationTest with
  | .error failure => throwError "wrong array maximum specification: {failure}"
  | .ok _ => pure ()
  for spelling in ["ArrayMaximum64", "arrayMaximum64 ", "arraymaximum64", "arrayMaximum"] do
    unless (taskID spelling).isNone do
      throwError "unregistered array maximum spelling accepted: {spelling}"
  logInfo "Array maximum spelling, quotation, independent task and callable profile checked"

/-- Import the trusted module set afresh without candidate modules. Useful
independent resource domains remain available; no compiler proof is admitted. -/
def checkArrayMaximumTrustedBoundary : IO Unit := do
  initSearchPath (← findSysroot)
  let trusted ← importModules #[{ module := `EDSL.Grading.Known },
    { module := `EDSL.Grading.Artifact },
    { module := `EDSL.Grading.CallStack.Artifact },
    { module := `EDSL.Grading.CallMemory64.Artifact },
    { module := `EDSL.Grading.CallMemoryLoop64.Artifact },
    { module := `EDSL.Grading.AtomicLogical64.Artifact },
    { module := `EDSL.Grading.AtomicSet64.Artifact }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  unless (trusted.find? `EDSL.ArrayMaximum64.Domain.nonvacuous).isSome do
    throw (IO.userError "independent array maximum domain missing from trusted snapshot")
  for (name, _) in trusted.constants.toList do
    for clientNamespace in [`EDSL.ArrayMaximum64.GCC,`EDSL.ArrayMaximum64.Clang,`EDSL.ArrayMaximum64.Client] do
      if clientNamespace.isPrefixOf name then
        throw (IO.userError s!"array maximum compiler client imported into trusted snapshot: {name}")
  IO.println "PASS array maximum trusted snapshot has independent domain and excludes compiler clients"

#eval checkArrayMaximumTrustedBoundary

#print axioms EDSL.ArrayMaximum64.Client.gcc
#print axioms EDSL.ArrayMaximum64.Client.clang
#print axioms EDSL.Tests.ArrayMaximum64.empty_pre
#print axioms EDSL.Tests.ArrayMaximum64.returned_resources
#print axioms EDSL.Tests.ArrayMaximum64.stack_alias_returns
#print axioms EDSL.Tests.ArrayMaximum64.unsupported_not_claim
#audit_edsl
