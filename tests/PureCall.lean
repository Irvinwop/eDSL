/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PureCall
import EDSL.OS.CallResources.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.PureCall
open X86 X86.Sequential OS EDSL.PureCall
open X86.VCGen

/-- Independent natural-number specification, with no overflow restriction. -/
def addition : Spec where
  Input := Word × Word
  arguments value index :=
    if index.val = 0 then some (.word64 value.1)
    else if index.val = 1 then some (.word64 value.2) else none
  domain _ := True
  result value result := result.toNat = (value.1.toNat + value.2.toNat) % 2^64
  useful value := value.1 ≠ 0 ∧ value.2 ≠ 0

-- A synthetic complete LEA RAX,[RDI+RSI]; RET window. No ELF/corpus claim.
def bytes : List Byte := [0x48, 0x8d, 0x04, 0x37, 0xc3]
def graph : CFG.Graph :=
  ⟨[⟨0, .lea64 .rax (.indexed .rdi .rsi 0), true, 2⟩,
    ⟨4, .legacy .ret, false, 1⟩], 2⟩
def entry : graph.Index := ⟨0, by decide⟩
theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide +kernel)

/-- Optional observations strengthen the independent mathematical contract. -/
def Observed (input : Invocation addition) (initial : State) (result : Result) : Prop :=
  Post addition input initial result.state ∧ result.instructions = 2 ∧
    result.reads = [⟨.stack, initial.registers .rsp, 8⟩] ∧ result.state.flags = initial.flags

theorem generated (input : Invocation addition) (initial : State)
    (pre : Pre addition bytes input initial) :
    wp graph initial.rip (PureCallAllowed initial) 2 entry initial (Observed input initial) := by
  have left : initial.registers .rdi = input.value.1 := by
    simpa [Argument.Holds, argumentRegister] using
      pre.arguments (0 : Fin 6) (.word64 input.value.1) rfl
  have right : initial.registers .rsi = input.value.2 := by
    simpa [Argument.Holds, argumentRegister] using
      pre.arguments (1 : Fin 6) (.word64 input.value.2) rfl
  have stack := pre.stack
  have target := pre.returnCanonical
  rw [wp]
  intro af
  simp only [entry, graph, CFG.Graph.node, List.getElem_cons_zero,
    execute_lea64, Instruction.length, Address.eval]
  refine ⟨by simp, ⟨⟨1, by decide⟩, rfl, ?_⟩⟩
  rw [wp]
  intro af'
  simp [CFG.Graph.node, execute, Instruction.operandReads, X86.executeInstruction,
    X86.executeRet, State.writeRegister, stack, target, PureCallAllowed, RawRead]
  refine ⟨?_, rfl, rfl, rfl⟩
  refine ⟨?_, rfl, rfl, rfl, ?_, rfl⟩
  · simp [addition, Result.prepend, left, right, BitVec.toNat_add]
  · simp [calleeSaved, Result.prepend]

theorem semantics : Grading.ReadOnlySemanticClaim (readOnlyTask addition) bytes :=
  pureCall_semantics_of_generated addition bytes graph valid entry rfl 2 Observed
    (fun _ _ _ evidence => evidence.1) generated

/-- Actual fetched execution for every admitted state and AF stream. This
checks the generated proof against natural modulo arithmetic, caller return,
whole RAM, callee-saved registers, flags, exact count and original STACK8 read. -/
theorem executes (input : Invocation addition) (initial : State)
    (pre : Pre addition bytes input initial) (choices : Choices) :
    ∃ result, Sequential.run choices 2 initial = .ok result ∧ Observed input initial result := by
  obtain ⟨result, actual, observed, _, _⟩ :=
    run_sound valid pre.code (by simp [entry, graph, CFG.Graph.node])
      (generated input initial pre) choices
  exact ⟨result, actual, observed⟩

def codeBase : Word := 0x401320
def stackBase : Word := 0x700008
def continuation : Word := 0x654321

-- Unrelated mappings include writable and inaccessible cells. Complete RAM
-- equality must preserve both, as well as all code and caller permissions.
def space : AddressSpace.Space where
  cells address :=
    if (⟨codeBase, bytes.length⟩ : AddressSpace.Region).Contains address then
      (bytes[address.toNat - codeBase.toNat]?).map fun byte => ⟨byte, AddressSpace.readExecute⟩
    else if (⟨stackBase, 8⟩ : AddressSpace.Region).Contains address then
      some ⟨continuation.extractLsb' ((address.toNat - stackBase.toNat) * 8) 8,
        AddressSpace.readOnly⟩
    else if address = 0x900000 then some ⟨0xa5, AddressSpace.readWrite⟩
    else if address = 0x900001 then some ⟨0x5a, AddressSpace.inaccessible⟩
    else none

def declared : CallResources.Domain.Initial :=
  ⟨space, 17, 29, 41, codeBase, bytes, stackBase, continuation⟩

theorem present : CallResources.Domain.Facts declared :=
  CallResources.Domain.check_sound (by decide +kernel)

def resource (left right : Word) : Resources addition :=
  ⟨CallResources.Domain.shared declared, CallResources.Domain.call declared, (left, right)⟩

def caller (left right : Word) (registers : Register → Word) (flags : Word) : State :=
  CallResources.Domain.machine declared
    (fun register => if register = .rdi then left else if register = .rsi then right
      else registers register) flags

theorem admitted (left right : Word) (registers : Register → Word) (flags : Word) :
    ResourcePre addition bytes (resource left right) (caller left right registers flags) := by
  refine ⟨CallResources.Domain.current present _ _, rfl, rfl, ?_, trivial, ?_⟩
  · simp [caller, CallResources.Domain.machine, declared, resource, CallResources.Domain.call]
  · intro index argument binding
    simp only [addition] at binding
    split at binding
    · have indexZero : index = 0 := Fin.ext (by assumption)
      subst index
      cases binding
      simp [Argument.Holds, caller, CallResources.Domain.machine, argumentRegister, resource]
    · split at binding
      · have indexOne : index = 1 := Fin.ext (by assumption)
        subst index
        cases binding
        simp [Argument.Holds, caller, CallResources.Domain.machine, argumentRegister, resource]
      · contradiction

/-- Overflowing useful admission is established without any execution or
output premise. The generic bridge supplies both nonvacuity domains. -/
theorem nonvacuous : Grading.ReadOnlyNonvacuous (readOnlyTask addition) bytes :=
  nonvacuous_of_resource (resource 0xffffffffffffffff 1)
    (caller 0xffffffffffffffff 1 (fun _ => 0) 0)
    ⟨by decide +kernel, by decide +kernel⟩ (admitted _ _ _ _)

/-- The return carries the same world, and policy retains original authority
at every reachable prefix; all operand reads have real permitted origins. -/
theorem resources_survive (left right : Word) (registers : Register → Word) (flags : Word) :
    AllExecutions (caller left right registers flags) (fun result =>
      Post addition (resourceInput (resource left right))
        (caller left right registers flags) result.state ∧
      CallResources.Current (resource left right).call (resource left right).shared result.state) ∧
    Grading.ReadOnlyPolicy (caller left right registers flags)
      (CallResources.Current (resource left right).call (resource left right).shared)
      (fun _ => CallResources.ReadAllowed (resource left right).call (resource left right).shared) :=
  semantics.resource _ _ (admitted left right registers flags)

/-- Concrete expected results are independent numerals, not assigned register
expressions. Arbitrary caller state and every AF sequence are retained. -/
theorem numeric_result (left right expected : Word)
    (mathematics : expected.toNat = (left.toNat + right.toNat) % 2^64)
    (registers : Register → Word) (flags : Word) (choices : Choices) :
    ∃ result, Sequential.run choices 2 (caller left right registers flags) = .ok result ∧
      result.state.registers .rax = expected ∧
      Observed (resourceInput (resource left right)) (caller left right registers flags) result := by
  obtain ⟨result, actual, observed⟩ := executes _ _ (admitted left right registers flags).machine choices
  refine ⟨result, actual, BitVec.eq_of_toNat_eq ?_, observed⟩
  exact observed.1.result.trans mathematics.symm

-- Wrapping, high-bit, full64 carry and noncanonical integer-result regressions.
example (registers : Register → Word) (flags : Word) (choices : Choices) :=
  numeric_result 0xffffffffffffffff 1 0 (by decide +kernel) registers flags choices
example (registers : Register → Word) (flags : Word) (choices : Choices) :=
  numeric_result 0x8000000000000000 0x8000000000000000 0
    (by decide +kernel) registers flags choices
example (registers : Register → Word) (flags : Word) (choices : Choices) :=
  numeric_result 0xffffffff 1 0x100000000 (by decide +kernel) registers flags choices
example (registers : Register → Word) (flags : Word) (choices : Choices) :=
  numeric_result 0x7fffffffffff 1 0x800000000000 (by decide +kernel) registers flags choices
example (registers : Register → Word) (flags : Word) (choices : Choices) :=
  numeric_result 0 0 0 (by decide +kernel) registers flags choices

end EDSL.Tests.PureCall

#audit_edsl
