/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Verification.Double
import EDSL.OS.CallResources.Domain
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.VerifyFunction
open X86 X86.Sequential OS PureCall
open Examples.Verification.Double

/-- Independent initial mappings, including unrelated writable/inaccessible
cells. The borrowed code and original caller are declared before execution. -/
def space : AddressSpace.Space where
  cells address :=
    if (⟨0x401320, bytes.length⟩ : AddressSpace.Region).Contains address then
      (bytes[address.toNat - 0x401320]?).map fun byte => ⟨byte, AddressSpace.readExecute⟩
    else if (⟨0x700008, 8⟩ : AddressSpace.Region).Contains address then
      some ⟨(0x654321 : Word).extractLsb' ((address.toNat - 0x700008) * 8) 8,
        AddressSpace.readOnly⟩
    else if address = 0x900000 then some ⟨0xa5, AddressSpace.readWrite⟩
    else if address = 0x900001 then some ⟨0x5a, AddressSpace.inaccessible⟩
    else none

def declared : CallResources.Domain.Initial :=
  ⟨space, 17, 29, 41, 0x401320, bytes, 0x700008, 0x654321⟩

theorem present : CallResources.Domain.Facts declared :=
  CallResources.Domain.check_sound (by decide +kernel)

def resource (value : Word) : Resources spec :=
  ⟨CallResources.Domain.shared declared, CallResources.Domain.call declared, value⟩

def caller (value : Word) (registers : Register → Word) (flags : Word) : State :=
  CallResources.Domain.machine declared
    (fun register => if register = .rdi then value else registers register) flags

theorem admitted (value : Word) (registers : Register → Word) (flags : Word) :
    ResourcePre spec bytes (resource value) (caller value registers flags) := by
  refine ⟨CallResources.Domain.current present _ _, rfl, rfl, ?_, trivial, ?_⟩
  · simp [caller, CallResources.Domain.machine, declared, resource, CallResources.Domain.call]
  · intro index argument binding
    simp only [spec] at binding
    split at binding
    · have zero : index = 0 := Fin.ext (by assumption)
      subst index
      cases binding
      simp [Argument.Holds, caller, CallResources.Domain.machine, argumentRegister, resource]
    · contradiction

/-- Useful raw and OS-resource admissions exist without any result premise. -/
theorem nonvacuous : Grading.ReadOnlyNonvacuous (readOnlyTask spec) bytes :=
  nonvacuous_of_resource (resource 0xffffffffffffffff)
    (caller 0xffffffffffffffff (fun _ => 0) 0)
    (by change (0xffffffffffffffff : Word) ≠ 0; decide +kernel) (admitted _ _ _)

/-- The generic result applies to this useful independently admitted OS world,
including unrelated cells, current code and the original caller loan. -/
theorem admitted_resources_survive (value : Word) (registers : Register → Word) (flags : Word) :
    AllExecutions (caller value registers flags) (fun result =>
      Post spec (resourceInput (resource value)) (caller value registers flags) result.state ∧
      CallResources.Current (resource value).call (resource value).shared result.state) ∧
    Grading.ReadOnlyPolicy (caller value registers flags)
      (CallResources.Current (resource value).call (resource value).shared)
      (fun _ => CallResources.ReadAllowed (resource value).call (resource value).shared) :=
  resources_survive (resource value) (caller value registers flags) (admitted value registers flags)

/-- Actual execution meets independently supplied numeric results while all
other registers, initial flags and the complete AF stream remain arbitrary. -/
theorem numeric_result (value expected : Word)
    (mathematics : expected.toNat = (2 * value.toNat) % 2^64)
    (registers : Register → Word) (flags : Word) (choices : Choices) :
    ∃ result, Sequential.run choices 2 (caller value registers flags) = .ok result ∧
      result.state.registers .rax = expected ∧
      Post spec (resourceInput (resource value)) (caller value registers flags) result.state := by
  obtain ⟨result, actual, post⟩ := executes _ _ (admitted value registers flags).machine choices
  refine ⟨result, actual, BitVec.eq_of_toNat_eq ?_, post⟩
  exact post.result.trans mathematics.symm

-- Independent wrapping/high-bit/full64 expectations catch 32-bit truncation,
-- failure to wrap and accidental dependence on a second argument register.
example (registers : Register → Word) (flags : Word) (choices : Choices) :=
  numeric_result 0xffffffffffffffff 0xfffffffffffffffe (by decide +kernel) registers flags choices
example (registers : Register → Word) (flags : Word) (choices : Choices) :=
  numeric_result 0x8000000000000000 0 (by decide +kernel) registers flags choices
example (registers : Register → Word) (flags : Word) (choices : Choices) :=
  numeric_result 0x80000000 0x100000000 (by decide +kernel) registers flags choices

/-- Same-length mutation selects RDI+RSI instead of RDI+RDI. A previously
accepted graph cannot authenticate different actual bytes. -/
theorem changed_operand_rejected :
    CFG.check [0x48, 0x8d, 0x04, 0x37, 0xc3] graph = false := by decide +kernel

/-- Search must close the RIP equality before committing to an index.
Index zero is in range but has the wrong offset for this real successor. -/
theorem successor_checked (base : Word) :
    ∃ destination : graph.Index,
      base + 4#64 = base + BitVec.ofNat 64 (graph.node destination).offset ∧ True := by
  vcgen_next
  trivial

/-- A no-op callback must leave its obligation available to the caller.
Factoring the original unsolved goal used to create a cyclic metavariable;
the separately supplied evidence below must still close that exact goal. -/
theorem factor_keeps_unsolved_goal (proposition : Prop) (evidence : proposition) :
    proposition := by
  vcgen_factor => skip
  exact evidence

#print axioms Examples.Verification.Double.generated
#print axioms Examples.Verification.Double.semantics
#print axioms Examples.Verification.Double.resources_survive
#print axioms admitted_resources_survive
#print axioms nonvacuous
#print axioms numeric_result
#print axioms changed_operand_rejected
#print axioms successor_checked
#print axioms factor_keeps_unsolved_goal
end EDSL.Tests.VerifyFunction
#audit_edsl
