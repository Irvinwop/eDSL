/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Domain
import EDSL.PureCall.Domain

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.PureCall.Candidate
open X86 OS

/-- The established executable-span and original caller-slot loans, without
an operand allocation or any interpretation of the candidate bytes. -/
def call (bytes : List Byte) : CallResources.Call :=
  ⟨10, 4096, 65544, 8192, bytes, 0, 1⟩

def resource (spec : Spec) (value : spec.Input) (bytes : List Byte) : Resources spec :=
  ⟨Grading.Domain.shared bytes, call bytes, value⟩

/-- Realize the supplied scalar arguments, then install the original RSP.
The complete ordinary memory is the existing candidate-domain mapping. -/
def initial (spec : Spec) (value : spec.Input) (bytes : List Byte)
    (flags : Word := 0x202) : State where
  registers register :=
    if register = .rsp then 65544 else Domain.registers spec value register
  rip := 4096
  flags := flags
  memory := AddressSpace.toMemory (Grading.Domain.space bytes)

/-- Reuse current byte mapping, allocation owners/epochs and original loans.
This evidence does not depend on decoding, execution or a scalar result. -/
theorem contract (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    CallResources.Contract (call bytes) (Grading.Domain.shared bytes) := by
  have base := Grading.Domain.contractA bytes positive bound
  exact ⟨base.wellFormed, base.held.code, base.held.stack, base.code, base.stack,
    base.returnCanonical, base.stackBound, base.postStackCanonical⟩

/-- Installing RSP preserves every supplied word64 or low32 argument in all
six integer argument registers; absent arguments impose no requirement. -/
theorem initial_arguments (spec : Spec) (value : spec.Input) (bytes : List Byte)
    (flags : Word := 0x202) : Bound spec value (initial spec value bytes flags) := by
  intro ⟨index, bound⟩ argument supplied
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 := by
    omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change argument.Holds (Domain.argumentValue (spec.arguments value _))
    have realized := Domain.argumentValue_holds argument
    rw [← supplied] at realized
    exact realized

/-- A domain value and present bounded bytes suffice for current admission.
The actual return-slot value, canonicality and full memory coupling are
inherited from the established resource proof. -/
theorem resource_pre (spec : Spec) (value : spec.Input) (domain : spec.domain value)
    (bytes : List Byte) (positive : 0 < bytes.length) (bound : bytes.length ≤ 4096)
    (flags : Word := 0x202) :
    ResourcePre spec bytes (resource spec value bytes) (initial spec value bytes flags) :=
  ⟨⟨contract bytes positive bound, rfl⟩, rfl, rfl, rfl, domain,
    initial_arguments spec value bytes flags⟩

/-- Every nonempty candidate of at most 4096 bytes, including unsupported
code, has useful raw and current-resource inputs from a single supplied
domain/useful witness. Execution and every-input semantic claims are separate. -/
theorem nonvacuous (spec : Spec) (value : spec.Input) (domain : spec.domain value)
    (useful : spec.useful value) (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) :
    Grading.ReadOnlyNonvacuous (readOnlyTask spec) bytes :=
  nonvacuous_of_resource (resource spec value bytes) (initial spec value bytes) useful
    (resource_pre spec value domain bytes positive bound)

end EDSL.PureCall.Candidate
