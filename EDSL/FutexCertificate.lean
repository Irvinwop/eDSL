/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.FutexStubs

namespace EDSL.FutexCertificate
open X86 Examples.FutexStubs

def accepts (profile : Profile) (candidate : List Byte) : Bool :=
  decide (candidate = profile.bytes)

/-- Exact userspace request/return contract. Current code and protected current
return-stack bytes are premises for resumption; no kernel implementation,
wait termination, predicate truth, or ownership acquisition is certified here. -/
def Specification (profile : Profile) (initial : State) (word : Word)
    (expected : BitVec 32) : Prop :=
  Invokes initial (request profile initial) profile.entryCost ∧ ¬ Diverges initial ∧
  (∀ other count, Invokes initial other count →
    other = request profile initial ∧ count = profile.entryCost) ∧
  CanonicalRequest profile (request profile initial) word expected ∧
  ∀ current after raw target,
    CodeAt current initial.rip profile.bytes →
    ReturnsAt (request profile initial) current raw after →
    readWord current (initial.registers .rsp) = .ok target →
    canonical target = true →
    Executes after (returnFinal after target) 1 ∧ ¬ Diverges after ∧
    (∀ final count, Executes after final count → final = returnFinal after target ∧ count = 1) ∧
    (returnFinal after target).registers .rax = raw ∧
    (returnFinal after target).registers .rsp = initial.registers .rsp + 8 ∧
    (returnFinal after target).memory = current ∧
    profile.entryCost + 1 = profile.completedCost

theorem sound (profile : Profile) (candidate : List Byte)
    (accepted : accepts profile candidate = true)
    (initial : State) (word : Word) (expected : BitVec 32)
    (arguments : CanonicalArguments profile initial word expected)
    (code : CodeAt initial.memory initial.rip candidate) :
    candidate = profile.bytes ∧ Specification profile initial word expected := by
  have equal : candidate = profile.bytes := of_decide_eq_true accepted
  subst candidate
  obtain ⟨invoked, finite, unique⟩ := reaches_request profile initial code
  refine ⟨rfl, invoked, finite, unique, request_canonical profile initial word expected arguments, ?_⟩
  intro current after raw target currentCode returned stack valid
  exact returns_correct profile initial after current raw target currentCode returned stack valid

end EDSL.FutexCertificate
