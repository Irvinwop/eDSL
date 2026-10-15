/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.FutexStubs
import EDSL.OS.Futex.History

namespace EDSL.OS.Futex
open X86 Examples.FutexStubs

def stubOperation : Profile → BitVec 32 → Op
  | .wait, expected => .wait expected
  | .wakeOne, _ => .wakeOne

/-- The independent exact-byte ABI specification satisfies the service's
canonical classifier. Full RAX and zero unused registers remain explicit. -/
theorem canonical_request_classifies (profile : Profile) (request : SyscallRequest)
    (word : Word) (expected : BitVec 32)
    (supported : CanonicalRequest profile request word expected) :
    classify request = .ok (stubOperation profile expected) ∧
      request.user.registers .rdi = word := by
  obtain ⟨number, _, address, operation, value, fourth, fifth, sixth⟩ := supported
  simp only [SyscallRequest.argument] at address operation value fourth fifth sixth
  cases profile with
  | wait =>
    simp only [Profile.operation] at operation
    simp only [↓reduceIte] at value
    simp [classify, number, address, operation, value, fourth, fifth, sixth, stubOperation]
  | wakeOne =>
    simp only [Profile.operation] at operation
    simp only [reduceCtorEq, ↓reduceIte] at value
    simp [classify, number, address, operation, value, fourth, fifth, sixth, stubOperation]

/-- Exact machine invocation and service admission agree at their common
request boundary. Native kernel conformance is a separate target contract. -/
theorem exact_stub_request (profile : Profile) (initial : X86.State)
    (word : Word) (expected : BitVec 32)
    (code : CodeAt initial.memory initial.rip profile.bytes)
    (arguments : CanonicalArguments profile initial word expected) :
    Invokes initial (request profile initial) profile.entryCost ∧
      classify (request profile initial) = .ok (stubOperation profile expected) ∧
      (request profile initial).user.registers .rdi = word := by
  have canonical := request_canonical profile initial word expected arguments
  exact ⟨(reaches_request profile initial code).1,
    (canonical_request_classifies _ _ _ _ canonical).1,
    (canonical_request_classifies _ _ _ _ canonical).2⟩

end EDSL.OS.Futex
