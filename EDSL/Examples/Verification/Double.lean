/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Examples.Verification.Double
open X86 X86.Sequential X86.VCGen PureCall

/-- Unsigned modular doubling, stated without an instruction or execution. -/
def spec : Spec where
  Input := Word
  arguments value index := if index.val = 0 then some (.word64 value) else none
  domain _ := True
  result value output := output.toNat = (2 * value.toNat) % 2^64
  useful value := value ≠ 0

/-- Synthetic complete LEA RAX,[RDI+RDI]; RET. This example makes no compiler,
ELF, native execution or corpus-coverage claim. -/
def bytes : List Byte := [0x48, 0x8d, 0x04, 0x3f, 0xc3]

/-- Discovery proposes the graph from the bytes; the independent production
checker authenticates it. No hand-written instruction list is required. -/
def graph : CFG.Graph := vcgen_graph bytes

theorem valid : CFG.Valid bytes graph := CFG.discover_sound (by decide +kernel)

abbrev entry : graph.Index := ⟨0, by decide +kernel⟩

/-- A new finite routine supplies its argument facts and mathematical result;
the shared tactic composes the production steps and proves the successors. -/
theorem generated (input : Invocation spec) (initial : State)
    (pre : Pre spec bytes input initial) :
    wp graph initial.rip (PureCallAllowed initial) 2 entry initial
      (fun result => Post spec input initial result.state) := by
  have argument : initial.registers .rdi = input.value :=
    pre.arguments 0 (.word64 input.value) rfl
  have stack := pre.stack
  have target := pre.returnCanonical
  vcgen_run graph entry simp [PureCallAllowed, RawRead, stack, target]
  refine ⟨?_, rfl, rfl, rfl, ?_, rfl⟩
  · simp [spec, argument, Result.prepend, BitVec.toNat_add, Nat.two_mul]
  · simp [calleeSaved, Result.prepend]

/-- One generic bridge supplies every-AF execution and every-prefix original
caller authority, full memory/permissions, ABI and nonarithmetic flags. The
sequential target profile and stable ordinary RAM remain assumptions. -/
theorem semantics : Grading.ReadOnlySemanticClaim (readOnlyTask spec) bytes :=
  pureCall_semantics_of_generated spec bytes graph valid entry (by decide +kernel) 2
    (fun input initial result => Post spec input initial result.state)
    (fun _ _ _ evidence => evidence) generated

/-- Actual fetched execution for every admitted machine state. -/
theorem executes (input : Invocation spec) (initial : State)
    (pre : Pre spec bytes input initial) (choices : Choices) :
    ∃ result, Sequential.run choices 2 initial = .ok result ∧
      Post spec input initial result.state := by
  obtain ⟨result, actual, post, _, _⟩ := run_sound valid pre.code
    (by change initial.rip = initial.rip + 0#64; simp) (generated input initial pre) choices
  exact ⟨result, actual, post⟩

/-- OS-resource calls use the same proof. Current code/caller loans and the
same complete world survive every actual prefix and the real return. -/
theorem resources_survive (resource : Resources spec) (initial : State)
    (pre : ResourcePre spec bytes resource initial) :
    AllExecutions initial (fun result =>
      Post spec (resourceInput resource) initial result.state ∧
      OS.CallResources.Current resource.call resource.shared result.state) ∧
    Grading.ReadOnlyPolicy initial (OS.CallResources.Current resource.call resource.shared)
      (fun _ => OS.CallResources.ReadAllowed resource.call resource.shared) :=
  semantics.resource resource initial pre

end EDSL.Examples.Verification.Double
