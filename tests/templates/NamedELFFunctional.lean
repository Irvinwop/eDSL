/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Named
import EDSL.Examples.Verification.Double
import EDSL.ELF.CallerResources.Stack
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.NamedImportedDouble
open X86 X86.Sequential X86.VCGen PureCall
open GeneratedCFG.Named (observedGraph)

abbrev imported := GeneratedCFG.Named.observedInput
abbrev file := GeneratedCFG.Named.observedELF
def name : List Byte := [116, 119, 105, 99, 101] -- twice
abbrev bytes := GeneratedCFG.Named.observedBytes
abbrev spec := Examples.Verification.Double.spec

theorem valid : CFG.Valid bytes observedGraph := GeneratedCFG.Named.valid
abbrev entry : observedGraph.Index := ⟨0, by decide +kernel⟩

theorem generated (input : Invocation spec) (initial : State)
    (pre : Pre spec bytes input initial) :
    wp observedGraph initial.rip (PureCallAllowed initial) (observedGraph.maxDepth + 1) entry initial
      (fun result => Post spec input initial result.state) := by
  have argument : initial.registers .rdi = input.value :=
    pre.arguments 0 (.word64 input.value) rfl
  have stack := pre.stack
  have target := pre.returnCanonical
  vcgen_run observedGraph entry simp [PureCallAllowed, RawRead, stack, target, BitVec.add_assoc]
  refine ⟨?_, rfl, rfl, rfl, ?_, rfl⟩
  · change (initial.registers .rdi + initial.registers .rdi).toNat =
      (2 * input.value.toNat) % 2^64
    rw [argument]
    simpa only [Nat.two_mul] using
      (BitVec.toNat_add (input.value : Word) (input.value : Word))
  · simp [calleeSaved, Result.prepend]

theorem semantics : Grading.ReadOnlySemanticClaim (readOnlyTask spec) bytes :=
  pureCall_semantics_of_generated spec bytes observedGraph valid entry (by decide +kernel)
    (observedGraph.maxDepth + 1) (fun input initial result => Post spec input initial result.state)
    (fun _ _ _ evidence => evidence) generated

abbrev caller := ELF.CallerResources.Stack.standard

theorem fresh : ELF.fresh imported.table.image caller.prior = true :=
  ELF.CallerResources.Stack.check_sound imported.table.image caller.stack
    caller.returnAddress (by decide +kernel)

theorem separate : OS.Ownership.Disjoint
    ⟨imported.function.window.base, imported.bytes.length⟩ caller.region := by
  decide +kernel

/-- A useful modeled current call accompanies the universal semantic claim.
The compiler and native Linux/CPU refinement remain outside this theorem. -/
def certificate : ELFCertificate spec file name :=
  ELFCertificate.ofCaller spec imported GeneratedCFG.Named.inputChecked semantics
    caller fresh ELF.CallerResources.Stack.standard_facts separate (7 : Word)
    trivial (by change (7 : Word) ≠ 0; decide +kernel)

def environment := ELF.CallerResources.initial file imported caller
def resource (value : Word) : Resources spec := Domain.resource environment spec value
def initial (value : Word) : State := Domain.initial environment spec value

theorem pre (value : Word) :
    ResourcePre spec bytes (resource value) (initial value) :=
  Domain.resource_pre
    (ELF.CallerResources.initial_facts GeneratedCFG.Named.inputChecked fresh
      ELF.CallerResources.Stack.standard_facts separate) spec value rfl trivial

/-- Literal full64 wraparound through an actual loaded current-resource call,
including the original caller's authority at the real return. -/
theorem wraparound (choices : Choices) :
    ∃ result, Sequential.Executes choices (initial 0xffffffffffffffff) result ∧
      result.state.registers .rax = 0xfffffffffffffffe ∧
      result.state.rip = caller.returnAddress ∧
      OS.CallResources.Current (resource 0xffffffffffffffff).call
        (resource 0xffffffffffffffff).shared result.state := by
  obtain ⟨result, actual, post, current⟩ :=
    (semantics.resource _ _ (pre 0xffffffffffffffff)).1 choices
  refine ⟨result, actual, BitVec.eq_of_toNat_eq ?_, post.returnAddress, current⟩
  exact post.result.trans (by decide +kernel)

end EDSL.Tests.NamedImportedDouble

#print axioms EDSL.Tests.NamedImportedDouble.semantics
#print axioms EDSL.Tests.NamedImportedDouble.certificate
#print axioms EDSL.Tests.NamedImportedDouble.wraparound
#audit_edsl
