/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects.Head

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Generated continuation obligations for one production vector-executor step.
The choice domain and its selection of full flag valuations are parameters;
the executor, decoded instruction's effects and complete observation are fixed
by `Sequential.executeWith`. Errors and syscalls fail closed.

Current code binding and actual decoding suffice to regenerate `Head` at this
prestate. No `CodeFrame` is required for one step: this module does not transport
executable bytes to a successor. The existing whole-trace soundness theorem
still requires its separate code frame for recursive decoding. No OS resource
transition, scheduler, TSO simulation or physical refinement is supplied here.
-/

namespace EDSL.X86.VCGen.Effects
open Sequential

/-- Generate obligations from the actual executor, then pass its full
observation to the continuation. Permissions concern the original prestate;
only a returned outcome checks final `Current` here. Continuing-state obligations
belong to `K`. The prestate's `Current` remains outside the choice quantifier,
including when `C` is empty. Selecting uniform Bool valuations does not by itself
cover all independently undefined flag valuations. -/
def oneStep {C : Type} (policy : Policy) (select : C → FlagChoices)
    (before : State) (instruction : Sequential.Instruction)
    (K : C → Observation → Prop) : Prop :=
  policy.Current before ∧ ∀ choice : C,
    match executeWith before instruction (select choice) with
    | .error _ => False
    | .ok observation =>
      (∀ read ∈ observation.reads, policy.AllowedRead before read) ∧
      policy.AllowedEffect before instruction observation ∧
      (∀ final, observation.result = .returned final → policy.Current final) ∧
      (∀ request, observation.result ≠ .syscall request) ∧
      K choice observation

/-- Actual code binding and actual decoding identify the generated obligation
with declarative head evidence for every selected valuation. `Head` itself has
no syscall-exclusion field, so exclusion is explicit here. Keeping `Current`
separate makes the reverse implication valid even for an empty choice domain. -/
theorem oneStep_iff_head {C : Type} {bytes : List Byte} {base : Word}
    {policy : Policy} {select : C → FlagChoices} {before : State}
    {instruction : Sequential.Instruction} {K : C → Observation → Prop}
    (code : CodeAt before.memory base bytes)
    (decoded : Sequential.decodeAt before = .ok instruction) :
    oneStep policy select before instruction K ↔
      policy.Current before ∧ ∀ choice : C, ∃ observation,
        Head bytes base policy (select choice) before instruction observation ∧
        (∀ request, observation.result ≠ .syscall request) ∧ K choice observation := by
  constructor
  · intro vc
    refine ⟨vc.1, ?_⟩
    intro choice
    have one := vc.2 choice
    cases executed : executeWith before instruction (select choice) with
    | error fault => simp only [executed] at one
    | ok observation =>
      simp only [executed] at one
      obtain ⟨reads, effect, returnedCurrent, noSyscall, post⟩ := one
      have actual : stepWith (select choice) before = .ok observation := by
        rw [stepWith_eq_executeWith (select choice) decoded]
        exact executed
      exact ⟨observation,
        ⟨code, vc.1, decoded, actual, reads, effect, returnedCurrent⟩, noSyscall, post⟩
  · rintro ⟨current, heads⟩
    refine ⟨current, ?_⟩
    intro choice
    obtain ⟨observation, head, noSyscall, post⟩ := heads choice
    have executed : executeWith before instruction (select choice) = .ok observation := by
      rw [← stepWith_eq_executeWith (select choice) decoded]
      exact head.actual
    rw [executed]
    exact ⟨head.reads, head.effect, head.returnedCurrent, noSyscall, post⟩

/-- Invert the generated executor obligation once to obtain an actual `Head`
and its continuation, without any client-supplied successor or executor. -/
theorem oneStep_head {C : Type} {bytes : List Byte} {base : Word}
    {policy : Policy} {select : C → FlagChoices} {before : State}
    {instruction : Sequential.Instruction} {K : C → Observation → Prop}
    (code : CodeAt before.memory base bytes)
    (decoded : Sequential.decodeAt before = .ok instruction)
    (vc : oneStep policy select before instruction K) (choice : C) :
    ∃ observation, Head bytes base policy (select choice) before instruction observation ∧
      (∀ request, observation.result ≠ .syscall request) ∧ K choice observation :=
  ((oneStep_iff_head code decoded).mp vc).2 choice

/-- Specialize to an already identified actual step. Equality of production
observations fixes every result, read and atomic payload seen by `K`. -/
theorem oneStep_head_of_step {C : Type} {bytes : List Byte} {base : Word}
    {policy : Policy} {select : C → FlagChoices} {before : State}
    {instruction : Sequential.Instruction} {K : C → Observation → Prop}
    (code : CodeAt before.memory base bytes)
    (decoded : Sequential.decodeAt before = .ok instruction)
    (vc : oneStep policy select before instruction K) (choice : C)
    {observation : Observation}
    (actual : stepWith (select choice) before = .ok observation) :
    Head bytes base policy (select choice) before instruction observation ∧
      (∀ request, observation.result ≠ .syscall request) ∧ K choice observation := by
  obtain ⟨observed, head, noSyscall, post⟩ := oneStep_head code decoded vc choice
  have same : observed = observation := Except.ok.inj (head.actual.symm.trans actual)
  cases same
  exact ⟨head, noSyscall, post⟩

/-- Weakening only the continuation preserves the generated obligation. -/
theorem oneStep_mono {C : Type} {policy : Policy} {select : C → FlagChoices}
    {before : State} {instruction : Sequential.Instruction}
    {K L : C → Observation → Prop}
    (implies : ∀ choice observation, K choice observation → L choice observation)
    (vc : oneStep policy select before instruction K) :
    oneStep policy select before instruction L := by
  refine ⟨vc.1, ?_⟩
  intro choice
  have one := vc.2 choice
  cases executed : executeWith before instruction (select choice) with
  | error fault => simp only [executed] at one
  | ok observation =>
    simp only [executed] at one ⊢
    obtain ⟨reads, effect, returnedCurrent, noSyscall, post⟩ := one
    exact ⟨reads, effect, returnedCurrent, noSyscall, implies choice observation post⟩

/-- Generate the unchanged bounded WP's continuation from its graph, residual
fuel and independent contract. Continuing outcomes require a graph edge and the
real successor RIP. Residual contracts prepend one instruction and actual reads;
atomic continuations also prepend their actual event. Return checks only `Post`:
`oneStep` supplies final `Current`. Syscalls still fail closed. -/
def wpContinuation (graph : CFG.Graph) (base : Word) (policy : Policy)
    (fuel : Nat) (node : graph.Index) (Post : Contract) (observation : Observation) : Prop :=
  match observation.result with
  | .returned final => Post ⟨final, 1, observation.reads⟩ []
  | .next middle => ∃ destination : graph.Index,
      graph.Edge node destination ∧
      middle.rip = base + BitVec.ofNat 64 (graph.node destination).offset ∧
      wp graph base policy fuel destination middle
        (fun result events => Post (result.prepend 1 observation.reads) events)
  | .atomic event middle => ∃ destination : graph.Index,
      graph.Edge node destination ∧
      middle.rip = base + BitVec.ofNat 64 (graph.node destination).offset ∧
      wp graph base policy fuel destination middle
        (fun result events => Post (result.prepend 1 observation.reads) (event :: events))
  | .syscall _ => False

/-- Factor the existing successor equation through `oneStep` over all full flag
valuations. This is a formula equivalence; code/graph authentication and the
whole-trace code frame retain their existing separate soundness contracts. -/
theorem wp_succ_iff_oneStep (graph : CFG.Graph) (base : Word) (policy : Policy)
    (fuel : Nat) (node : graph.Index) (before : State) (Post : Contract) :
    wp graph base policy (fuel + 1) node before Post ↔
      oneStep policy (fun choices : FlagChoices => choices) before (graph.node node).instruction
        (fun _ observation => wpContinuation graph base policy fuel node Post observation) := by
  simp only [wp, oneStep]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro choices
  cases executed : executeWith before (graph.node node).instruction choices with
  | error fault => rfl
  | ok observation =>
    cases outcome : observation.result <;> simp [wpContinuation, outcome]

#print axioms oneStep
#print axioms oneStep_iff_head
#print axioms oneStep_head
#print axioms oneStep_head_of_step
#print axioms oneStep_mono
#print axioms wpContinuation
#print axioms wp_succ_iff_oneStep

end EDSL.X86.VCGen.Effects

#audit_edsl
