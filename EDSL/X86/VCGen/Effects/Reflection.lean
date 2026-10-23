/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Effects
import EDSL.X86.VCGen.Choices

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Computational reflection for the existing bounded effect-aware WP. Policy and
postcondition decisions are explicit inputs; the only choice enumeration uses
the instruction's finite active flag representatives. Its completeness proof
uses equality of the entire production executor observation.

The Boolean checks only `wp`. Structural validity, initial executable bytes,
entry RIP and the mandatory `CodeFrame` law remain separate premises of every
execution theorem. This layer adds no interpreter, full-memory frame, decision
procedure for `CodeAt`, or interpretation of sequential traces as OS, scheduler,
TSO, linearizability, hardware or corpus claims.
-/

namespace EDSL.X86.VCGen.Effects
open Sequential

variable {profile : CFG.Profile}

/-- Decide the existing effect WP by fuel induction, with finite active flag
representatives and finite graph successors. The caller supplies all decisions
on policy predicates and the independent result/event contract. Inactive flags
cannot affect any part of the checked observation, including reads, effects,
continuing state, atomic payloads and execution errors. -/
def decidableWP (graph : CFG.Graph) (base : Word) (policy : Policy)
    (decCurrent : ∀ state, Decidable (policy.Current state))
    (decReads : ∀ state read, Decidable (policy.AllowedRead state read))
    (decEffects : ∀ state instruction observation,
      Decidable (policy.AllowedEffect state instruction observation))
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    (decPost : ∀ result events, Decidable (Post result events)) :
    Decidable (wp graph base policy fuel node initial Post) := by
  letI (state : State) : Decidable (policy.Current state) := decCurrent state
  letI (state : State) (read : Read) : Decidable (policy.AllowedRead state read) :=
    decReads state read
  letI (state : State) (instruction : Sequential.Instruction) (observation : Observation) :
      Decidable (policy.AllowedEffect state instruction observation) :=
    decEffects state instruction observation
  induction fuel generalizing node initial Post with
  | zero => exact isFalse id
  | succ fuel induction =>
    change Decidable (policy.Current initial ∧ ∀ choices : FlagChoices, _)
    refine @instDecidableAnd _ _ (decCurrent initial) ?_
    refine decidableFlagChoices ((graph.node node).instruction.undefinedFlags initial) _ ?_ ?_
    · intro choices
      cases effect : executeWith initial (graph.node node).instruction choices with
      | error fault => exact isFalse id
      | ok observation =>
        simp only
        letI (result : Result) (events : List AtomicEvent) : Decidable (Post result events) :=
          decPost result events
        cases outcome : observation.result with
        | returned final => infer_instance
        | next middle =>
          letI (destination : graph.Index) :
              Decidable (wp graph base policy fuel destination middle
                (fun result events => Post (result.prepend 1 observation.reads) events)) :=
            induction destination middle
              (fun result events => Post (result.prepend 1 observation.reads) events)
              (fun result events => decPost (result.prepend 1 observation.reads) events)
          infer_instance
        | atomic event middle =>
          letI (destination : graph.Index) :
              Decidable (wp graph base policy fuel destination middle
                (fun result events => Post (result.prepend 1 observation.reads) (event :: events))) :=
            induction destination middle
              (fun result events => Post (result.prepend 1 observation.reads) (event :: events))
              (fun result events => decPost (result.prepend 1 observation.reads) (event :: events))
          infer_instance
        | syscall request => infer_instance
    · intro left right agree
      dsimp only
      rw [executeWith_congr initial (graph.node node).instruction left right agree]

/-- Reflect only the generated dynamic obligations. No executable-memory or
structural admission predicate is silently made decidable by this checker. -/
def check (graph : CFG.Graph) (base : Word) (policy : Policy)
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    [Decidable (wp graph base policy fuel node initial Post)] : Bool :=
  decide (wp graph base policy fuel node initial Post)

/-- Acceptance is equivalent to the unchanged effect-aware WP. -/
theorem check_iff (graph : CFG.Graph) (base : Word) (policy : Policy)
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    [Decidable (wp graph base policy fuel node initial Post)] :
    check graph base policy fuel node initial Post = true ↔
      wp graph base policy fuel node initial Post := by
  simp [check]

/-- A checked WP, the exact structurally validated graph, actual entry code and
RIP, and the mandatory effect code frame give the existing production run. The
contract and checked trace retain the ordered atomic event list, and the result
retains the engine's instruction count and ordered reads. -/
theorem checked_run_sound {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Structural.Valid bytes graph profile)
    {base : Word} {policy : Policy} {fuel : Nat} {node : graph.Index}
    {initial : State} {Post : Contract}
    [Decidable (wp graph base policy fuel node initial Post)]
    (frame : CodeFrame policy bytes base)
    (code : CodeAt initial.memory base bytes)
    (nodePC : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (accepted : check graph base policy fuel node initial Post = true)
    (choices : ChoiceStream FlagChoices) :
    ∃ result events, runWith choices fuel initial = .ok result ∧ Post result events ∧
      result.instructions ≤ fuel ∧ Trace bytes base policy choices initial result events :=
  run_sound valid frame code nodePC (of_decide_eq_true accepted) choices

/-- The same explicit environmental premises certify an actual returning
execution, its independent result/event contract, and its ordered checked trace. -/
theorem checked_sound {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Structural.Valid bytes graph profile)
    {base : Word} {policy : Policy} {fuel : Nat} {node : graph.Index}
    {initial : State} {Post : Contract}
    [Decidable (wp graph base policy fuel node initial Post)]
    (frame : CodeFrame policy bytes base)
    (code : CodeAt initial.memory base bytes)
    (nodePC : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (accepted : check graph base policy fuel node initial Post = true)
    (choices : ChoiceStream FlagChoices) :
    ∃ result events, ExecutesWith choices initial result ∧ Post result events ∧
      result.instructions ≤ fuel ∧ Trace bytes base policy choices initial result events :=
  sound valid frame code nodePC (of_decide_eq_true accepted) choices

/-- Every complete flag-choice stream satisfies the independent contract for
its actual event list within the checked instruction bound. -/
theorem checked_all_executions {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Structural.Valid bytes graph profile)
    {base : Word} {policy : Policy} {fuel : Nat} {node : graph.Index}
    {initial : State} {Post : Contract}
    [Decidable (wp graph base policy fuel node initial Post)]
    (frame : CodeFrame policy bytes base)
    (code : CodeAt initial.memory base bytes)
    (nodePC : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (accepted : check graph base policy fuel node initial Post = true) :
    AllExecutionsWith initial
      (fun result => (∃ events, Post result events) ∧ result.instructions ≤ fuel) :=
  all_executions valid frame code nodePC (of_decide_eq_true accepted)

/-- All reachable continuing prefixes are sequentially safe under every vector
choice, subject to the same code binding and effect frame premises. -/
theorem checked_safe {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Structural.Valid bytes graph profile)
    {base : Word} {policy : Policy} {fuel : Nat} {node : graph.Index}
    {initial : State} {Post : Contract}
    [Decidable (wp graph base policy fuel node initial Post)]
    (frame : CodeFrame policy bytes base)
    (code : CodeAt initial.memory base bytes)
    (nodePC : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (accepted : check graph base policy fuel node initial Post = true) :
    Engine.Safe stepWith initial :=
  safe valid frame code nodePC (of_decide_eq_true accepted)

#print axioms decidableWP
#print axioms check
#print axioms check_iff
#print axioms checked_run_sound
#print axioms checked_sound
#print axioms checked_all_executions
#print axioms checked_safe

end EDSL.X86.VCGen.Effects

#audit_edsl
