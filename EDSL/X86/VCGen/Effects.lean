/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.StructuralControl
import EDSL.X86.Sequential.ExecutionChoices

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
A bounded sequential effect-aware VCG over structurally authenticated bytes and
the production vector executor. Policies authorize actual observations; a
separate, mandatory `CodeFrame` law preserves executable text at every
continuation. Data memory may change. The checked trace retains the exact
ordered atomic payloads, which the existing engine's `Result` does not expose.

This is a sequential foundation. Connecting it to current OS resources requires
a later simulation with coherent resource/world evolution. It establishes no
ownership epochs, scheduling, TSO, linearizability, compiler/hardware preservation,
unbounded-loop support, or new corpus coverage. Syscalls and execution errors
fail closed. Existing read-only APIs are unchanged.
-/

namespace EDSL.X86.VCGen.Effects
open Sequential

variable {profile : CFG.Profile}

/-- Predicates selected by the trusted verification task or registry, independently
 of candidate bytes or a submitted proof packet.
`AllowedEffect` sees the decoded instruction and the complete actual observation.
In particular, authorizing a store must account for its prestate write intent;
equality of initial and final memory does not distinguish a same-value store.
`Current` alone supplies no OS-resource evolution theorem. -/
structure Policy where
  Current : State → Prop
  AllowedRead : State → Read → Prop
  AllowedEffect : State → Sequential.Instruction → Observation → Prop

/-- The policy must preserve the selected executable bytes across every allowed
actual continuation, including atomic continuations. This law is required by
soundness separately from the generated WP; it is neither a candidate Boolean
nor an assumed full-memory frame. -/
def CodeFrame (policy : Policy) (bytes : List Byte) (base : Word) : Prop :=
  ∀ (before : State) (instruction : Sequential.Instruction) (choices : FlagChoices)
    (observation : Observation) (after : State),
    policy.Current before → CodeAt before.memory base bytes →
    executeWith before instruction choices = .ok observation →
    policy.AllowedEffect before instruction observation →
    CFG.Structural.Continues observation after → CodeAt after.memory base bytes

/-- An independent contract on the existing full result and the exact ordered
atomic-event list. The event list is justified by `Trace`, not reconstructed from
the final CPU or memory and not returned by `runWith`. -/
abbrev Contract := Result → List AtomicEvent → Prop

/-- Checked actual production steps, with code binding, current-state facts,
decoding and read/effect authorization in every real instruction prestate.
The trace needs no graph parameter: its instruction is authenticated by actual
decoding. The generated WP separately records graph successors and their RIPs.

Only `atomic` extends the event list, by prepending its actual payload. Thus the
index retains order and multiplicity through ordinary steps and return. This is
a proof-only refinement of the existing engine, not another interpreter. -/
inductive Trace (bytes : List Byte) (base : Word) (policy : Policy) :
    ChoiceStream FlagChoices → State → Result → List AtomicEvent → Prop where
  | ret {choices initial final reads instruction}
      (code : CodeAt initial.memory base bytes)
      (current : policy.Current initial)
      (decoded : Sequential.decodeAt initial = .ok instruction)
      (actual : stepWith (choices 0) initial = .ok ⟨.returned final, reads⟩)
      (allowedRead : ∀ read ∈ reads, policy.AllowedRead initial read)
      (allowedEffect : policy.AllowedEffect initial instruction ⟨.returned final, reads⟩)
      (finalCurrent : policy.Current final) :
      Trace bytes base policy choices initial ⟨final, 1, reads⟩ []
  | next {choices initial middle reads instruction result events}
      (code : CodeAt initial.memory base bytes)
      (current : policy.Current initial)
      (decoded : Sequential.decodeAt initial = .ok instruction)
      (actual : stepWith (choices 0) initial = .ok ⟨.next middle, reads⟩)
      (allowedRead : ∀ read ∈ reads, policy.AllowedRead initial read)
      (allowedEffect : policy.AllowedEffect initial instruction ⟨.next middle, reads⟩)
      (tail : Trace bytes base policy (choices.drop 1) middle result events) :
      Trace bytes base policy choices initial (result.prepend 1 reads) events
  | atomic {choices initial middle reads instruction result events event}
      (code : CodeAt initial.memory base bytes)
      (current : policy.Current initial)
      (decoded : Sequential.decodeAt initial = .ok instruction)
      (actual : stepWith (choices 0) initial = .ok ⟨.atomic event middle, reads⟩)
      (allowedRead : ∀ read ∈ reads, policy.AllowedRead initial read)
      (allowedEffect : policy.AllowedEffect initial instruction ⟨.atomic event middle, reads⟩)
      (tail : Trace bytes base policy (choices.drop 1) middle result events) :
      Trace bytes base policy choices initial (result.prepend 1 reads) (event :: events)

/-- Erasing the additional policy and event evidence yields execution by the
existing production engine, including its actual atomic constructor. -/
theorem Trace.execution {bytes : List Byte} {base : Word} {policy : Policy}
    {choices : ChoiceStream FlagChoices} {initial : State} {result : Result}
    {events : List AtomicEvent} (trace : Trace bytes base policy choices initial result events) :
    Engine.Executes stepWith choices initial result := by
  induction trace with
  | ret _ _ _ actual _ _ _ => exact Engine.Executes.ret actual
  | next _ _ _ actual _ _ _ induction => exact Engine.Executes.next actual induction
  | atomic _ _ _ actual _ _ _ induction => exact Engine.Executes.atomic actual induction

/-- Bounded obligations over the production executor and a finite graph index.
Every complete flag valuation must execute successfully, with all actual reads
and the actual effect allowed. Return checks the final current-state predicate
and independent contract. Continuing steps require a graph edge, the actual RIP
and a recursive residual contract, consuming one instruction of fuel. Atomic
steps also prepend the actual event to that residual contract.

Zero fuel, errors, syscalls and absent successors fail closed. Code binding is
an explicit soundness premise transported by `CodeFrame`, outside this formula.
No atomic oracle, guessed poststate or per-program interpreter is used. -/
def wp (graph : CFG.Graph) (base : Word) (policy : Policy) :
    Nat → graph.Index → State → Contract → Prop
  | 0, _, _, _ => False
  | fuel + 1, node, state, Post => policy.Current state ∧ ∀ choices : FlagChoices,
    match executeWith state (graph.node node).instruction choices with
    | .error _ => False
    | .ok observation =>
      (∀ read ∈ observation.reads, policy.AllowedRead state read) ∧
      policy.AllowedEffect state (graph.node node).instruction observation ∧
      match observation.result with
      | .returned final => policy.Current final ∧ Post ⟨final, 1, observation.reads⟩ []
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

/-- Generated obligations give an actual returning production execution for
any choice stream, the independent result/event contract, the fuel bound and
an ordered checked trace. Every continuation applies the mandatory code frame
before the next recursive decoding; full memory equality is not required. -/
theorem sound {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Structural.Valid bytes graph profile)
    {base : Word} {policy : Policy} {fuel : Nat} {node : graph.Index}
    {initial : State} {Post : Contract}
    (frame : CodeFrame policy bytes base)
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base policy fuel node initial Post)
    (choices : ChoiceStream FlagChoices) :
    ∃ result events, ExecutesWith choices initial result ∧ Post result events ∧
      result.instructions ≤ fuel ∧ Trace bytes base policy choices initial result events := by
  induction fuel generalizing node initial Post choices with
  | zero => exact False.elim vc
  | succ fuel induction =>
    have current : policy.Current initial := vc.1
    have one := vc.2 (choices 0)
    have decoded := valid.decoded code node initial rfl pc
    cases effect : executeWith initial (graph.node node).instruction (choices 0) with
    | error fault => simp only [effect] at one
    | ok observation =>
      have actual : stepWith (choices 0) initial = .ok observation := by
        rw [stepWith_eq_executeWith (choices 0) decoded]
        exact effect
      simp only [effect] at one
      rcases one with ⟨allowedRead, allowedEffect, after⟩
      cases outcome : observation.result with
      | returned final =>
        have exactObservation : observation = ⟨.returned final, observation.reads⟩ := by
          cases observation
          simp_all
        rw [exactObservation] at actual allowedEffect
        simp only [outcome] at after
        obtain ⟨finalCurrent, post⟩ := after
        exact ⟨⟨final, 1, observation.reads⟩, [], Engine.Executes.ret actual, post,
          Nat.succ_le_succ (Nat.zero_le fuel),
          Trace.ret code current decoded actual allowedRead allowedEffect finalCurrent⟩
      | next middle =>
        simp only [outcome] at after
        obtain ⟨destination, _, nextPC, nextVC⟩ := after
        have nextCode : CodeAt middle.memory base bytes :=
          frame initial (graph.node node).instruction (choices 0) observation middle
            current code effect allowedEffect (Or.inl outcome)
        obtain ⟨result, events, execution, post, bound, trace⟩ :=
          induction nextCode nextPC nextVC (choices.drop 1)
        have exactObservation : observation = ⟨.next middle, observation.reads⟩ := by
          cases observation
          simp_all
        rw [exactObservation] at actual allowedEffect
        refine ⟨result.prepend 1 observation.reads, events, Engine.Executes.next actual execution,
          post, ?_, Trace.next code current decoded actual allowedRead allowedEffect trace⟩
        change 1 + result.instructions ≤ fuel + 1
        omega
      | atomic event middle =>
        simp only [outcome] at after
        obtain ⟨destination, _, nextPC, nextVC⟩ := after
        have nextCode : CodeAt middle.memory base bytes :=
          frame initial (graph.node node).instruction (choices 0) observation middle
            current code effect allowedEffect (Or.inr ⟨event, outcome⟩)
        obtain ⟨result, events, execution, post, bound, trace⟩ :=
          induction nextCode nextPC nextVC (choices.drop 1)
        have exactObservation : observation = ⟨.atomic event middle, observation.reads⟩ := by
          cases observation
          simp_all
        rw [exactObservation] at actual allowedEffect
        refine ⟨result.prepend 1 observation.reads, event :: events,
          Engine.Executes.atomic actual execution, post, ?_,
          Trace.atomic code current decoded actual allowedRead allowedEffect trace⟩
        change 1 + result.instructions ≤ fuel + 1
        omega
      | syscall request => simp only [outcome] at after

/-- Reuse the existing engine's completeness theorem for bounded replay.
`runWith` returns the existing `Result`; its separate event list is certified by
the checked trace and the independent contract. -/
theorem run_sound {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Structural.Valid bytes graph profile)
    {base : Word} {policy : Policy} {fuel : Nat} {node : graph.Index}
    {initial : State} {Post : Contract}
    (frame : CodeFrame policy bytes base)
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base policy fuel node initial Post)
    (choices : ChoiceStream FlagChoices) :
    ∃ result events, runWith choices fuel initial = .ok result ∧ Post result events ∧
      result.instructions ≤ fuel ∧ Trace bytes base policy choices initial result events := by
  obtain ⟨result, events, execution, post, bound, trace⟩ := sound valid frame code pc vc choices
  exact ⟨result, events, Engine.run_complete stepWith execution bound, post, bound, trace⟩

/-- Every choice stream has a returning execution satisfying the independent
contract for its checked event list, within the same fuel bound. -/
theorem all_executions {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Structural.Valid bytes graph profile)
    {base : Word} {policy : Policy} {fuel : Nat} {node : graph.Index}
    {initial : State} {Post : Contract}
    (frame : CodeFrame policy bytes base)
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base policy fuel node initial Post) :
    AllExecutionsWith initial
      (fun result => (∃ events, Post result events) ∧ result.instructions ≤ fuel) := by
  intro choices
  obtain ⟨result, events, execution, post, bound, _⟩ := sound valid frame code pc vc choices
  exact ⟨result, execution, ⟨events, post⟩, bound⟩

/-- All actual reachable continuing prefixes are safe under every vector choice,
by the existing engine's safety theorem. This is sequential prefix safety. -/
theorem safe {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Structural.Valid bytes graph profile)
    {base : Word} {policy : Policy} {fuel : Nat} {node : graph.Index}
    {initial : State} {Post : Contract}
    (frame : CodeFrame policy bytes base)
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base policy fuel node initial Post) :
    Engine.Safe stepWith initial :=
  Engine.AllExecutions.safe stepWith (all_executions valid frame code pc vc)

#print axioms Policy
#print axioms CodeFrame
#print axioms Contract
#print axioms Trace
#print axioms Trace.execution
#print axioms wp
#print axioms sound
#print axioms run_sound
#print axioms all_executions
#print axioms safe

end EDSL.X86.VCGen.Effects

#audit_edsl
