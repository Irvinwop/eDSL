/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Core
import EDSL.X86.Sequential.CFGChoices
import EDSL.X86.Sequential.ExecutionChoices

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.VCGen
open Sequential

variable {profile : CFG.Profile}

/-- Actual decoded vector-choice steps whose operand reads satisfy the supplied
permission predicate in each real pre-instruction state. Atomic and syscall
boundaries have no constructor. -/
inductive CheckedTraceWith (AllowedRead : State → Read → Prop) :
    ChoiceStream FlagChoices → State → Result → Prop where
  | ret {choices initial final reads}
      (actual : stepWith (choices 0) initial = .ok ⟨.returned final, reads⟩)
      (allowed : ∀ read ∈ reads, AllowedRead initial read) :
      CheckedTraceWith AllowedRead choices initial ⟨final, 1, reads⟩
  | next {choices initial middle reads result}
      (actual : stepWith (choices 0) initial = .ok ⟨.next middle, reads⟩)
      (allowed : ∀ read ∈ reads, AllowedRead initial read)
      (tail : CheckedTraceWith AllowedRead (choices.drop 1) middle result) :
      CheckedTraceWith AllowedRead choices initial (result.prepend 1 reads)

theorem CheckedTraceWith.execution {AllowedRead : State → Read → Prop}
    {choices initial result} (trace : CheckedTraceWith AllowedRead choices initial result) :
    ExecutesWith choices initial result := by
  induction trace with
  | ret actual _ => exact Engine.Executes.ret actual
  | next actual _ _ induction => exact Engine.Executes.next actual induction

/-- Each reported read has an actual decoded origin, the client's permission,
and the production memory primitive's successful access checks. -/
theorem CheckedTraceWith.read_origin {AllowedRead : State → Read → Prop}
    {choices initial result} (trace : CheckedTraceWith AllowedRead choices initial result)
    {read : Read} (member : read ∈ result.reads) :
    ∃ count before priorReads observation, count < result.instructions ∧
      BlockWith choices initial before count priorReads ∧
      stepWith (choices count) before = .ok observation ∧
      read ∈ observation.reads ∧ AllowedRead before read ∧
      OperandReadSucceeds before read := by
  induction trace with
  | @ret choices initial final reads actual allowed =>
    exact ⟨0, initial, [], ⟨.returned final, reads⟩, by simp,
      Engine.Block.nil, actual, member, allowed read member,
      stepWith_reads_succeed actual read member⟩
  | @next choices initial middle reads result actual allowed tail induction =>
    rcases List.mem_append.mp member with first | suffix
    · exact ⟨0, initial, [], ⟨.next middle, reads⟩, by
        change 0 < 1 + result.instructions
        omega,
        Engine.Block.nil, actual, first, allowed read first,
        stepWith_reads_succeed actual read first⟩
    · obtain ⟨count, before, priorReads, observation, bound, block, step,
        present, permitted, succeeded⟩ := induction suffix
      refine ⟨count + 1, before, reads ++ priorReads, observation, ?_,
        Engine.Block.next actual block, ?_, present, permitted, succeeded⟩
      · change count + 1 < 1 + result.instructions
        omega
      · simpa only [ChoiceStream.drop, Nat.add_comm 1 count] using step

/-- Bounded weakest preconditions over the production vector executor and an
independently byte-checked CFG. Every complete status-flag valuation is covered;
only declared active bits need enumeration in the decision procedure below.

Zero fuel, execution errors, atomic events, syscalls and missing successors fail
closed. The admitted CFG retains its existing read-only resource profile. -/
def wpWith (graph : CFG.Graph) (base : Word) (AllowedRead : State → Read → Prop) :
    Nat → graph.Index → State → Contract → Prop
  | 0, _, _, _ => False
  | fuel + 1, node, state, Post => ∀ choices : FlagChoices,
    match executeWith state (graph.node node).instruction choices with
    | .error _ => False
    | .ok observation =>
      (∀ read ∈ observation.reads, AllowedRead state read) ∧
      match observation.result with
      | .returned final => Post ⟨final, 1, observation.reads⟩
      | .next middle => ∃ destination : graph.Index,
          middle.rip = base + BitVec.ofNat 64 (graph.node destination).offset ∧
          wpWith graph base AllowedRead fuel destination middle
            (fun result => Post (result.prepend 1 observation.reads))
      | .atomic _ _ | .syscall _ => False

/-- Generated obligations yield a real execution for every complete choice
stream. Decoding is transported from the validated bytes into the actual
current executable RAM at each instruction. -/
theorem soundWith {bytes : List Byte} {graph : CFG.Graph} (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wpWith graph base AllowedRead fuel node initial Post)
    (choices : ChoiceStream FlagChoices) :
    ∃ result, ExecutesWith choices initial result ∧ Post result ∧
      result.instructions ≤ fuel ∧ CheckedTraceWith AllowedRead choices initial result := by
  induction fuel generalizing node initial Post choices with
  | zero => exact False.elim vc
  | succ fuel induction =>
    have one := vc (choices 0)
    cases effect : executeWith initial (graph.node node).instruction (choices 0) with
    | error fault => simp only [effect] at one
    | ok observation =>
      have actual : stepWith (choices 0) initial = .ok observation := by
        rw [stepWith_eq_executeWith (choices 0) (valid.decoded code node initial rfl pc)]
        exact effect
      simp only [effect] at one
      rcases one with ⟨allowed, after⟩
      cases outcome : observation.result with
      | returned final =>
        have exactObservation : observation = ⟨.returned final, observation.reads⟩ := by
          cases observation
          simp_all
        rw [exactObservation] at actual
        simp only [outcome] at after
        exact ⟨⟨final, 1, observation.reads⟩, Engine.Executes.ret actual, after,
          Nat.succ_le_succ (Nat.zero_le fuel), CheckedTraceWith.ret actual allowed⟩
      | next middle =>
        simp only [outcome] at after
        obtain ⟨destination, nextPC, nextVC⟩ := after
        have memory : middle.memory = initial.memory :=
          CFG.executeWith_next_memory (valid.nodes node).2.2.1 effect outcome
        have nextCode : CodeAt middle.memory base bytes := by rwa [memory]
        obtain ⟨result, execution, post, bound, trace⟩ :=
          induction nextCode nextPC nextVC (choices.drop 1)
        have exactObservation : observation = ⟨.next middle, observation.reads⟩ := by
          cases observation
          simp_all
        rw [exactObservation] at actual
        refine ⟨result.prepend 1 observation.reads, Engine.Executes.next actual execution,
          post, ?_, CheckedTraceWith.next actual allowed trace⟩
        change 1 + result.instructions ≤ fuel + 1
        omega
      | atomic event middle => simp only [outcome] at after
      | syscall request => simp only [outcome] at after

/-- The bounded production evaluator retains the proved complete result. -/
theorem run_soundWith {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wpWith graph base AllowedRead fuel node initial Post)
    (choices : ChoiceStream FlagChoices) :
    ∃ result, runWith choices fuel initial = .ok result ∧ Post result ∧
      result.instructions ≤ fuel ∧ CheckedTraceWith AllowedRead choices initial result := by
  obtain ⟨result, execution, post, bound, trace⟩ := soundWith valid code pc vc choices
  exact ⟨result, Engine.run_complete stepWith execution bound, post, bound, trace⟩

/-- A finite universal quantifier is valid only with a proof that inactive bits
cannot affect the actual predicate. The enumeration contains exactly 2^n rows
for n listed active bits, rather than enumerating all six status flags. -/
def decidableFlagChoices (active : List StatusFlag) (predicate : FlagChoices → Prop)
    (decision : ∀ choices, Decidable (predicate choices))
    (independent : FlagChoices.Invariant active predicate) : Decidable (∀ choices, predicate choices) := by
  letI (choices : FlagChoices) : Decidable (predicate choices) := decision choices
  exact decidable_of_iff (∀ candidate ∈ FlagChoices.representatives active, predicate candidate)
    (FlagChoices.forall_iff_representatives active predicate independent).symm

/-- Executable admission enumerates only each instruction's active choices.
The inactive-bit proof concerns the entire observation, including successor
state, operand reads and errors; no projected register result is substituted. -/
def decidableWPWith (graph : CFG.Graph) (base : Word) (AllowedRead : State → Read → Prop)
    (decReads : ∀ state read, Decidable (AllowedRead state read))
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    (decPost : ∀ result, Decidable (Post result)) :
    Decidable (wpWith graph base AllowedRead fuel node initial Post) := by
  letI (state : State) (read : Read) : Decidable (AllowedRead state read) := decReads state read
  induction fuel generalizing node initial Post with
  | zero => exact isFalse id
  | succ fuel induction =>
    change Decidable (∀ choices : FlagChoices, _)
    refine decidableFlagChoices ((graph.node node).instruction.undefinedFlags initial) _ ?_ ?_
    · intro choices
      cases effect : executeWith initial (graph.node node).instruction choices with
      | error fault => exact isFalse id
      | ok observation =>
        simp only
        letI (result : Result) : Decidable (Post result) := decPost result
        cases outcome : observation.result with
        | returned final => infer_instance
        | next middle =>
          letI (destination : graph.Index) :
              Decidable (wpWith graph base AllowedRead fuel destination middle
                (fun result => Post (result.prepend 1 observation.reads))) :=
            induction destination middle (fun result => Post (result.prepend 1 observation.reads))
              (fun result => decPost (result.prepend 1 observation.reads))
          infer_instance
        | atomic event middle => infer_instance
        | syscall request => infer_instance
    · intro left right agree
      dsimp only
      rw [executeWith_congr initial (graph.node node).instruction left right agree]

/-- Reflection checks the generated dynamic formula. Byte, CFG and entry-PC
binding remain explicit premises of the soundness theorem. -/
def checkChoices (graph : CFG.Graph) (base : Word) (AllowedRead : State → Read → Prop)
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    [Decidable (wpWith graph base AllowedRead fuel node initial Post)] : Bool :=
  decide (wpWith graph base AllowedRead fuel node initial Post)

theorem checkChoices_iff (graph : CFG.Graph) (base : Word) (AllowedRead : State → Read → Prop)
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    [Decidable (wpWith graph base AllowedRead fuel node initial Post)] :
    checkChoices graph base AllowedRead fuel node initial Post = true ↔
      wpWith graph base AllowedRead fuel node initial Post := by
  simp [checkChoices]

theorem checked_soundWith {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    [Decidable (wpWith graph base AllowedRead fuel node initial Post)]
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (accepted : checkChoices graph base AllowedRead fuel node initial Post = true)
    (choices : ChoiceStream FlagChoices) :
    ∃ result, runWith choices fuel initial = .ok result ∧ Post result ∧
      result.instructions ≤ fuel ∧ CheckedTraceWith AllowedRead choices initial result :=
  run_soundWith valid code pc (of_decide_eq_true accepted) choices

/-- The independent contract and fuel bound hold for every vector stream. -/
theorem all_executionsWith {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wpWith graph base AllowedRead fuel node initial Post) :
    AllExecutionsWith initial (fun result => Post result ∧ result.instructions ≤ fuel) := by
  intro choices
  obtain ⟨result, execution, post, bound, _⟩ := soundWith valid code pc vc choices
  exact ⟨result, execution, post, bound⟩

/-- All actual reachable prefixes are safe under every vector valuation. -/
theorem safeWith {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wpWith graph base AllowedRead fuel node initial Post) :
    Engine.Safe stepWith initial :=
  Engine.AllExecutions.safe stepWith (all_executionsWith valid code pc vc)

end EDSL.X86.VCGen
