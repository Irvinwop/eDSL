/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGVerification
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.ELF.Loader

namespace EDSL.X86.VCGen
open Sequential

variable {profile : CFG.Profile}

/-- The client's contract observes the final state, the exact retired-instruction
count, and the ordered operand-read trace. It is independent of the checker. -/
abbrev Contract := Result → Prop

/-- A trace of actual decoded steps, with permissions checked in each actual
pre-instruction state. Atomic and syscall boundaries have no constructor. -/
inductive CheckedTrace (AllowedRead : State → Read → Prop) :
    Choices → State → Result → Prop where
  | ret {choices initial final reads}
      (actual : Sequential.step (choices 0) initial = .ok ⟨.returned final, reads⟩)
      (allowed : ∀ read ∈ reads, AllowedRead initial read) :
      CheckedTrace AllowedRead choices initial ⟨final, 1, reads⟩
  | next {choices initial middle reads result}
      (actual : Sequential.step (choices 0) initial = .ok ⟨.next middle, reads⟩)
      (allowed : ∀ read ∈ reads, AllowedRead initial read)
      (tail : CheckedTrace AllowedRead (choices.drop 1) middle result) :
      CheckedTrace AllowedRead choices initial (result.prepend 1 reads)

theorem CheckedTrace.execution {AllowedRead : State → Read → Prop}
    {choices initial result} (trace : CheckedTrace AllowedRead choices initial result) :
    Sequential.Executes choices initial result := by
  induction trace with
  | ret actual _ => exact Sequential.Executes.ret actual
  | next actual _ _ induction => exact Sequential.Executes.next actual induction

/-- Every reported read has both an actual decoded origin and the client's
permission at that origin, including the protected return-stack read. -/
theorem CheckedTrace.read_origin {AllowedRead : State → Read → Prop}
    {choices initial result} (trace : CheckedTrace AllowedRead choices initial result)
    {read : Read} (member : read ∈ result.reads) :
    ∃ count before priorReads observation, count < result.instructions ∧
      Sequential.Block choices initial before count priorReads ∧
      Sequential.step (choices count) before = .ok observation ∧
      read ∈ observation.reads ∧ AllowedRead before read ∧
      OperandReadSucceeds before read := by
  induction trace with
  | @ret choices initial final reads actual allowed =>
    exact ⟨0, initial, [], ⟨.returned final, reads⟩, by simp,
      Sequential.Block.nil, actual, member, allowed read member,
      observed_reads_succeed actual read member⟩
  | @next choices initial middle reads result actual allowed tail induction =>
    rcases List.mem_append.mp member with first | suffix
    · exact ⟨0, initial, [], ⟨.next middle, reads⟩, by
        change 0 < 1 + result.instructions
        omega,
        Sequential.Block.nil, actual, first, allowed read first,
        observed_reads_succeed actual read first⟩
    · obtain ⟨count, before, priorReads, observation, bound, block, step,
        present, permitted, succeeded⟩ := induction suffix
      refine ⟨count + 1, before, reads ++ priorReads, observation, ?_,
        Sequential.Block.next actual block, ?_, present, permitted, succeeded⟩
      · change count + 1 < 1 + result.instructions
        omega
      · simpa only [ChoiceStream.drop, Nat.add_comm 1 count] using step

/-- Generate bounded weakest preconditions by reducing the production ISA
executor. The only instruction data comes from an independently byte-checked
CFG. The generator automatically composes all successor obligations; clients
provide no per-instruction `localVC`. Both values of the named undefined flag
(AF or OF) are required; inactive choices are ignored by the executor.

Zero fuel, machine errors, locked events, syscalls and missing successors fail
closed. This first profile inherits the CFG's explicit read-only restriction. -/
def wp (graph : CFG.Graph) (base : Word) (AllowedRead : State → Read → Prop) :
    Nat → graph.Index → State → Contract → Prop
  | 0, _, _, _ => False
  | fuel + 1, node, state, Post => ∀ af : Bool,
    match execute state (graph.node node).instruction af with
    | .error _ => False
    | .ok observation =>
      (∀ read ∈ observation.reads, AllowedRead state read) ∧
      match observation.result with
      | .returned final => Post ⟨final, 1, observation.reads⟩
      | .next middle => ∃ destination : graph.Index,
          middle.rip = base + BitVec.ofNat 64 (graph.node destination).offset ∧
          wp graph base AllowedRead fuel destination middle
            (fun result => Post (result.prepend 1 observation.reads))
      | .atomic _ _ | .syscall _ => False

/-- One ordinary register step with defined flags has no operand-read
obligation and only its real successor WP. This is a proof rule for the
production executor, applicable to any instruction with the stated effect. -/
theorem wp_pure_next_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (initial final : State) (Post : Contract)
    (effect : ∀ af, execute initial (graph.node node).instruction af = .ok ⟨.next final, []⟩) :
    wp graph base AllowedRead (fuel + 1) node initial Post ↔
      ∃ destination : graph.Index,
        final.rip = base + BitVec.ofNat 64 (graph.node destination).offset ∧
        wp graph base AllowedRead fuel destination final
          (fun result => Post (result.prepend 1 [])) := by
  simp [wp, effect]

/-- Sound once for every checked binary, initial state, independently chosen
contract and complete AF sequence. Exact code bytes are fetched from actual
current executable RAM; the static graph cannot override them. -/
theorem sound {bytes : List Byte} {graph : CFG.Graph} (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base AllowedRead fuel node initial Post) (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧ Post result ∧
      result.instructions ≤ fuel ∧ CheckedTrace AllowedRead choices initial result := by
  induction fuel generalizing node initial Post choices with
  | zero => exact False.elim vc
  | succ fuel induction =>
    have one := vc (choices 0)
    cases effect : execute initial (graph.node node).instruction (choices 0) with
    | error fault => simp only [effect] at one
    | ok observation =>
      have actual : Sequential.step (choices 0) initial = .ok observation := by
        rw [valid.step_eq_execute code node initial rfl pc]
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
        exact ⟨⟨final, 1, observation.reads⟩, Sequential.Executes.ret actual, after,
          Nat.succ_le_succ (Nat.zero_le fuel), CheckedTrace.ret actual allowed⟩
      | next middle =>
        simp only [outcome] at after
        obtain ⟨destination, nextPC, nextVC⟩ := after
        obtain ⟨_, _, _, memory, _⟩ := valid.next code node pc actual outcome
        have nextCode : CodeAt middle.memory base bytes := by rwa [memory]
        obtain ⟨result, execution, post, bound, trace⟩ :=
          induction nextCode nextPC nextVC (choices.drop 1)
        have exactObservation : observation = ⟨.next middle, observation.reads⟩ := by
          cases observation
          simp_all
        rw [exactObservation] at actual
        refine ⟨result.prepend 1 observation.reads, Sequential.Executes.next actual execution,
          post, ?_, CheckedTrace.next actual allowed trace⟩
        change 1 + result.instructions ≤ fuel + 1
        omega
      | atomic event middle => simp only [outcome] at after
      | syscall request => simp only [outcome] at after

/-- A successful VC also produces the production bounded evaluator's result.
No claim depends on native evaluation, an external solver or an untrusted
instruction interpreter. -/
theorem run_sound {bytes : List Byte} {graph : CFG.Graph} (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base AllowedRead fuel node initial Post) (choices : Choices) :
    ∃ result, Sequential.run choices fuel initial = .ok result ∧ Post result ∧
      result.instructions ≤ fuel ∧ CheckedTrace AllowedRead choices initial result := by
  obtain ⟨result, execution, post, bound, trace⟩ := sound valid code pc vc choices
  exact ⟨result, Sequential.run_complete execution bound, post, bound, trace⟩

/-- Executable reflection is available whenever the generated obligations are
decidable. Symbolic clients can instead discharge `wp` by kernel-checked
simplification and arithmetic proof terms. A false result has no defect or
insecurity interpretation. -/
def check (graph : CFG.Graph) (base : Word) (AllowedRead : State → Read → Prop)
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    [Decidable (wp graph base AllowedRead fuel node initial Post)] : Bool :=
  decide (wp graph base AllowedRead fuel node initial Post)

/-- Complete executable admission for a concrete modeled initial state. Besides
the generated VC, this checks the decoder-validated CFG, actual executable RAM
bytes and current entry RIP. `check` alone reflects only the dynamic formula. -/
def certifyWith (profile : CFG.Profile) (bytes : List Byte) (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (initial : State) (Post : Contract)
    [Decidable (wp graph base AllowedRead fuel node initial Post)] : Bool :=
  CFG.checkWith profile bytes graph && ELF.checkCode initial.memory base bytes &&
    decide (initial.rip = base + BitVec.ofNat 64 (graph.node node).offset) &&
    check graph base AllowedRead fuel node initial Post

/-- Compatibility entry point, fixed to the original CFG admission profile. -/
def certify (bytes : List Byte) (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (initial : State) (Post : Contract)
    [Decidable (wp graph base AllowedRead fuel node initial Post)] : Bool :=
  certifyWith CFG.defaultProfile bytes graph base AllowedRead fuel node initial Post

private def decidableChoice (chooses : Bool) (P : Bool → Prop)
    (decision : ∀ af, Decidable (P af))
    (independent : chooses = false → ∀ af, P af ↔ P false) : Decidable (∀ af, P af) :=
  if noChoice : chooses = false then
    letI := decision false
    decidable_of_iff (P false) ⟨fun admitted af => (independent noChoice af).mpr admitted,
      fun admitted => admitted false⟩
  else
    letI (af : Bool) : Decidable (P af) := decision af
    inferInstance

/-- Construct the executable decision procedure from decidable client
contracts. The recursion is on fuel and enumerates finite CFG-node choices.
The existing ISA independence theorem avoids branching on an undefined flag for instructions
which ignore it. No external solver is called. -/
def decidableWP (graph : CFG.Graph) (base : Word) (AllowedRead : State → Read → Prop)
    (decReads : ∀ state read, Decidable (AllowedRead state read))
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    (decPost : ∀ result, Decidable (Post result)) :
    Decidable (wp graph base AllowedRead fuel node initial Post) := by
  letI (state : State) (read : Read) : Decidable (AllowedRead state read) := decReads state read
  induction fuel generalizing node initial Post with
  | zero => exact isFalse id
  | succ fuel induction =>
    change Decidable (∀ af : Bool, _)
    refine decidableChoice ((graph.node node).instruction.choiceFlag initial).isSome _ ?_ ?_
    · intro af
      cases effect : execute initial (graph.node node).instruction af with
      | error fault => exact isFalse id
      | ok observation =>
        simp only
        letI (result : Result) : Decidable (Post result) := decPost result
        cases outcome : observation.result with
        | returned final => infer_instance
        | next middle =>
          letI (destination : graph.Index) :
              Decidable (wp graph base AllowedRead fuel destination middle
                (fun result => Post (result.prepend 1 observation.reads))) :=
            induction destination middle (fun result => Post (result.prepend 1 observation.reads))
              (fun result => decPost (result.prepend 1 observation.reads))
          infer_instance
        | atomic event middle => infer_instance
        | syscall request => infer_instance
    · intro independent af
      have noChoice : (graph.node node).instruction.choiceFlag initial = none :=
        Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp independent)
      rw [execute_choice_independent initial (graph.node node).instruction af false noChoice]

theorem check_iff (graph : CFG.Graph) (base : Word) (AllowedRead : State → Read → Prop)
    (fuel : Nat) (node : graph.Index) (initial : State) (Post : Contract)
    [Decidable (wp graph base AllowedRead fuel node initial Post)] :
    check graph base AllowedRead fuel node initial Post = true ↔
      wp graph base AllowedRead fuel node initial Post := by
  simp [check]

theorem checked_sound {bytes : List Byte} {graph : CFG.Graph} (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    [Decidable (wp graph base AllowedRead fuel node initial Post)]
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (accepted : check graph base AllowedRead fuel node initial Post = true)
    (choices : Choices) :
    ∃ result, Sequential.run choices fuel initial = .ok result ∧ Post result ∧
      result.instructions ≤ fuel ∧ CheckedTrace AllowedRead choices initial result :=
  run_sound valid code pc (of_decide_eq_true accepted) choices

/-- A successful complete checker directly yields a production decoded run.
Its premises contain no trusted claimed opcode, assumed future execution or
external semantic solver result. Platform/OS interpretation of the modeled
initial state remains the caller's environmental obligation. -/
theorem certifyWith_sound {bytes : List Byte} {graph : CFG.Graph}
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    [Decidable (wp graph base AllowedRead fuel node initial Post)]
    (accepted : certifyWith profile bytes graph base AllowedRead fuel node initial Post = true)
    (choices : Choices) :
    ∃ result, Sequential.run choices fuel initial = .ok result ∧ Post result ∧
      result.instructions ≤ fuel ∧ CheckedTrace AllowedRead choices initial result := by
  have parts : CFG.checkWith profile bytes graph = true ∧
      ELF.checkCode initial.memory base bytes = true ∧
      initial.rip = base + BitVec.ofNat 64 (graph.node node).offset ∧
      check graph base AllowedRead fuel node initial Post = true := by
    simpa only [certifyWith, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using accepted
  exact checked_sound (CFG.checkWith_sound parts.1)
    (ELF.checkCode_sound _ _ _ parts.2.1) parts.2.2.1 parts.2.2.2 choices

theorem certify_sound {bytes : List Byte} {graph : CFG.Graph}
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    [Decidable (wp graph base AllowedRead fuel node initial Post)]
    (accepted : certify bytes graph base AllowedRead fuel node initial Post = true)
    (choices : Choices) :
    ∃ result, Sequential.run choices fuel initial = .ok result ∧ Post result ∧
      result.instructions ≤ fuel ∧ CheckedTrace AllowedRead choices initial result :=
  certifyWith_sound accepted choices

/-- The independently selected result contract and fuel bound hold for every
concrete execution, including every choice of the named undefined flag. -/
theorem all_executions {bytes : List Byte} {graph : CFG.Graph} (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base AllowedRead fuel node initial Post) :
    Sequential.AllExecutions initial (fun result => Post result ∧ result.instructions ≤ fuel) := by
  intro choices
  obtain ⟨result, execution, post, bound, _⟩ := sound valid code pc vc choices
  exact ⟨result, execution, post, bound⟩

theorem safe {bytes : List Byte} {graph : CFG.Graph} (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base AllowedRead fuel node initial Post) : Sequential.Safe initial :=
  (all_executions valid code pc vc).safe

theorem no_divergence {bytes : List Byte} {graph : CFG.Graph} (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base AllowedRead fuel node initial Post) : ¬ Sequential.Diverges initial :=
  (all_executions valid code pc vc).no_divergence

/-- An independent lower-bound contract proves that less fuel cannot terminate
this exact program on this admitted input. This is a dynamic instruction lower
bound, not a minimum across equivalent programs or a physical cycle count. -/
theorem lower_bound_exhausted {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel minimum : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base AllowedRead fuel node initial Post)
    (lower : ∀ result, Post result → minimum ≤ result.instructions)
    (choices : Choices) {short : Nat} (tooShort : short < minimum) :
    Sequential.run choices short initial = .error .exhaustedFuel := by
  obtain ⟨result, execution, post, _, _⟩ := sound valid code pc vc choices
  exact execution.exhausted (Nat.lt_of_lt_of_le tooShort (lower result post))

end EDSL.X86.VCGen
