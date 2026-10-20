/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGVerification
import EDSL.X86.Sequential.CFGDiscovery

namespace EDSL.X86.VCGen.Cutpoints
open Sequential

variable {profile : CFG.Profile}

/-- Generate a nonempty block obligation by executing the production ISA
semantics. A block stops at RET or its first cutpoint successor. Every ordinary
successor is composed automatically, without an interior invariant or a local
instruction proof supplied by the client. Both AF choices must satisfy it.

`Post` and `AllowedRead` are independent client contracts. Zero fuel, errors,
missing successors, atomic outcomes and syscall boundaries fail closed. This
profile inherits the checked CFG's read-only restriction. -/
def wp (graph : CFG.Graph) (base : Word) (Post : State → Prop)
    (AllowedRead : State → Read → Prop) (Inv : graph.Index → State → Prop)
    (rank : graph.Index → State → Nat) (budget : Nat) :
    Nat → graph.Index → State → Prop
  | 0, _, _ => False
  | fuel + 1, node, state => ∀ af : Bool,
    match execute state (graph.node node).instruction af with
    | .error _ => False
    | .ok observation =>
      (∀ read ∈ observation.reads, AllowedRead state read) ∧
      match observation.result with
      | .returned final => Post final
      | .next middle => ∃ destination : graph.Index,
          middle.rip = base + BitVec.ofNat 64 (graph.node destination).offset ∧
          if graph.cutpoint destination then
            Inv destination middle ∧ rank destination middle < budget
          else wp graph base Post AllowedRead Inv rank budget fuel destination middle
      | .atomic _ _ | .syscall _ => False

/-- The block-WP counterpart of a pure ordinary continuation. The destination
cutpoint, invariant and rank checks are retained exactly. -/
theorem wp_pure_next_iff (graph : CFG.Graph) (base : Word) (Post : State → Prop)
    (AllowedRead : State → Read → Prop) (Inv : graph.Index → State → Prop)
    (rank : graph.Index → State → Nat) (budget fuel : Nat) (node : graph.Index)
    (initial final : State)
    (effect : ∀ af, execute initial (graph.node node).instruction af = .ok ⟨.next final, []⟩) :
    wp graph base Post AllowedRead Inv rank budget (fuel + 1) node initial ↔
      ∃ destination : graph.Index,
        final.rip = base + BitVec.ofNat 64 (graph.node destination).offset ∧
        if graph.cutpoint destination then
          Inv destination final ∧ rank destination final < budget
        else wp graph base Post AllowedRead Inv rank budget fuel destination final := by
  simp [wp, effect]

/-- Only sparse cutpoints need client assertions and dynamic ranks. `blocks`
is a generated whole-block VC, including every intervening instruction, not a
renaming of `CFG.Annotations.localVC`. The finite depth bound is checked by
`CFG.Valid`; it is independent of the initial dynamic loop count. -/
structure Annotations (bytes : List Byte) (graph : CFG.Graph) (base : Word)
    (Post : State → Prop) (AllowedRead : State → Read → Prop) where
  Inv : graph.Index → State → Prop
  rank : graph.Index → State → Nat
  blocks : ∀ cut state, graph.cutpoint cut = true →
    CFG.At bytes graph base cut state → Inv cut state →
    wp graph base Post AllowedRead Inv rank (rank cut state)
      (graph.depth cut + 1) cut state

/-- Finite reflection for decidable client assertions. This enumerates both
AF values and all candidate CFG successors, using structural recursion on the
block bound. No external solver result is trusted. -/
def decidableWP (graph : CFG.Graph) (base : Word) (Post : State → Prop)
    (AllowedRead : State → Read → Prop) (Inv : graph.Index → State → Prop)
    (rank : graph.Index → State → Nat) (budget : Nat)
    (decPost : ∀ state, Decidable (Post state))
    (decReads : ∀ state read, Decidable (AllowedRead state read))
    (decInv : ∀ node state, Decidable (Inv node state))
    (fuel : Nat) (node : graph.Index) (initial : State) :
    Decidable (wp graph base Post AllowedRead Inv rank budget fuel node initial) := by
  letI (state : State) : Decidable (Post state) := decPost state
  letI (state : State) (read : Read) : Decidable (AllowedRead state read) := decReads state read
  letI (node : graph.Index) (state : State) : Decidable (Inv node state) := decInv node state
  induction fuel generalizing node initial with
  | zero => exact isFalse id
  | succ fuel induction =>
    change Decidable (∀ af : Bool, _)
    refine @Bool.instDecidableForallOfDecidablePred _ ?_
    intro af
    dsimp only
    cases effect : execute initial (graph.node node).instruction af with
    | error fault => exact isFalse id
    | ok observation =>
      simp only
      cases outcome : observation.result with
      | returned final => infer_instance
      | atomic event middle => infer_instance
      | syscall request => infer_instance
      | next middle =>
        letI (destination : graph.Index) :
            Decidable (wp graph base Post AllowedRead Inv rank budget fuel destination middle) :=
          induction destination middle
        infer_instance

variable {bytes : List Byte} {graph : CFG.Graph} {base : Word}
  {Post : State → Prop} {AllowedRead : State → Read → Prop}

/-- Discharge all interior obligations once, for every client and checked
binary. Residual generated WPs serve as internal ghost assertions. Current
code and RIP transport through actual steps; a supplied node cannot override
the bytes in executable RAM. -/
def Annotations.machineAnnotations
    (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : CFG.Valid bytes graph profile) : CFG.Annotations bytes graph base Post AllowedRead where
  Inv node state := CFG.At bytes graph base node state ∧ annotations.Inv node state
  rank := annotations.rank
  Interior _ budget node state := CFG.At bytes graph base node state ∧
    ∃ fuel, wp graph base Post AllowedRead annotations.Inv annotations.rank budget fuel node state
  binding _ _ _ _ inside := inside.1
  start cut state isCut admitted :=
    ⟨admitted.1, graph.depth cut + 1,
      annotations.blocks cut state isCut admitted.1 admitted.2⟩
  localVC _ budget node state inside af := by
    obtain ⟨⟨code, pc⟩, fuel, generated⟩ := inside
    cases fuel with
    | zero => exact False.elim generated
    | succ fuel =>
      have one := generated af
      cases effect : execute state (graph.node node).instruction af with
      | error fault => simp only [effect] at one
      | ok observation =>
        simp only [effect] at one
        refine ⟨observation, rfl, one.1, ?_⟩
        have after := one.2
        cases outcome : observation.result with
        | returned final => simpa only [outcome] using after
        | atomic event middle => simp only [outcome] at after
        | syscall request => simp only [outcome] at after
        | next middle =>
          simp only [outcome] at after
          obtain ⟨dest, nextPC, continuation⟩ := after
          have actual : Sequential.step af state = .ok observation := by
            rw [valid.step_eq_execute code node state rfl pc af]
            exact effect
          obtain ⟨actualDest, edge, actualPC, _, nextCode⟩ :=
            valid.next code node pc actual outcome
          have same : actualDest = dest := valid.wordOffset_injective
            ((BitVec.add_right_inj base).mp (actualPC.symm.trans nextPC))
          subst actualDest
          refine ⟨dest, edge, ?_⟩
          cases isCut : graph.cutpoint dest with
          | true =>
            simp only [isCut, ↓reduceIte] at continuation
            exact .inl ⟨rfl, ⟨⟨nextCode, nextPC⟩, continuation.1⟩, continuation.2⟩
          | false =>
            simp only [isCut] at continuation
            exact .inr ⟨rfl, ⟨nextCode, nextPC⟩, fuel, continuation⟩

/-- Reuse the existing generic cutpoint totality and prefix-safety theory. -/
def Annotations.certificate (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : CFG.Valid bytes graph profile) :
    Sequential.Cutpoints.Certificate valid.layout Post AllowedRead :=
  (annotations.machineAnnotations valid).certificate valid

/-- Construct a total actual execution for every AF stream. The instruction
bound is conservative; it counts retired model instructions, not wall time. -/
theorem Annotations.execution (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : CFG.Valid bytes graph profile) {entry : graph.Index} {initial : State}
    (isCut : graph.cutpoint entry = true) (binding : CFG.At bytes graph base entry initial)
    (admitted : annotations.Inv entry initial) (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧ Post result.state ∧
      result.instructions ≤ (graph.maxDepth + 1) * (annotations.rank entry initial + 1) :=
  (annotations.certificate valid).execution isCut ⟨binding, admitted⟩ choices

/-- The generated VC produces success of the production bounded evaluator;
there is no assumed successful run or external interpreter in its premises. -/
theorem Annotations.sound (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : CFG.Valid bytes graph profile) {entry : graph.Index} {initial : State}
    (isCut : graph.cutpoint entry = true) (binding : CFG.At bytes graph base entry initial)
    (admitted : annotations.Inv entry initial) (choices : Choices) :
    ∃ result, Sequential.run choices
        ((graph.maxDepth + 1) * (annotations.rank entry initial + 1)) initial = .ok result ∧
      Post result.state ∧
      result.instructions ≤ (graph.maxDepth + 1) * (annotations.rank entry initial + 1) :=
  (annotations.certificate valid).total isCut ⟨binding, admitted⟩ choices

theorem Annotations.all_executions (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : CFG.Valid bytes graph profile) {entry : graph.Index} {initial : State}
    (isCut : graph.cutpoint entry = true) (binding : CFG.At bytes graph base entry initial)
    (admitted : annotations.Inv entry initial) :
    Sequential.AllExecutions initial (fun result => Post result.state ∧
      result.instructions ≤ (graph.maxDepth + 1) * (annotations.rank entry initial + 1)) :=
  (annotations.certificate valid).all_executions isCut ⟨binding, admitted⟩

theorem Annotations.safe (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : CFG.Valid bytes graph profile) {entry : graph.Index} {initial : State}
    (isCut : graph.cutpoint entry = true) (binding : CFG.At bytes graph base entry initial)
    (admitted : annotations.Inv entry initial) : Sequential.Safe initial :=
  (annotations.certificate valid).safe isCut ⟨binding, admitted⟩

theorem Annotations.no_divergence (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : CFG.Valid bytes graph profile) {entry : graph.Index} {initial : State}
    (isCut : graph.cutpoint entry = true) (binding : CFG.At bytes graph base entry initial)
    (admitted : annotations.Inv entry initial) : ¬ Sequential.Diverges initial :=
  (annotations.certificate valid).no_divergence isCut ⟨binding, admitted⟩

theorem Annotations.no_fault_prefix (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : CFG.Valid bytes graph profile) {entry : graph.Index} {initial : State}
    (isCut : graph.cutpoint entry = true) (binding : CFG.At bytes graph base entry initial)
    (admitted : annotations.Inv entry initial) (choices : Choices) {fuel : Nat} {error : Error}
    (fault : Sequential.run choices fuel initial = .error error) : error = .exhaustedFuel :=
  (annotations.certificate valid).no_fault_prefix isCut ⟨binding, admitted⟩ choices fault

/-- Every reported operand read has its actual decoded origin, the client's
permission in the actual pre-state, and successful memory access. RET's stack
read is included. -/
theorem Annotations.read_origin (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : CFG.Valid bytes graph profile) {entry : graph.Index} {initial : State}
    (isCut : graph.cutpoint entry = true) (binding : CFG.At bytes graph base entry initial)
    (admitted : annotations.Inv entry initial) {choices : Choices} {result : Result}
    (execution : Sequential.Executes choices initial result) {read : Read} (member : read ∈ result.reads) :
    ∃ count before priorReads observation node, count < result.instructions ∧
      Sequential.Block choices initial before count priorReads ∧
      Sequential.step (choices count) before = .ok observation ∧
      read ∈ observation.reads ∧ CFG.At bytes graph base node before ∧
      AllowedRead before read ∧ OperandReadSucceeds before read := by
  let certificate := annotations.certificate valid
  have start := certificate.ghost_start isCut ⟨binding, admitted⟩
  obtain ⟨count, before, priorReads, observation, bound, block, actual, present,
    ghost, allowed, succeeded⟩ := certificate.execution_read_origin start execution member
  obtain ⟨source, budget, node, inside⟩ := ghost
  exact ⟨count, before, priorReads, observation, node, bound, block, actual, present,
    (annotations.machineAnnotations valid).binding source budget node before inside, allowed, succeeded⟩

end EDSL.X86.VCGen.Cutpoints
