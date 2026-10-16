/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CFGTransport
import EDSL.X86.Sequential.CutpointsSafety

namespace EDSL.X86.Sequential.CFG

/-- The annotation refers to current executable RAM and the actual RIP. -/
def At (bytes : List Byte) (graph : Graph) (base : Word)
    (node : graph.Index) (state : State) : Prop :=
  CodeAt state.memory base bytes ∧
    state.rip = base + BitVec.ofNat 64 (graph.node node).offset

/-- Checked finite graph facts instantiate the generic cutpoint composition
theorem. Dynamic invariants and ranks remain separate proof obligations. -/
def Valid.layout {bytes : List Byte} {graph : Graph} (valid : Valid bytes graph) :
    Cutpoints.Layout graph.Index where
  cutpoint := graph.cutpoint
  depth := graph.depth
  maxDepth := graph.maxDepth
  Edge := graph.Edge
  depth_bound node := (valid.nodes node).2.2.2
  depth_decrease {node dest} := valid.decreases node dest

/-- Local proof data for an independently supplied result and access contract.
Effects are proved for the decoded instruction. Actual step equations are
derived below from the checked bytes and current code/PC binding. -/
structure Annotations (bytes : List Byte) (graph : Graph) (base : Word)
    (Post : State → Prop) (AllowedRead : State → Read → Prop) where
  Inv : graph.Index → State → Prop
  rank : graph.Index → State → Nat
  Interior : graph.Index → Nat → graph.Index → State → Prop
  binding : ∀ source budget node state, Interior source budget node state →
    At bytes graph base node state
  start : ∀ cut state, graph.cutpoint cut = true → Inv cut state →
    Interior cut (rank cut state) cut state
  localVC : ∀ source budget node state, Interior source budget node state → ∀ af,
    ∃ observation, execute state (graph.node node).instruction af = .ok observation ∧
      (∀ read ∈ observation.reads, AllowedRead state read) ∧
      match observation.result with
      | .returned final => Post final
      | .next middle => ∃ dest, graph.Edge node dest ∧
          ((graph.cutpoint dest = true ∧ Inv dest middle ∧ rank dest middle < budget) ∨
           (graph.cutpoint dest = false ∧ Interior source budget dest middle))
      | .atomic _ _ | .syscall _ => False

/-- Local execute proofs become actual decoded machine-step proofs. Neither
the checker nor execution selects instructions through annotation data. -/
def Annotations.certificate {bytes : List Byte} {graph : Graph} {base : Word}
    {Post : State → Prop} {AllowedRead : State → Read → Prop}
    (annotations : Annotations bytes graph base Post AllowedRead) (valid : Valid bytes graph) :
    Cutpoints.Certificate valid.layout Post AllowedRead where
  Inv := annotations.Inv
  rank := annotations.rank
  Interior := annotations.Interior
  start := annotations.start
  localVC source budget node state inside af := by
    obtain ⟨code, pc⟩ := annotations.binding source budget node state inside
    obtain ⟨observation, effect, reads, after⟩ := annotations.localVC source budget node state inside af
    refine ⟨observation, ?_, reads, after⟩
    rw [valid.step_eq_execute code node state rfl pc af]
    exact effect

variable {bytes : List Byte} {graph : Graph} {base : Word}
  {Post : State → Prop} {AllowedRead : State → Read → Prop}

/-- Construct actual all-choice termination from local byte-bound obligations.
The input contains no assumed future run or precomputed successful result. -/
theorem Annotations.execution (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : Valid bytes graph) {initial : State} (admitted : annotations.Inv valid.entry initial)
    (choices : Choices) :
    ∃ result, Executes choices initial result ∧ Post result.state ∧
      result.instructions ≤ (graph.maxDepth + 1) * (annotations.rank valid.entry initial + 1) :=
  (annotations.certificate valid).execution (entry := valid.entry) valid.entry_cutpoint admitted choices

theorem Annotations.sound (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : Valid bytes graph) {initial : State} (admitted : annotations.Inv valid.entry initial)
    (choices : Choices) :
    ∃ result, run choices ((graph.maxDepth + 1) * (annotations.rank valid.entry initial + 1)) initial =
        .ok result ∧ Post result.state ∧
      result.instructions ≤ (graph.maxDepth + 1) * (annotations.rank valid.entry initial + 1) :=
  (annotations.certificate valid).total (entry := valid.entry) valid.entry_cutpoint admitted choices

theorem Annotations.all_executions (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : Valid bytes graph) {initial : State} (admitted : annotations.Inv valid.entry initial) :
    AllExecutions initial (fun result => Post result.state ∧
      result.instructions ≤ (graph.maxDepth + 1) * (annotations.rank valid.entry initial + 1)) :=
  (annotations.certificate valid).all_executions (entry := valid.entry) valid.entry_cutpoint admitted

theorem Annotations.safe (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : Valid bytes graph) {initial : State} (admitted : annotations.Inv valid.entry initial) :
    Safe initial := (annotations.certificate valid).safe (entry := valid.entry) valid.entry_cutpoint admitted

theorem Annotations.no_divergence (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : Valid bytes graph) {initial : State} (admitted : annotations.Inv valid.entry initial) :
    ¬ Diverges initial :=
  (annotations.certificate valid).no_divergence (entry := valid.entry) valid.entry_cutpoint admitted

/-- Actual read origins retain the checked code/PC annotation and the supplied
permission predicate in the real pre-instruction state. -/
theorem Annotations.read_origin (annotations : Annotations bytes graph base Post AllowedRead)
    (valid : Valid bytes graph) {initial : State} (admitted : annotations.Inv valid.entry initial)
    {choices : Choices} {result : Result} (execution : Executes choices initial result)
    {read : Read} (member : read ∈ result.reads) :
    ∃ count before priorReads observation node, count < result.instructions ∧
      Block choices initial before count priorReads ∧
        step (choices count) before = .ok observation ∧ read ∈ observation.reads ∧
          At bytes graph base node before ∧ AllowedRead before read ∧ OperandReadSucceeds before read := by
  let certificate := annotations.certificate valid
  have start := certificate.ghost_start (entry := valid.entry) valid.entry_cutpoint admitted
  obtain ⟨count, before, priorReads, observation, bound, block, actual, present,
    ghost, allowed, succeeded⟩ := certificate.execution_read_origin start execution member
  obtain ⟨source, budget, node, inside⟩ := ghost
  exact ⟨count, before, priorReads, observation, node, bound, block, actual, present,
    annotations.binding source budget node before inside, allowed, succeeded⟩

end EDSL.X86.Sequential.CFG
