/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Choices
import EDSL.Grading.PolicyFor

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.VCGen
open Sequential

variable {profile : CFG.Profile}

/-- Every actual continuing vector prefix retains full initial memory, actual
executable bytes and a checked node PC with a positive residual WP. The remaining
contract prepends the prefix's exact instruction count and ordered read trace.

The induction follows production `BlockWith`, including its atomic constructor.
An atomic prefix contradicts `wpWith` at that actual step; neither a successful
future execution nor a separate exclusion premise is assumed. -/
theorem block_residualWith {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Valid bytes graph profile) {base : Word}
    {AllowedRead : State → Read → Prop} {fuel : Nat} {node : graph.Index}
    {initial before : State} {Post : Contract} {choices : ChoiceStream FlagChoices}
    {count : Nat} {reads : List Read}
    (block : BlockWith choices initial before count reads)
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wpWith graph base AllowedRead fuel node initial Post) :
    before.memory = initial.memory ∧ CodeAt before.memory base bytes ∧
      ∃ remaining destination, count + remaining = fuel ∧ 0 < remaining ∧
        before.rip = base + BitVec.ofNat 64 (graph.node destination).offset ∧
        wpWith graph base AllowedRead remaining destination before
          (fun result => Post (result.prepend count reads)) := by
  induction block generalizing fuel node Post with
  | nil =>
    refine ⟨rfl, code, fuel, node, Nat.zero_add fuel, ?_, pc, ?_⟩
    · cases fuel with
      | zero => exact False.elim vc
      | succ fuel => exact Nat.zero_lt_succ fuel
    · simpa only [Result.prepend_zero] using vc
  | @next choices initial middle _before count reads _rest actual _tail induction =>
    cases fuel with
    | zero => exact False.elim vc
    | succ fuel =>
      have decoded := valid.decoded code node initial rfl pc
      have effect : executeWith initial (graph.node node).instruction (choices 0) =
          .ok ⟨.next middle, reads⟩ := by
        rwa [stepWith_eq_executeWith (choices 0) decoded] at actual
      have one := vc (choices 0)
      simp only [effect] at one
      obtain ⟨destination, nextPC, nextVC⟩ := one.2
      have memory : middle.memory = initial.memory :=
        CFG.executeWith_memory (valid.nodes node).2.2.1 effect
      have nextCode : CodeAt middle.memory base bytes := by rwa [memory]
      obtain ⟨framed, finalCode, remaining, finalNode, sum, positive, finalPC, residual⟩ :=
        induction nextCode nextPC nextVC
      refine ⟨framed.trans memory, finalCode, remaining, finalNode, ?_,
        positive, finalPC, ?_⟩
      · calc
          count + 1 + remaining = count + remaining + 1 := Nat.add_right_comm _ _ _
          _ = fuel + 1 := congrArg (fun budget : Nat => budget + 1) sum
      · simpa only [Result.prepend_prepend, Nat.add_comm 1 count] using residual
  | @atomic choices initial middle _before _count reads _rest event actual _tail _induction =>
    cases fuel with
    | zero => exact False.elim vc
    | succ fuel =>
      have decoded := valid.decoded code node initial rfl pc
      have effect : executeWith initial (graph.node node).instruction (choices 0) =
          .ok ⟨.atomic event middle, reads⟩ := by
        rwa [stepWith_eq_executeWith (choices 0) decoded] at actual
      have one := vc (choices 0)
      rw [effect] at one
      exact False.elim one.2

/-- A proved bounded vector WP establishes the semantic policy at every actual
continuing vector prefix. `Current` follows from complete initial memory
equality, including byte presence and executable/writable maps. Logical read
permissions are required in each actual pre-state, without changing their
meaning or replacing them with address bounds.

Code and execution concern stable ordinary modeled RAM. Native mappings,
lifetimes, interference control and physical CPU/OS correspondence remain
environmental obligations beyond this theorem. -/
theorem readOnly_policyWith {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Valid bytes graph profile) {base : Word}
    {AllowedRead : State → Read → Prop} {fuel : Nat} {node : graph.Index}
    {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wpWith graph base AllowedRead fuel node initial Post)
    (Current : State → Prop)
    (current : ∀ before, before.memory = initial.memory → Current before) :
    Grading.ReadOnlyPolicyFor .flags initial Current AllowedRead := by
  intro before reachable
  obtain ⟨choices, count, priorReads, block⟩ := reachable
  obtain ⟨memory, currentCode, remaining, destination, _, positive, currentPC, residual⟩ :=
    block_residualWith valid block code pc vc
  have decoded := valid.decoded currentCode destination before rfl currentPC
  have readOnly := (valid.nodes destination).2.2.1
  refine ⟨current before memory,
    ⟨(graph.node destination).instruction, decoded, readOnly⟩, ?_⟩
  intro vector
  cases remaining with
  | zero => cases positive
  | succ remaining =>
    have one := residual vector
    cases effect : executeWith before (graph.node destination).instruction vector with
    | error fault => simp only [effect] at one
    | ok observation =>
      simp only [effect] at one
      have actual : stepWith vector before = .ok observation := by
        rw [stepWith_eq_executeWith vector decoded]
        exact effect
      refine ⟨observation, actual, ?_, CFG.executeWith_memory readOnly effect⟩
      intro read member
      exact ⟨one.1 read member, stepWith_reads_succeed actual read member⟩

/-- Canonical policy with complete present-memory equality as its current-state
predicate, for later independently proved resource transport. No decidable
equality on the memory functions or extra execution premise is required. -/
theorem readOnly_policy_memoryWith {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Valid bytes graph profile) {base : Word}
    {AllowedRead : State → Read → Prop} {fuel : Nat} {node : graph.Index}
    {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wpWith graph base AllowedRead fuel node initial Post) :
    Grading.ReadOnlyPolicyFor .flags initial
      (fun before => before.memory = initial.memory) AllowedRead :=
  readOnly_policyWith valid code pc vc _ (fun _ memory => memory)

end EDSL.X86.VCGen
