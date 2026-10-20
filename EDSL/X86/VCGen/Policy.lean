/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Core
import EDSL.Grading.Policy

set_option warningAsError true

namespace EDSL.X86.VCGen
open Sequential

/-- Every actual continuing prefix retains executable code, its checked PC,
complete initial memory and the residual generated WP. The residual contract
accounts for the prefix's actual cost and reads. In particular, a continuing
prefix cannot consume all the fuel of a proved returning WP.

This induction follows the production `Sequential.Block`, including arbitrary
AF choices. It assumes neither a future successful run nor a prefix policy. -/
theorem block_residual {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Valid bytes graph) {base : Word}
    {AllowedRead : State → Read → Prop} {fuel : Nat} {node : graph.Index}
    {initial before : State} {Post : Contract} {choices : Choices}
    {count : Nat} {reads : List Read}
    (block : Sequential.Block choices initial before count reads)
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base AllowedRead fuel node initial Post) :
    before.memory = initial.memory ∧ CodeAt before.memory base bytes ∧
      ∃ remaining destination, count + remaining = fuel ∧ 0 < remaining ∧
        before.rip = base + BitVec.ofNat 64 (graph.node destination).offset ∧
        wp graph base AllowedRead remaining destination before
          (fun result => Post (result.prepend count reads)) := by
  induction block generalizing fuel node Post with
  | nil =>
    refine ⟨rfl, code, fuel, node, by omega, ?_, pc, ?_⟩
    · cases fuel with
      | zero => exact False.elim vc
      | succ fuel => omega
    · simpa only [Result.prepend_zero] using vc
  | @next choices initial middle before count reads rest actual tail induction =>
    cases fuel with
    | zero => exact False.elim vc
    | succ fuel =>
      have effect : execute initial (graph.node node).instruction (choices 0) =
          .ok ⟨.next middle, reads⟩ := by
        rwa [valid.step_eq_execute code node initial rfl pc] at actual
      have one := vc (choices 0)
      simp only [effect] at one
      obtain ⟨destination, nextPC, nextVC⟩ := one.2
      obtain ⟨_, _, _, memory, nextCode⟩ := valid.next code node pc actual rfl
      obtain ⟨framed, finalCode, remaining, finalNode, sum, positive, finalPC, residual⟩ :=
        induction nextCode nextPC nextVC
      refine ⟨framed.trans memory, finalCode, remaining, finalNode, by omega,
        positive, finalPC, ?_⟩
      simpa only [Result.prepend_prepend, Nat.add_comm 1 count] using residual
  | @atomic choices initial middle before count reads rest event actual tail induction =>
    exact False.elim (valid.no_atomic code node pc actual event middle rfl)

/-- A proved bounded WP establishes the existing semantic grading policy at
every real continuing prefix. `Current` must follow from complete initial
memory equality; this is an explicit transport requirement, not an assumption
of future authority. It covers resource predicates whose original OS world,
ownership epochs, permissions and code/caller loans survive unchanged RAM.

The code binding and steps refer to stable ordinary modeled RAM. Relating that
RAM to a native mapping, its lifetime, interference control and physical CPU
behavior remains the caller's environmental obligation. -/
theorem readOnly_policy {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Valid bytes graph) {base : Word}
    {AllowedRead : State → Read → Prop} {fuel : Nat} {node : graph.Index}
    {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base AllowedRead fuel node initial Post)
    (Current : State → Prop)
    (current : ∀ before, before.memory = initial.memory → Current before) :
    Grading.ReadOnlyPolicy initial Current AllowedRead := by
  intro before reachable
  obtain ⟨choices, count, priorReads, block⟩ := reachable
  obtain ⟨memory, currentCode, remaining, destination, _, positive, currentPC, residual⟩ :=
    block_residual valid block code pc vc
  have decoded := valid.decoded currentCode destination before rfl currentPC
  have readOnly := (valid.nodes destination).2.2.1
  refine ⟨current before memory,
    ⟨(graph.node destination).instruction, decoded, readOnly⟩, ?_⟩
  intro af
  cases remaining with
  | zero => omega
  | succ remaining =>
    have one := residual af
    cases effect : execute before (graph.node destination).instruction af with
    | error fault => simp only [effect] at one
    | ok observation =>
      simp only [effect] at one
      have actual : Sequential.step af before = .ok observation := by
        rw [Sequential.step_eq_execute af decoded]
        exact effect
      refine ⟨observation, actual, ?_, ?_⟩
      · intro read member
        exact ⟨one.1 read member, observed_reads_succeed actual read member⟩
      · obtain ⟨after, next | ⟨returned, _⟩⟩ := CFG.execute_result readOnly effect
        · rw [next]
          exact CFG.execute_next_memory readOnly effect next
        · rw [returned]
          exact CFG.execute_returned_memory readOnly effect returned

/-- Canonical raw policy for later transport through an independently proved
current-resource admission. No decidable equality on memory functions is used. -/
theorem readOnly_policy_memory {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Valid bytes graph) {base : Word}
    {AllowedRead : State → Read → Prop} {fuel : Nat} {node : graph.Index}
    {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base AllowedRead fuel node initial Post) :
    Grading.ReadOnlyPolicy initial (fun before => before.memory = initial.memory) AllowedRead :=
  readOnly_policy valid code pc vc _ (fun _ memory => memory)

end EDSL.X86.VCGen
