/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Core

namespace EDSL.X86.VCGen
open Sequential

variable {profile : CFG.Profile}

/-- The checked read-only profile preserves the entire memory and both
permission maps for every terminating actual execution. Clients need not
decide extensional memory equality as part of their executable postcondition. -/
theorem execution_memory {bytes : List Byte} {graph : CFG.Graph}
    (valid : CFG.Valid bytes graph profile) {base : Word} {choices : Choices}
    {initial : State} {result : Result} (execution : Sequential.Executes choices initial result)
    (code : CodeAt initial.memory base bytes) (node : graph.Index)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset) :
    result.state.memory = initial.memory := by
  induction execution generalizing node with
  | @ret choices initial final reads actual =>
    exact (valid.returned code node pc actual rfl).2.1
  | @next choices initial middle result reads actual tail induction =>
    obtain ⟨destination, _, nextPC, memory, nextCode⟩ := valid.next code node pc actual rfl
    exact (induction nextCode destination nextPC).trans memory
  | @atomic choices initial middle result reads event actual tail induction =>
    exact False.elim (valid.no_atomic code node pc actual event middle rfl)

/-- Automatic whole-memory framing composes with arbitrary independently
chosen value, count and read contracts, including decidable contracts that
omit function-valued memory equality. -/
theorem run_sound_frame {bytes : List Byte} {graph : CFG.Graph} (valid : CFG.Valid bytes graph profile)
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    (code : CodeAt initial.memory base bytes)
    (pc : initial.rip = base + BitVec.ofNat 64 (graph.node node).offset)
    (vc : wp graph base AllowedRead fuel node initial Post) (choices : Choices) :
    ∃ result, Sequential.run choices fuel initial = .ok result ∧ Post result ∧
      result.state.memory = initial.memory ∧ result.instructions ≤ fuel ∧
      CheckedTrace AllowedRead choices initial result := by
  obtain ⟨result, actual, post, bound, trace⟩ := run_sound valid code pc vc choices
  exact ⟨result, actual, post, execution_memory valid (Sequential.run_sound actual) code node pc,
    bound, trace⟩

/-- The complete concrete-state checker also supplies the memory frame without
requiring an executable equality test on arbitrary memory functions. -/
theorem certifyWith_sound_frame {bytes : List Byte} {graph : CFG.Graph}
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    [Decidable (wp graph base AllowedRead fuel node initial Post)]
    (accepted : certifyWith profile bytes graph base AllowedRead fuel node initial Post = true)
    (choices : Choices) :
    ∃ result, Sequential.run choices fuel initial = .ok result ∧ Post result ∧
      result.state.memory = initial.memory ∧ result.instructions ≤ fuel ∧
      CheckedTrace AllowedRead choices initial result := by
  have parts : CFG.checkWith profile bytes graph = true ∧
      ELF.checkCode initial.memory base bytes = true ∧
      initial.rip = base + BitVec.ofNat 64 (graph.node node).offset ∧
      check graph base AllowedRead fuel node initial Post = true := by
    simpa only [certifyWith, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using accepted
  exact run_sound_frame (CFG.checkWith_sound parts.1)
    (ELF.checkCode_sound _ _ _ parts.2.1) parts.2.2.1
    (of_decide_eq_true parts.2.2.2) choices

theorem certify_sound_frame {bytes : List Byte} {graph : CFG.Graph}
    {base : Word} {AllowedRead : State → Read → Prop} {fuel : Nat}
    {node : graph.Index} {initial : State} {Post : Contract}
    [Decidable (wp graph base AllowedRead fuel node initial Post)]
    (accepted : certify bytes graph base AllowedRead fuel node initial Post = true)
    (choices : Choices) :
    ∃ result, Sequential.run choices fuel initial = .ok result ∧ Post result ∧
      result.state.memory = initial.memory ∧ result.instructions ≤ fuel ∧
      CheckedTrace AllowedRead choices initial result :=
  certifyWith_sound_frame accepted choices

end EDSL.X86.VCGen
