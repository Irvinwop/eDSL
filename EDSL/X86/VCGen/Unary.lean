/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Core
import EDSL.X86.VCGen.Cutpoints
import EDSL.X86.Sequential.Unary

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.VCGen
open Sequential

/-- Reusable NEG32 WP over any checked-graph node and independently selected
postcondition. The destination is read in the prestate, including RSP. -/
theorem wp_negReg32_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (state : State) (Post : Contract) (destination : Register) (prefixed : Bool)
    (instruction : (graph.node node).instruction = .negReg32 destination prefixed) :
    let final := { state.writeRegister destination
      ((-((state.registers destination).setWidth 32)).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 (if prefixed then 3 else 2)
      flags := cmpFlags32 state.flags 0 ((state.registers destination).setWidth 32) }
    wp graph base AllowedRead (fuel + 1) node state Post ↔
      ∃ next : graph.Index,
        final.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        wp graph base AllowedRead fuel next final (fun result => Post (result.prepend 1 [])) := by
  apply wp_pure_next_iff
  intro af
  rw [instruction, execute_negReg32]
  rfl

/-- BSWAP64 preserves all incoming flags and contributes no operand read.
Successor and continuation obligations are the existing bounded WP. -/
theorem wp_bswapReg64_iff (graph : CFG.Graph) (base : Word)
    (AllowedRead : State → Read → Prop) (fuel : Nat) (node : graph.Index)
    (state : State) (Post : Contract) (destination : Register)
    (instruction : (graph.node node).instruction = .bswapReg64 destination) :
    let final := { state.writeRegister destination
      (WordMath.byteSwap64 (state.registers destination)) with rip := state.rip + 3 }
    wp graph base AllowedRead (fuel + 1) node state Post ↔
      ∃ next : graph.Index,
        final.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        wp graph base AllowedRead fuel next final (fun result => Post (result.prepend 1 [])) := by
  apply wp_pure_next_iff
  intro af
  rw [instruction, execute_bswapReg64]

namespace Cutpoints

theorem wp_negReg32_iff (graph : CFG.Graph) (base : Word) (Post : State → Prop)
    (AllowedRead : State → Read → Prop) (Inv : graph.Index → State → Prop)
    (rank : graph.Index → State → Nat) (budget fuel : Nat) (node : graph.Index)
    (state : State) (destination : Register) (prefixed : Bool)
    (instruction : (graph.node node).instruction = .negReg32 destination prefixed) :
    let final := { state.writeRegister destination
      ((-((state.registers destination).setWidth 32)).setWidth 64) with
      rip := state.rip + BitVec.ofNat 64 (if prefixed then 3 else 2)
      flags := cmpFlags32 state.flags 0 ((state.registers destination).setWidth 32) }
    wp graph base Post AllowedRead Inv rank budget (fuel + 1) node state ↔
      ∃ next : graph.Index,
        final.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        if graph.cutpoint next then Inv next final ∧ rank next final < budget
        else wp graph base Post AllowedRead Inv rank budget fuel next final := by
  apply wp_pure_next_iff
  intro af
  rw [instruction, execute_negReg32]
  rfl

theorem wp_bswapReg64_iff (graph : CFG.Graph) (base : Word) (Post : State → Prop)
    (AllowedRead : State → Read → Prop) (Inv : graph.Index → State → Prop)
    (rank : graph.Index → State → Nat) (budget fuel : Nat) (node : graph.Index)
    (state : State) (destination : Register)
    (instruction : (graph.node node).instruction = .bswapReg64 destination) :
    let final := { state.writeRegister destination
      (WordMath.byteSwap64 (state.registers destination)) with rip := state.rip + 3 }
    wp graph base Post AllowedRead Inv rank budget (fuel + 1) node state ↔
      ∃ next : graph.Index,
        final.rip = base + BitVec.ofNat 64 (graph.node next).offset ∧
        if graph.cutpoint next then Inv next final ∧ rank next final < budget
        else wp graph base Post AllowedRead Inv rank budget fuel next final := by
  apply wp_pure_next_iff
  intro af
  rw [instruction, execute_bswapReg64]

end Cutpoints
end EDSL.X86.VCGen
