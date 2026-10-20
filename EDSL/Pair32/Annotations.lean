/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Pair32.Phases
import EDSL.Pair32.Steps
import EDSL.Pair32.Resources

namespace EDSL.Pair32
open X86

theorem header_instruction (loop : Loop) :
    (graph.node (headerIndex loop)).instruction = .test64 loop.counter loop.counter := by
  cases loop <;> rfl
theorem tested_instruction (loop : Loop) :
    (graph.node (testedIndex loop)).instruction = .je 11 := by cases loop <;> rfl
theorem body_instruction (loop : Loop) :
    (graph.node (bodyIndex loop)).instruction = .addMem32 .rax (.base loop.pointer) := by
  cases loop <;> rfl
theorem loaded_instruction (loop : Loop) :
    (graph.node (loadedIndex loop)).instruction = .dec64 loop.counter := by cases loop <;> rfl
theorem decremented_instruction (loop : Loop) :
    (graph.node (decrementedIndex loop)).instruction = .addImm64 loop.pointer 4 := by cases loop <;> rfl
theorem advanced_instruction (loop : Loop) :
    (graph.node (advancedIndex loop)).instruction = .jmp 240 := by cases loop <;> rfl

theorem header_cutpoint (loop : Loop) : graph.cutpoint (headerIndex loop) = true := by
  cases loop <;> decide
theorem tested_notcut (loop : Loop) : graph.cutpoint (testedIndex loop) = false := by cases loop <;> decide
theorem body_notcut (loop : Loop) : graph.cutpoint (bodyIndex loop) = false := by cases loop <;> decide
theorem loaded_notcut (loop : Loop) : graph.cutpoint (loadedIndex loop) = false := by cases loop <;> decide
theorem decremented_notcut (loop : Loop) : graph.cutpoint (decrementedIndex loop) = false := by
  cases loop <;> decide
theorem advanced_notcut (loop : Loop) : graph.cutpoint (advancedIndex loop) = false := by
  cases loop <;> decide

theorem header_edge (loop : Loop) : graph.Edge (headerIndex loop) (testedIndex loop) := by
  cases loop <;> decide
theorem tested_body_edge (loop : Loop) : graph.Edge (testedIndex loop) (bodyIndex loop) := by
  cases loop <;> decide
theorem body_edge (loop : Loop) : graph.Edge (bodyIndex loop) (loadedIndex loop) := by
  cases loop <;> decide
theorem loaded_edge (loop : Loop) : graph.Edge (loadedIndex loop) (decrementedIndex loop) := by
  cases loop <;> decide
theorem decremented_edge (loop : Loop) : graph.Edge (decrementedIndex loop) (advancedIndex loop) := by
  cases loop <;> decide
theorem advanced_edge (loop : Loop) : graph.Edge (advancedIndex loop) (headerIndex loop) := by
  cases loop <;> decide

/-- Instantiate the reusable byte-bound local obligations for an independent
two-list sum and an independently supplied current read-permission predicate. -/
def annotations {initial : State} {valuesA valuesB : List (BitVec 32)} {target : Word}
    (pre : Pre bytes initial valuesA valuesB target) (Access : Sequential.Read → Prop)
    (permission : ∀ read ∈ operandReads initial valuesA valuesB, Access read) :
    Sequential.CFG.Annotations bytes graph initial.rip (Post initial valuesA valuesB target)
      (Allowed initial Access) where
  Inv := Invariant initial valuesA valuesB target
  rank := rank valuesA.length valuesB.length
  Interior := Phase initial valuesA valuesB target
  binding source amount node state inside := ⟨by rw [inside.memory]; exact pre.code, inside.pc⟩
  start cut state isCut admitted := by
    cases admitted with
    | entry accepted => exact Phase.entry accepted
    | loop header => simpa only [rank_header header] using Phase.header (target := target) header
  localVC source amount node state inside af := by
    cases inside with
    | entry accepted =>
      let ready := initialized accepted af
      refine ⟨⟨.next (clear initial af), []⟩, rfl, by simp, headerIndex .first,
        by decide, .inl ⟨header_cutpoint .first, .loop ready, ?_⟩⟩
      rw [rank_header ready]
      change valuesA.length + valuesB.length + 1 < valuesA.length + valuesB.length + 2
      omega
    | @header loop state header =>
      refine ⟨⟨.next (test loop state af), []⟩, ?_, by simp, testedIndex loop,
        header_edge loop, .inr ⟨tested_notcut loop, .tested header af⟩⟩
      rw [header_instruction, Sequential.execute_test64, BitVec.and_self]
      rfl
    | @tested loop state header previous =>
      by_cases zero : header.count = 0
      · cases loop with
        | first =>
          let next := switchHeader pre header zero previous
          refine ⟨⟨.next (exitState .first initial.rip state previous), []⟩,
            ?_, by simp, headerIndex .second, by decide,
            .inl ⟨header_cutpoint .second, .loop next, ?_⟩⟩
          · exact guard_exit pre header zero previous af
          · rw [rank_header next]
            change valuesB.length < header.count + valuesB.length + 1
            omega
        | second =>
          exact ⟨⟨.next (exitState .second initial.rip state previous), []⟩,
            guard_exit pre header zero previous af, by simp, ⟨13, by decide⟩, by decide,
            .inr ⟨by decide, .returning header zero previous⟩⟩
      · obtain ⟨element⟩ := header.element (by omega)
        refine ⟨⟨.next (body loop initial.rip state previous), []⟩, ?_, by simp,
          bodyIndex loop, tested_body_edge loop, .inr ⟨body_notcut loop, .body header element previous⟩⟩
        rw [tested_instruction]
        exact guard_body header element previous af
    | @body loop state header element previous =>
      refine ⟨⟨.next (load (body loop initial.rip state previous) element.first),
        [⟨.data, state.registers loop.pointer, 4⟩]⟩, ?_, ?_, loadedIndex loop,
        body_edge loop, .inr ⟨loaded_notcut loop, .loaded header element previous⟩⟩
      · rw [body_instruction, Sequential.execute_addMem32]
        simp only [Sequential.Address.eval, header_operand header element previous, ok_bind, pure_ok]
        rfl
      · intro read member
        have same : read = ⟨.data, state.registers loop.pointer, 4⟩ := List.mem_singleton.mp member
        subst read
        exact ⟨permission _ (header_read_member header element), header.frame.memory⟩
    | @loaded loop state header element previous =>
      refine ⟨⟨.next (decrement loop (load (body loop initial.rip state previous) element.first)), []⟩,
        ?_, by simp, decrementedIndex loop, loaded_edge loop,
        .inr ⟨decremented_notcut loop, .decremented header element previous⟩⟩
      rw [loaded_instruction]
      rfl
    | @decremented loop state header element previous =>
      refine ⟨⟨.next (advance loop (decrement loop (load (body loop initial.rip state previous) element.first))), []⟩,
        ?_, by simp, advancedIndex loop, decremented_edge loop,
        .inr ⟨advanced_notcut loop, .advanced header element previous⟩⟩
      rw [decremented_instruction]
      rfl
    | @advanced loop state header element previous =>
      let next := nextHeader header element previous
      refine ⟨⟨.next (cycleState loop initial.rip state previous element.first), []⟩,
        ?_, by simp, headerIndex loop, advanced_edge loop,
        .inl ⟨header_cutpoint loop, .loop next, ?_⟩⟩
      · rw [advanced_instruction]
        exact back_edge pre header element previous af
      · rw [rank_header next]
        have count := element.count
        cases loop <;> change budget _ element.rest valuesB.length < budget _ header.count valuesB.length
        all_goals simp only [budget]; omega
    | @returning state header zero previous =>
      refine ⟨⟨.returned (finish (exitState .second initial.rip state previous) target),
        [⟨.stack, initial.registers .rsp, 8⟩]⟩, zero_return pre header previous af, ?_,
        zero_post header zero previous⟩
      intro read member
      have same : read = ⟨.stack, initial.registers .rsp, 8⟩ := List.mem_singleton.mp member
      subst read
      exact ⟨permission _ (stack_read_member initial valuesA valuesB), header.frame.memory⟩

end EDSL.Pair32
