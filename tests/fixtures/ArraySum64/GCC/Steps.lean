/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.ArraySum64.GCC.Invariant

set_option warningAsError true

namespace EDSL.ArraySum64.GCC
open X86 X86.Sequential

theorem test_pc {initial values remaining consumed state}
    (header : Header initial values remaining consumed state) :
    (test state).rip = initial.rip + 7 := by
  simp only [test,header.pc,BitVec.add_assoc]
  rfl

theorem added_pc (base : Word) (state : State) (value : Word) :
    (added base state value).rip = base + 13 := by
  simp only [added,addOperand,body,atPC,edit,BitVec.add_assoc]
  rfl

theorem advanced_pc (base : Word) (state : State) (value : Word) :
    (advanced base state value).rip = base + 16 := by
  simp only [advanced,increment,edit,added_pc,BitVec.add_assoc]
  rfl

theorem moved_pc (base : Word) (state : State) :
    (moved base state).rip = base + 21 := by
  simp only [moved,moveResult,exiting,atPC,edit,BitVec.add_assoc]
  rfl

theorem prefix_block {initial values target} (pre : Pre bytes initial values target) (choices : Choices) :
    Sequential.Block choices initial (initialized initial (choices 0) ((choices.drop 1) 0)) 2 [] := by
  have first := (step_eq_execute (choices 0) (decode pre.code .clearIndex (by simp [offset]))).trans
    (execute_clear initial .rax (choices 0))
  have code : CodeAt (clear initial .rax (choices 0)).memory initial.rip bytes := pre.code
  have pc : (clear initial .rax (choices 0)).rip = initial.rip + 2 := rfl
  have second := (step_eq_execute ((choices.drop 1) 0) (decode code .clearValue pc)).trans
    (execute_clear _ .rdx ((choices.drop 1) 0))
  exact Sequential.Block.next first (Sequential.Block.next second Sequential.Block.nil)

theorem test_step {initial values remaining consumed state target}
    (header : Header initial values remaining consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af state = .ok ⟨.next (test state),[]⟩ :=
  (step_eq_execute af (decode (header.frame.code pre.code) .header header.pc)).trans
    (execute_test state af)

theorem exit_step {initial values consumed state target}
    (header : Header initial values [] consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af (test state) = .ok ⟨.next (exiting initial.rip state),[]⟩ := by
  have frame := header.frame.trans (frame_test state)
  have zero : (test state).flags.getLsbD 6 = true := by simpa using header.tested_zero pre
  exact (step_eq_execute af (decode (frame.code pre.code) .guard (test_pc header))).trans
    (guard_exit (frame.code pre.code) (test_pc header) zero af)

theorem body_step {initial values value rest consumed state target}
    (header : Header initial values (value :: rest) consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af (test state) = .ok ⟨.next (body initial.rip state),[]⟩ := by
  have frame := header.frame.trans (frame_test state)
  have nonzero : (test state).flags.getLsbD 6 = false := by simpa using header.tested_zero pre
  exact (step_eq_execute af (decode (frame.code pre.code) .guard (test_pc header))).trans
    (guard_body (test_pc header) nonzero af)

theorem add_step {initial values value rest consumed state target}
    (header : Header initial values (value :: rest) consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af (body initial.rip state) =
      .ok ⟨.next (added initial.rip state value),
        [⟨.data,initial.registers .rdi + BitVec.ofNat 64 (8 * consumed),8⟩]⟩ := by
  have frame := header.frame.trans (frame_body initial.rip state)
  have actual := (step_eq_execute af (decode (frame.code pre.code) .add rfl)).trans
    (execute_add (body_operand header pre) af)
  have address : (Address.indexed .rdi .rax 3).eval (body initial.rip state) =
      initial.registers .rdi + BitVec.ofNat 64 (8 * consumed) := by
    change (Address.indexed .rdi .rax 3).eval state = _
    exact indexed_address header pre
  simpa only [address,added] using actual

theorem increment_step {initial values value rest consumed state target}
    (header : Header initial values (value :: rest) consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af (added initial.rip state value) =
      .ok ⟨.next (advanced initial.rip state value),[]⟩ :=
  (step_eq_execute af (decode ((header.frame.trans (frame_added initial.rip state value)).code pre.code)
    .increment (added_pc ..))).trans (execute_increment _ af)

theorem back_step {initial values value rest consumed state target}
    (header : Header initial values (value :: rest) consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af (advanced initial.rip state value) =
      .ok ⟨.next (cycle initial.rip state value),[]⟩ := by
  have frame := header.frame.trans (frame_advanced initial.rip state value)
  exact (step_eq_execute af (decode (frame.code pre.code) .back (advanced_pc ..))).trans
    (back_edge (frame.code pre.code) (advanced_pc ..) af)

theorem move_step {initial values consumed state target}
    (header : Header initial values [] consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af (exiting initial.rip state) =
      .ok ⟨.next (moved initial.rip state),[]⟩ :=
  (step_eq_execute af (decode ((header.frame.trans (frame_exiting initial.rip state)).code pre.code)
    .move rfl)).trans (execute_move _ af)

theorem ret_step {initial values remaining consumed state target}
    (header : Header initial values remaining consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af (moved initial.rip state) =
      .ok ⟨.returned (finish (moved initial.rip state) target),[⟨.stack,initial.registers .rsp,8⟩]⟩ := by
  have frame := header.frame.trans (frame_moved initial.rip state)
  have read : readWord (moved initial.rip state).memory
      ((moved initial.rip state).registers .rsp) = .ok target := by
    rw [frame.memory,frame.stack]
    exact pre.stack
  have actual := (step_eq_execute af (decode (frame.code pre.code) .ret (moved_pc ..))).trans
    (execute_ret read pre.canonicalTarget af)
  simpa only [frame.stack] using actual

/-- One actual CMP/JE/ADD/INC/JMP cycle. Each step consumes its own AF choice. -/
theorem iteration_block {initial values value rest consumed state target}
    (header : Header initial values (value :: rest) consumed state) (pre : Pre bytes initial values target)
    (choices : Choices) : Sequential.Block choices state (cycle initial.rip state value) 5
      [⟨.data,initial.registers .rdi + BitVec.ofNat 64 (8 * consumed),8⟩] := by
  exact Sequential.Block.next (test_step header pre (choices 0))
    (Sequential.Block.next (body_step header pre ((choices.drop 1) 0))
      (Sequential.Block.next (add_step header pre (((choices.drop 1).drop 1) 0))
        (Sequential.Block.next (increment_step header pre ((((choices.drop 1).drop 1).drop 1) 0))
          (Sequential.Block.next (back_step header pre (((((choices.drop 1).drop 1).drop 1).drop 1) 0))
            Sequential.Block.nil))))

end EDSL.ArraySum64.GCC
