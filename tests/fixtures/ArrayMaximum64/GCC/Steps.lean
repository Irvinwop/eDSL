/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.ArrayMaximum64.GCC.Invariant

set_option warningAsError true

namespace EDSL.ArrayMaximum64.GCC
open X86 X86.Sequential

theorem test_pc {initial values remaining consumed state}
    (header : Header initial values remaining consumed state) :
    (test state).rip = initial.rip + 7 := by
  simp only [test,header.pc,BitVec.add_assoc]
  rfl

theorem loaded_pc (base : Word) (state : State) (value : Word) :
    (loaded base state value).rip = base + 13 := by
  simp only [loaded,load,body,atPC,edit,BitVec.add_assoc]
  rfl

theorem compared_pc (base : Word) (state : State) (value : Word) :
    (compared base state value).rip = base + 16 := by
  simp only [compared,compare,loaded_pc,BitVec.add_assoc]
  rfl

theorem selected_pc (base : Word) (state : State) (value : Word) :
    (selected base state value).rip = base + 20 := by
  simp only [selected,select,edit,compared_pc,BitVec.add_assoc]
  rfl

theorem advanced_pc (base : Word) (state : State) (value : Word) :
    (advanced base state value).rip = base + 23 := by
  simp only [advanced,increment,edit,selected_pc,BitVec.add_assoc]
  rfl

theorem prefix_block {initial values target} (pre : Pre bytes initial values target) (choices : Choices) :
    Sequential.Block choices initial (initialized initial (choices 0) ((choices.drop 1) 0)) 2 [] := by
  have first := (step_eq_execute (choices 0) (decode pre.code .clearIndex (by simp [offset]))).trans
    (execute_clear initial .rdx (choices 0))
  have code : CodeAt (clear initial .rdx (choices 0)).memory initial.rip bytes := pre.code
  have pc : (clear initial .rdx (choices 0)).rip = initial.rip + 2 := rfl
  have second := (step_eq_execute ((choices.drop 1) 0) (decode code .clearValue pc)).trans
    (execute_clear _ .rax ((choices.drop 1) 0))
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

theorem load_step {initial values value rest consumed state target}
    (header : Header initial values (value :: rest) consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af (body initial.rip state) =
      .ok ⟨.next (loaded initial.rip state value),
        [⟨.data,initial.registers .rdi + BitVec.ofNat 64 (8 * consumed),8⟩]⟩ := by
  have frame := header.frame.trans (frame_body initial.rip state)
  have actual := (step_eq_execute af (decode (frame.code pre.code) .load rfl)).trans
    (execute_load (body_operand header pre) af)
  have address : (Address.indexed .rdi .rdx 3).eval (body initial.rip state) =
      initial.registers .rdi + BitVec.ofNat 64 (8 * consumed) := by
    change (Address.indexed .rdi .rdx 3).eval state = _
    exact indexed_address header pre
  simpa only [address,loaded] using actual

theorem compare_step {initial values value rest consumed state target}
    (header : Header initial values (value :: rest) consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af (loaded initial.rip state value) =
      .ok ⟨.next (compared initial.rip state value),[]⟩ :=
  (step_eq_execute af (decode ((header.frame.trans (frame_loaded initial.rip state value)).code pre.code)
    .compare (loaded_pc ..))).trans (execute_compare _ af)

theorem select_step {initial values value rest consumed state target}
    (header : Header initial values (value :: rest) consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af (compared initial.rip state value) =
      .ok ⟨.next (selected initial.rip state value),[]⟩ :=
  (step_eq_execute af (decode ((header.frame.trans (frame_compared initial.rip state value)).code pre.code)
    .select (compared_pc ..))).trans (execute_select _ af)

theorem increment_step {initial values value rest consumed state target}
    (header : Header initial values (value :: rest) consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af (selected initial.rip state value) =
      .ok ⟨.next (advanced initial.rip state value),[]⟩ :=
  (step_eq_execute af (decode ((header.frame.trans (frame_selected initial.rip state value)).code pre.code)
    .increment (selected_pc ..))).trans (execute_increment _ af)

theorem back_step {initial values value rest consumed state target}
    (header : Header initial values (value :: rest) consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af (advanced initial.rip state value) =
      .ok ⟨.next (cycle initial.rip state value),[]⟩ := by
  have frame := header.frame.trans (frame_advanced initial.rip state value)
  exact (step_eq_execute af (decode (frame.code pre.code) .back (advanced_pc ..))).trans
    (back_edge (frame.code pre.code) (advanced_pc ..) af)

theorem ret_step {initial values remaining consumed state target}
    (header : Header initial values remaining consumed state) (pre : Pre bytes initial values target)
    (af : Bool) : Sequential.step af (exiting initial.rip state) =
      .ok ⟨.returned (finish (exiting initial.rip state) target),[⟨.stack,initial.registers .rsp,8⟩]⟩ := by
  have frame := header.frame.trans (frame_exiting initial.rip state)
  have read : readWord (exiting initial.rip state).memory
      ((exiting initial.rip state).registers .rsp) = .ok target := by
    rw [frame.memory,frame.stack]
    exact pre.stack
  have actual := (step_eq_execute af (decode (frame.code pre.code) .ret rfl)).trans
    (execute_ret read pre.canonicalTarget af)
  simpa only [frame.stack] using actual

theorem iteration_block {initial values value rest consumed state target}
    (header : Header initial values (value :: rest) consumed state) (pre : Pre bytes initial values target)
    (choices : Choices) : Sequential.Block choices state (cycle initial.rip state value) 7
      [⟨.data,initial.registers .rdi + BitVec.ofNat 64 (8 * consumed),8⟩] := by
  exact Sequential.Block.next (test_step header pre (choices 0))
    (Sequential.Block.next (body_step header pre ((choices.drop 1) 0))
      (Sequential.Block.next (load_step header pre (((choices.drop 1).drop 1) 0))
        (Sequential.Block.next (compare_step header pre ((((choices.drop 1).drop 1).drop 1) 0))
          (Sequential.Block.next (select_step header pre (((((choices.drop 1).drop 1).drop 1).drop 1) 0))
            (Sequential.Block.next (increment_step header pre ((((((choices.drop 1).drop 1).drop 1).drop 1).drop 1) 0))
              (Sequential.Block.next (back_step header pre (((((((choices.drop 1).drop 1).drop 1).drop 1).drop 1).drop 1) 0))
                Sequential.Block.nil))))))

end EDSL.ArrayMaximum64.GCC
