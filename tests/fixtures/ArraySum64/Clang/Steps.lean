/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.ArraySum64.Clang.Model

set_option warningAsError true

namespace EDSL.ArraySum64.Clang
open X86 X86.Sequential

/-- Transport the exact decoded node to the executable bytes in current RAM. -/
theorem step_at {initial before : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (node : Index)
    (memory : before.memory = initial.memory)
    (pc : before.rip = initial.rip + BitVec.ofNat 64 (graph.node node).offset)
    (af : Bool) {observation : Observation}
    (effect : execute before (graph.node node).instruction af = .ok observation) :
    Sequential.step af before = .ok observation :=
  (valid.step_eq_execute pre.code node before memory pc af).trans effect

theorem initialized {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (positive : values ≠ [])
    (testAF indexAF resultAF : Bool) :
    Header initial values values 0 (initializedState initial testAF indexAF resultAF) where
  length := by simp
  index := by simp [initializedState,indexState,positiveState,clear,edit,State.writeRegister]
  array := by simpa [initializedState,indexState,positiveState,clear,edit,atPC,test,State.writeRegister] using pre.array
  correct := by
    change ((0 : Word).toNat + sumNat values) % 2^64 = sumMod values
    simp [sumMod]
  frame := frame_initialized ..
  pc := by
    have nonempty : values.isEmpty = false := by cases values <;> simp_all
    simp only [initializedState,indexState,positiveState,clear,edit,atPC,loopOffset,nonempty,
      Bool.false_eq_true,ite_false,BitVec.add_assoc]
    rfl

@[simp] theorem add_value (state : State) (value : Word) :
    (add state value).registers .rax = state.registers .rax + value := rfl
@[simp] theorem advanced_index (state : State) (value : Word) :
    (advanced state value).registers .rcx = state.registers .rcx + 1 := rfl
@[simp] theorem advanced_count (state : State) (value : Word) :
    (advanced state value).registers .rsi = state.registers .rsi := rfl
@[simp] theorem testedIndex_index (state : State) (value : Word) :
    (testedIndex state value).registers .rcx = state.registers .rcx + 1 := rfl
@[simp] theorem testedIndex_value (state : State) (value : Word) :
    (testedIndex state value).registers .rax = state.registers .rax + value := rfl

theorem nextHeader {initial state : State} {values rest : List Word} {consumed : Nat} {value : Word}
    (header : Header initial values (value :: rest) consumed state) :
    Header initial values rest (consumed + 1) (cycleState initial.rip state value rest) where
  length := by have length := header.length; simp only [List.length_cons] at length; omega
  index := by
    change state.registers .rcx + 1 = BitVec.ofNat 64 (consumed + 1)
    rw [header.index,BitVec.ofNat_add]
    rfl
  array := by
    change ArrayAt64 state.memory
      (initial.registers .rdi + BitVec.ofNat 64 (8 * (consumed + 1))) rest
    simpa [Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc] using header.array.tail
  correct := by
    change (((testedIndex state value).registers .rax).toNat + sumNat rest) % 2^64 = sumMod values
    rw [testedIndex_value,accumulator_suffix]
    exact header.correct
  frame := header.frame.trans (frame_cycle ..)
  pc := rfl

theorem header_address {initial state : State} {values remaining : List Word} {consumed : Nat}
    (header : Header initial values remaining consumed state) :
    Address.eval (.indexed .rdi .rcx 3) state =
      initial.registers .rdi + BitVec.ofNat 64 (8 * consumed) := by
  have shift : (BitVec.ofNat 64 consumed <<< 3) = BitVec.ofNat 64 (8 * consumed) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 consumed * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * consumed)
    rw [← BitVec.ofNat_mul,Nat.mul_comm]
  change state.registers .rdi + (state.registers .rcx <<< 3) = _
  rw [header.frame.preserved .rdi (by decide),header.index,shift]

theorem header_operand {initial state : State} {values rest : List Word} {consumed : Nat} {value : Word}
    (header : Header initial values (value :: rest) consumed state) :
    loadQWord state.memory (Address.eval (.indexed .rdi .rcx 3) state) = .ok value := by
  rw [header_address header]
  exact header.array.head

theorem step_test {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (af : Bool) :
    Sequential.step af initial = .ok ⟨.next (test initial af),[]⟩ := by
  refine step_at (before := initial) pre 0 rfl (by simp [graph,CFG.Graph.node]) af ?_
  change execute initial (.test64 .rsi .rsi) af = _
  rw [execute_test64,BitVec.and_self]
  rfl

theorem tested_zero {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (af : Bool) :
    (test initial af).flags.getLsbD 6 = decide (values = []) := by
  have zero : BitVec.ofNat 64 values.length = 0 ↔ values = [] := by
    constructor
    · intro zero
      have same := congrArg BitVec.toNat zero
      have bound := pre.bound.length_lt
      have length : values.length = 0 := by simpa [Nat.mod_eq_of_lt bound] using same
      exact List.length_eq_zero_iff.mp length
    · intro zero; rw [zero]; rfl
  simp only [test,logicalFlags64_zero,pre.count,Bool.beq_eq_decide_eq,zero]

theorem step_positive {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (positive : values ≠ []) (testAF af : Bool) :
    Sequential.step af (test initial testAF) = .ok ⟨.next (positiveState initial testAF),[]⟩ := by
  refine step_at (before := test initial testAF) pre 1 rfl rfl af ?_
  change execute (test initial testAF) (.je 17) af = _
  rw [execute_je,tested_zero pre testAF]
  simp only [positive,decide_false,executeShortBranch,Bool.false_eq_true,ite_false,ok_bind,pure_ok]
  congr 1
  simp only [test,positiveState,atPC,BitVec.add_assoc]
  rfl

theorem step_empty {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (empty : values = []) (testAF af : Bool) :
    Sequential.step af (test initial testAF) = .ok ⟨.next (emptyState initial testAF),[]⟩ := by
  have canonicalExit : canonical (initial.rip + 22) = true :=
    valid.canonical_node pre.code (9 : Index)
  have displacement : (3 : Word) + 2 + (17 : Byte).signExtend 64 = 22 := by decide
  refine step_at (before := test initial testAF) pre 1 rfl rfl af ?_
  change execute (test initial testAF) (.je 17) af = _
  rw [execute_je,tested_zero pre testAF]
  simp only [empty,decide_true,executeShortBranch,ite_true,test,BitVec.add_assoc,
    displacement,canonicalExit,ok_bind,pure_ok]
  rfl

theorem step_clearIndex {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (testAF af : Bool) :
    Sequential.step af (positiveState initial testAF) =
      .ok ⟨.next (indexState initial testAF af),[]⟩ :=
  step_at (before := positiveState initial testAF) pre 2 rfl rfl af rfl

theorem step_clearResult {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (testAF indexAF af : Bool) :
    Sequential.step af (indexState initial testAF indexAF) =
      .ok ⟨.next (initializedState initial testAF indexAF af),[]⟩ := by
  refine step_at (before := indexState initial testAF indexAF) pre 3 rfl ?_ af rfl
  change initial.rip + 5 + 2 = initial.rip + 7
  rw [BitVec.add_assoc]
  rfl

theorem step_clearEmpty {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (testAF af : Bool) :
    Sequential.step af (emptyState initial testAF) =
      .ok ⟨.next (emptyReturn initial testAF af),[]⟩ :=
  step_at (before := emptyState initial testAF) pre 9 rfl rfl af rfl

/-- The one fused memory-source ADD reads DATA8 at the current original input
address and uses the original accumulator, before writing RAX or flags. -/
theorem step_add {initial state : State} {values rest : List Word} {consumed : Nat}
    {value target : Word} (pre : Pre bytes initial values target)
    (header : Header initial values (value :: rest) consumed state) (af : Bool) :
    Sequential.step af state = .ok ⟨.next (add state value),
      [⟨.data,initial.registers .rdi + BitVec.ofNat 64 (8 * consumed),8⟩]⟩ := by
  refine step_at (before := state) pre 4 header.frame.memory header.pc af ?_
  change execute state (.addMem64 .rax (.indexed .rdi .rcx 3)) af = _
  rw [execute_addMem64,header_operand header]
  simp only [ok_bind,pure_ok,header_address header]
  rfl

theorem step_increment {initial state : State} {values rest : List Word} {consumed : Nat}
    {value target : Word} (pre : Pre bytes initial values target)
    (header : Header initial values (value :: rest) consumed state) (af : Bool) :
    Sequential.step af (add state value) = .ok ⟨.next (advanced state value),[]⟩ := by
  refine step_at (before := add state value) pre 5 header.frame.memory ?_ af rfl
  simp only [add,edit,header.pc,loopOffset,List.isEmpty_cons,BitVec.add_assoc]
  rfl

theorem step_compareIndex {initial state : State} {values rest : List Word} {consumed : Nat}
    {value target : Word} (pre : Pre bytes initial values target)
    (header : Header initial values (value :: rest) consumed state) (af : Bool) :
    Sequential.step af (advanced state value) = .ok ⟨.next (testedIndex state value),[]⟩ := by
  refine step_at (before := advanced state value) pre 6 header.frame.memory ?_ af rfl
  simp only [advanced,increment,add,edit,header.pc,loopOffset,List.isEmpty_cons,BitVec.add_assoc]
  rfl

theorem index_zero {initial state : State} {values rest : List Word} {consumed : Nat}
    {value target : Word} (pre : Pre bytes initial values target)
    (header : Header initial values (value :: rest) consumed state) :
    (testedIndex state value).flags.getLsbD 6 = decide (rest = []) := by
  have countBound := pre.bound.length_lt
  have length := header.length
  simp only [List.length_cons] at length
  have indexBound : consumed + 1 < 2^64 := by omega
  have same : BitVec.ofNat 64 values.length = BitVec.ofNat 64 (consumed + 1) ↔ rest = [] := by
    rw [BitVec.toNat_eq]
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt countBound,Nat.mod_eq_of_lt indexBound]
    constructor
    · intro equal
      apply List.length_eq_zero_iff.mp
      omega
    · intro empty
      subst rest
      simpa using length.symm
  have nextIndex : BitVec.ofNat 64 consumed + 1 = BitVec.ofNat 64 (consumed + 1) := by
    rw [BitVec.ofNat_add]
    rfl
  simp only [testedIndex,compareIndex,cmpFlags64_zero,advanced_count,advanced_index,
    header.frame.preserved .rsi (by decide),pre.count,header.index,nextIndex,
    Bool.beq_eq_decide_eq,same]

theorem step_cycle {initial state : State} {values rest : List Word} {consumed : Nat}
    {value target : Word} (pre : Pre bytes initial values target)
    (header : Header initial values (value :: rest) consumed state) (af : Bool) :
    Sequential.step af (testedIndex state value) =
      .ok ⟨.next (cycleState initial.rip state value rest),[]⟩ := by
  have pc : (testedIndex state value).rip = initial.rip + 19 := by
    simp only [testedIndex,compareIndex,advanced,increment,add,edit,header.pc,loopOffset,
      List.isEmpty_cons,BitVec.add_assoc]
    rfl
  have canonicalHeader : canonical (initial.rip + 9) = true :=
    valid.canonical_node pre.code (4 : Index)
  have displacement : (19 : Word) + 2 + (244 : Byte).signExtend 64 = 9 := by decide
  refine step_at (before := testedIndex state value) pre 7 header.frame.memory pc af ?_
  change execute (testedIndex state value) (.legacy (.jnz 244)) af = _
  simp only [execute,X86.executeInstruction,executeJnz,Instruction.operandReads]
  rw [index_zero pre header]
  cases rest with
  | nil =>
    simp only [decide_true,Bool.not_true,executeShortBranch,Bool.false_eq_true,ite_false,
      ok_bind,pure_ok]
    congr 1
    simp only [cycleState,atPC,loopOffset,List.isEmpty_nil,ite_true,pc,BitVec.add_assoc]
    rfl
  | cons next tail =>
    simp only [executeShortBranch,ite_true,pc,
      BitVec.add_assoc,displacement,canonicalHeader,pure_ok]
    rfl

theorem execute_return {initial before : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (frame : Frame initial before) (af : Bool) :
    execute before (.legacy .ret) af = .ok ⟨.returned (finish before target),
      [⟨.stack,initial.registers .rsp,8⟩]⟩ := by
  have stack : readWord before.memory (before.registers .rsp) = .ok target := by
    rw [frame.memory,frame.stack]
    exact pre.stack
  simp only [execute,X86.executeInstruction,executeRet,stack,pre.canonicalTarget,ite_true,
    ok_bind,pure_ok,Instruction.operandReads,finish]
  rw [frame.stack]

theorem step_return {initial state : State} {values : List Word} {consumed : Nat}
    {target : Word} (pre : Pre bytes initial values target)
    (header : Header initial values [] consumed state) (af : Bool) :
    Sequential.step af state = .ok ⟨.returned (finish state target),
      [⟨.stack,initial.registers .rsp,8⟩]⟩ :=
  step_at (before := state) pre 8 header.frame.memory header.pc af (execute_return pre header.frame af)

theorem step_returnEmpty {initial : State} {values : List Word} {target : Word}
    (pre : Pre bytes initial values target) (testAF resultAF af : Bool) :
    Sequential.step af (emptyReturn initial testAF resultAF) =
      .ok ⟨.returned (finish (emptyReturn initial testAF resultAF) target),
        [⟨.stack,initial.registers .rsp,8⟩]⟩ := by
  refine step_at (before := emptyReturn initial testAF resultAF) pre 10 rfl ?_ af
    (execute_return pre (frame_emptyReturn ..) af)
  change initial.rip + 22 + 2 = initial.rip + 24
  rw [BitVec.add_assoc]
  rfl

theorem finish_post {initial state : State} {values : List Word} {target : Word}
    (frame : Frame initial state) (correct : (state.registers .rax).toNat = sumMod values) :
    Post initial values target (finish state target) := by
  refine ⟨correct,frame.memory,rfl,?_,?_,frame.flags⟩
  · change state.registers .rsp + 8 = initial.registers .rsp + 8
    rw [frame.stack]
  · intro register outside
    have different : register ≠ .rsp := by
      intro same; subst register; simp [clobbers] at outside
    simpa only [finish,State.writeRegister,different,ite_false] using frame.preserved register outside

theorem return_post {initial state : State} {values : List Word} {consumed : Nat} {target : Word}
    (header : Header initial values [] consumed state) : Post initial values target (finish state target) := by
  apply finish_post header.frame
  simpa only [sumNat_nil,Nat.add_zero,Nat.mod_eq_of_lt (BitVec.isLt _)] using header.correct

theorem empty_post {initial : State} {values : List Word} {target : Word}
    (empty : values = []) (testAF resultAF : Bool) :
    Post initial values target (finish (emptyReturn initial testAF resultAF) target) := by
  refine finish_post (frame_emptyReturn ..) ?_
  subst values
  rfl

end EDSL.ArraySum64.Clang
