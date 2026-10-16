/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.IndexFrame

namespace EDSL.Sum32
open X86
namespace IndexProof

def compared (plan : Plan) (base : Word) (state : State) : State :=
  { state with
    rip := base + BitVec.ofNat 64 plan.branch.offset
    flags := Sequential.cmpFlags64 state.flags (state.registers .rsi) (state.registers .rcx) }

def atLoad (plan : Plan) (base : Word) (state : State) : State :=
  { compared plan base state with rip := base + BitVec.ofNat 64 plan.load }

def added (plan : Plan) (base : Word) (state : State) (value : BitVec 32) : State :=
  { (atLoad plan base state).writeRegister .rax
      (((state.registers .rax).setWidth 32 + value).setWidth 64) with
    rip := base + BitVec.ofNat 64 (plan.load + 3)
    flags := addFlags32 (compared plan base state).flags ((state.registers .rax).setWidth 32) value }

def incremented (plan : Plan) (base : Word) (state : State) (value : BitVec 32) : State :=
  { (added plan base state value).writeRegister .rcx (state.registers .rcx + 1) with
    rip := base + BitVec.ofNat 64 plan.back.offset
    flags := Sequential.incFlags64 (added plan base state value).flags (state.registers .rcx) }

def resumed (plan : Plan) (base : Word) (state : State) (value : BitVec 32) : State :=
  { incremented plan base state value with rip := base + BitVec.ofNat 64 plan.header }

def atExit (plan : Plan) (base : Word) (state : State) : State :=
  { compared plan base state with rip := base + BitVec.ofNat 64 plan.exit }

def returned (plan : Plan) (base : Word) (state : State) (target : Word) : State :=
  { (atExit plan base state).writeRegister .rsp (state.registers .rsp + 8) with rip := target }

theorem compare_step {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {values : List (BitVec 32)} {accumulator : BitVec 32} {target : Word}
    {consumed total : Nat} (valid : Valid bytes plan) (mode : plan.mode = .index)
    (header : IndexHeader bytes plan base state values accumulator target consumed total)
    (af : Bool) :
    Sequential.step af state = .ok ⟨.next (compared plan base state), []⟩ := by
  have decoded : Sequential.decodeAt state = .ok (.cmp64 .rsi .rcx) := by
    simpa only [mode, Mode.guard] using
      valid.decoded header.code ⟨plan.header, plan.mode.guard⟩ plan.header_member state rfl header.pc
  rw [Sequential.step_eq_execute af decoded, Sequential.execute_cmp64]
  simp only [compared, header.pc, valid.headerNext, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

theorem branch_exit_step {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {accumulator : BitVec 32} {target : Word} {consumed total : Nat}
    (valid : Valid bytes plan)
    (header : IndexHeader bytes plan base state [] accumulator target consumed total) (af : Bool) :
    Sequential.step af (compared plan base state) =
      .ok ⟨.next (atExit plan base state), []⟩ := by
  have zero : (compared plan base state).flags.getLsbD 6 = true :=
    (cmp_zero header).mpr (by have := header.remaining; simp only [List.length_nil] at this; omega)
  have decoded := valid.decoded header.code _ plan.branch_member (compared plan base state) rfl rfl
  have canonicalExit := valid.canonical_node header.code _ plan.exit_member
  rw [Sequential.step_eq_execute af decoded, Sequential.execute_je, zero]
  simp only [executeShortBranch, ↓reduceIte, compared, valid.forward_target base,
    canonicalExit, atExit, ok_bind, pure_ok]

theorem branch_load_step {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {value : BitVec 32} {values : List (BitVec 32)} {accumulator : BitVec 32}
    {target : Word} {consumed total : Nat} (valid : Valid bytes plan)
    (header : IndexHeader bytes plan base state (value :: values) accumulator target consumed total)
    (af : Bool) :
    Sequential.step af (compared plan base state) = .ok ⟨.next (atLoad plan base state), []⟩ := by
  have nonzero : (compared plan base state).flags.getLsbD 6 = false := by
    apply Bool.eq_false_iff.mpr
    intro zero
    have same := (cmp_zero header).mp zero
    have := header.remaining
    simp only [List.length_cons] at this
    omega
  have decoded := valid.decoded header.code _ plan.branch_member (compared plan base state) rfl rfl
  rw [Sequential.step_eq_execute af decoded, Sequential.execute_je, nonzero]
  simp only [executeShortBranch, Bool.false_eq_true, ↓reduceIte, compared, atLoad,
    valid.branchNext, BitVec.ofNat_add, BitVec.add_assoc, ok_bind, pure_ok]
  rfl

theorem add_step {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {value : BitVec 32} {values : List (BitVec 32)} {accumulator : BitVec 32}
    {target : Word} {consumed total : Nat} (valid : Valid bytes plan) (mode : plan.mode = .index)
    (header : IndexHeader bytes plan base state (value :: values) accumulator target consumed total)
    (af : Bool) :
    Sequential.step af (atLoad plan base state) =
      .ok ⟨.next (added plan base state value),
        [⟨.data, state.registers .rdi + BitVec.ofNat 64 (4 * consumed), 4⟩]⟩ := by
  have decoded : Sequential.decodeAt (atLoad plan base state) =
      .ok (.addMem32 .rax (.indexed .rdi .rcx 2)) := by
    simpa only [mode, Mode.load] using
      valid.decoded header.code _ plan.load_member (atLoad plan base state) rfl rfl
  have address : (Sequential.Address.indexed .rdi .rcx 2).eval (atLoad plan base state) =
      state.registers .rdi + BitVec.ofNat 64 (4 * consumed) := indexed_address header.index
  rw [Sequential.step_eq_execute af decoded, Sequential.execute_addMem32, address]
  have loaded : loadDWord (atLoad plan base state).memory
      (state.registers .rdi + BitVec.ofNat 64 (4 * consumed)) = .ok value := header.array.head
  rw [loaded]
  simp only [ok_bind, pure_ok, Sequential.Instruction.length, added, atLoad, compared,
    BitVec.ofNat_add, BitVec.add_assoc]

theorem increment_step {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {value : BitVec 32} {values : List (BitVec 32)} {accumulator : BitVec 32}
    {target : Word} {consumed total : Nat} (valid : Valid bytes plan) (mode : plan.mode = .index)
    (header : IndexHeader bytes plan base state (value :: values) accumulator target consumed total)
    (af : Bool) :
    Sequential.step af (added plan base state value) =
      .ok ⟨.next (incremented plan base state value), []⟩ := by
  have layout := update_layout valid mode
  have member : (⟨plan.load + 3, .inc64 .rcx⟩ : Node) ∈ plan.nodes :=
    plan.update_member (by rw [layout.1]; exact List.mem_singleton_self _)
  have decoded := valid.decoded header.code _ member (added plan base state value) rfl rfl
  rw [Sequential.step_eq_execute af decoded, Sequential.execute_inc64]
  simp only [incremented, added, atLoad, compared, State.writeRegister,
    reduceCtorEq, ↓reduceIte,
    layout.2, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

theorem back_step {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {value : BitVec 32} {values : List (BitVec 32)} {accumulator : BitVec 32}
    {target : Word} {consumed total : Nat} (valid : Valid bytes plan)
    (header : IndexHeader bytes plan base state (value :: values) accumulator target consumed total)
    (af : Bool) :
    Sequential.step af (incremented plan base state value) =
      .ok ⟨.next (resumed plan base state value), []⟩ := by
  have decoded := valid.decoded header.code _ plan.back_member (incremented plan base state value) rfl rfl
  have canonicalHeader := valid.canonical_node header.code _ plan.header_member
  rw [Sequential.step_eq_execute af decoded, Sequential.execute_jmp]
  simp only [executeShortBranch, ↓reduceIte, incremented, valid.backward_target base,
    canonicalHeader, resumed, ok_bind, pure_ok]

theorem return_step {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {values : List (BitVec 32)} {accumulator : BitVec 32} {target : Word}
    {consumed total : Nat} (valid : Valid bytes plan)
    (header : IndexHeader bytes plan base state values accumulator target consumed total) (af : Bool) :
    Sequential.step af (atExit plan base state) =
      .ok ⟨.returned (returned plan base state target), [⟨.stack, state.registers .rsp, 8⟩]⟩ := by
  have decoded := valid.decoded header.code _ plan.exit_member (atExit plan base state) rfl rfl
  rw [Sequential.step_eq_execute af decoded, Sequential.execute_legacy]
  simp only [executeInstruction, executeRet, atExit, compared, header.stack,
    header.canonicalTarget, ↓reduceIte, ok_bind, pure_ok, returned,
    Sequential.Instruction.operandReads]
  rfl

theorem resumed_frame (plan : Plan) (base : Word) (state : State) (value : BitVec 32) :
    Frame state (resumed plan base state value) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro register notRax notRcx
    simp only [resumed, incremented, added, atLoad, compared, State.writeRegister,
      notRax, notRcx, ↓reduceIte]
  · change Sequential.incFlags64 _ _ &&& ~~~arithmeticFlagMask = _
    rw [Sequential.incFlags64_preserves]
    change addFlags32 _ _ _ &&& ~~~arithmeticFlagMask = _
    rw [addFlags32_preserves]
    exact Sequential.cmpFlags64_preserves _ _ _

theorem resumed_header {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {value : BitVec 32} {values : List (BitVec 32)} {accumulator : BitVec 32}
    {target : Word} {consumed total : Nat}
    (header : IndexHeader bytes plan base state (value :: values) accumulator target consumed total) :
    IndexHeader bytes plan base (resumed plan base state value) values (accumulator + value)
      target (consumed + 1) total := by
  have frame := resumed_frame plan base state value
  have rdi := frame.registers .rdi (by decide) (by decide)
  have rsi := frame.registers .rsi (by decide) (by decide)
  have rsp := frame.registers .rsp (by decide) (by decide)
  refine {
    code := ?_
    pc := rfl
    accumulator := ?_
    stack := ?_
    canonicalTarget := header.canonicalTarget
    canonicalStackAfter := ?_
    array := ?_
    count := rsi.trans header.count
    index := ?_
    remaining := ?_
    countBound := header.countBound }
  · rw [frame.memory]
    exact header.code
  · simp [resumed, incremented, added, atLoad, compared, State.writeRegister, header.accumulator]
  · rw [frame.memory, rsp]
    exact header.stack
  · rw [rsp]
    exact header.canonicalStackAfter
  · rw [frame.memory, rdi, next_address]
    exact header.array.tail
  · simp only [resumed, incremented, State.writeRegister, ↓reduceIte, header.index,
      BitVec.ofNat_add]
    rfl
  · have := header.remaining
    simp only [List.length_cons] at this
    omega

theorem body_block {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {value : BitVec 32} {values : List (BitVec 32)} {accumulator : BitVec 32}
    {target : Word} {consumed total : Nat} (valid : Valid bytes plan) (mode : plan.mode = .index)
    (header : IndexHeader bytes plan base state (value :: values) accumulator target consumed total)
    (choices : Sequential.Choices) :
    Sequential.Block choices state (resumed plan base state value) 5
      [⟨.data, state.registers .rdi + BitVec.ofNat 64 (4 * consumed), 4⟩] := by
  exact Sequential.Block.next (compare_step valid mode header (choices 0))
    (Sequential.Block.next (branch_load_step valid header ((choices.drop 1) 0))
      (Sequential.Block.next (add_step valid mode header (((choices.drop 1).drop 1) 0))
        (Sequential.Block.next (increment_step valid mode header ((((choices.drop 1).drop 1).drop 1) 0))
          (Sequential.Block.next (back_step valid header (((((choices.drop 1).drop 1).drop 1).drop 1) 0))
            Sequential.Block.nil))))

theorem exit_execution {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {accumulator : BitVec 32} {target : Word} {consumed total : Nat}
    (valid : Valid bytes plan) (mode : plan.mode = .index)
    (header : IndexHeader bytes plan base state [] accumulator target consumed total)
    (choices : Sequential.Choices) :
    Sequential.Executes choices state
      ⟨returned plan base state target, 3, [⟨.stack, state.registers .rsp, 8⟩]⟩ := by
  exact Sequential.Executes.next (compare_step valid mode header (choices 0))
    (Sequential.Executes.next (branch_exit_step valid header ((choices.drop 1) 0))
      (Sequential.Executes.ret (return_step valid header (((choices.drop 1).drop 1) 0))))

theorem exit_post {bytes : List Byte} {plan : Plan} {base : Word} {state : State}
    {accumulator : BitVec 32} {target : Word} {consumed total : Nat}
    (header : IndexHeader bytes plan base state [] accumulator target consumed total) :
    LoopPost state accumulator [] target (returned plan base state target) := by
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [returned, atExit, compared, State.writeRegister] using header.accumulator
  · simp only [returned, State.writeRegister, ↓reduceIte]
  · intro register outside
    have notRsp : register ≠ .rsp := by
      intro same
      subst register
      exact outside (by decide)
    simp only [returned, atExit, compared, State.writeRegister, notRsp, ↓reduceIte]
  · exact Sequential.cmpFlags64_preserves _ _ _

theorem reads_cons (plan : Plan) (base : Word) (state : State) (value : BitVec 32)
    (values : List (BitVec 32)) (consumed : Nat) :
    indexReads state consumed (value :: values) =
      [⟨.data, state.registers .rdi + BitVec.ofNat 64 (4 * consumed), 4⟩] ++
        indexReads (resumed plan base state value) (consumed + 1) values := by
  have frame := resumed_frame plan base state value
  simp only [indexReads, inputReads, frame.registers .rdi (by decide) (by decide),
    frame.registers .rsp (by decide) (by decide), next_address, List.cons_append, List.nil_append]

end IndexProof
end EDSL.Sum32
