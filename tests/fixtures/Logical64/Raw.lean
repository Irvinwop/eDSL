/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Logical64.Domain
import EDSL.CountedStore64.Bridges

set_option warningAsError true

namespace EDSL.Logical64.Client
open X86 X86.Sequential

def bytes : Operation → List Byte
  | .intersection => [0x48,0x89,0xf8,0x48,0x21,0xf0,0xc3]
  | .union => [0x48,0x89,0xf8,0x48,0x09,0xf0,0xc3]
  | .symmetricDifference => [0x48,0x89,0xf8,0x48,0x31,0xf0,0xc3]

/-- The translation belongs to the implementation, outside the contracts. -/
def opcode : Operation → LogicalOp
  | .intersection => .band | .union => .bor | .symmetricDifference => .bxor

inductive Stage where
  | copy | logical | ret
  deriving DecidableEq, Repr

def offset : Stage → Nat
  | .copy => 0 | .logical => 3 | .ret => 6

def instruction (operation : Operation) : Stage → Sequential.Instruction
  | .copy => .movReg64 .rax .rdi
  | .logical => .logicalReg64 (opcode operation) .rax .rsi
  | .ret => .legacy .ret

theorem inside (operation : Operation) (stage : Stage) : offset stage < (bytes operation).length := by
  cases operation <;> cases stage <;> decide

theorem static_decode (operation : Operation) (stage : Stage) :
    Sequential.decodeAt (codeState (bytes operation) (offset stage)) =
      .ok (instruction operation stage) := by
  cases operation <;> cases stage <;> rfl

theorem decode {operation} {state : State} {base : Word}
    (code : CodeAt state.memory base (bytes operation))
    (stage : Stage) (pc : state.rip = base + BitVec.ofNat 64 (offset stage)) :
    Sequential.decodeAt state = .ok (instruction operation stage) :=
  decodeAt_transport (code_fetch_transport code (by cases operation <;> decide) (offset stage)
    (inside operation stage) state rfl pc) (static_decode operation stage)

def copy (state : State) : State :=
  { state.writeRegister .rax (state.registers .rdi) with rip := state.rip + 3 }

def logical (operation : Operation) (state : State) (af : Bool) : State :=
  let result := (opcode operation).eval (state.registers .rax) (state.registers .rsi)
  { state.writeRegister .rax result with
    rip := state.rip + 3, flags := logicalFlags64 state.flags result af }

def secondState (operation : Operation) (initial : State) (af : Bool) : State :=
  logical operation (copy initial) af

def finish (state : State) (target : Word) : State :=
  { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target }

def finalState (operation : Operation) (initial : State) (target : Word) (af : Bool) : State :=
  finish (secondState operation initial af) target

def stageState (operation : Operation) (stage : Stage) (initial : State) (logicalAF : Bool) : State :=
  match stage with
  | .copy => initial | .logical => copy initial | .ret => secondState operation initial logicalAF

structure Frame (initial current : State) : Prop where
  memory : current.memory = initial.memory
  registers : ∀ register, register ≠ .rax → current.registers register = initial.registers register
  flags : current.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem Frame.initial (initial : State) : Frame initial initial := ⟨rfl,fun _ _ => rfl,rfl⟩

theorem Frame.copy {initial current} (frame : Frame initial current) :
    Frame initial (copy current) := by
  refine ⟨frame.memory,?_,frame.flags⟩
  intro register different
  simpa [Logical64.Client.copy,State.writeRegister,different] using frame.registers register different

theorem Frame.logical {initial current} (frame : Frame initial current) (operation : Operation) (af : Bool) :
    Frame initial (logical operation current af) := by
  refine ⟨frame.memory,?_,(logicalFlags64_preserves ..).trans frame.flags⟩
  intro register different
  simpa [Logical64.Client.logical,State.writeRegister,different] using frame.registers register different

theorem stage_frame (operation stage initial af) : Frame initial (stageState operation stage initial af) := by
  cases stage with
  | copy => exact .initial initial
  | logical => exact (Frame.initial initial).copy
  | ret => exact (Frame.initial initial).copy.logical operation af

theorem stage_pc (operation stage initial af) :
    (stageState operation stage initial af).rip = initial.rip + BitVec.ofNat 64 (offset stage) := by
  cases stage <;>
    simp only [stageState,secondState,logical,copy,offset,BitVec.add_assoc,BitVec.add_zero] <;> rfl

def observation (operation : Operation) (stage : Stage) (initial : State) (target : Word)
    (logicalAF stepAF : Bool) : Observation :=
  match stage with
  | .copy => ⟨.next (copy initial),[]⟩
  | .logical => ⟨.next (secondState operation initial stepAF),[]⟩
  | .ret => ⟨.returned (finalState operation initial target logicalAF),[⟨.stack,initial.registers .rsp,8⟩]⟩

theorem execute_stage {operation input initial} (pre : Pre (bytes operation) input initial)
    (stage : Stage) (logicalAF stepAF : Bool) :
    execute (stageState operation stage initial logicalAF) (instruction operation stage) stepAF =
      .ok (observation operation stage initial input.returnAddress logicalAF stepAF) := by
  cases stage with
  | copy => rfl
  | logical => rfl
  | ret =>
    have frame := stage_frame operation .ret initial logicalAF
    change Frame initial (secondState operation initial logicalAF) at frame
    have loaded : readWord (secondState operation initial logicalAF).memory
        ((secondState operation initial logicalAF).registers .rsp) = .ok input.returnAddress := by
      rw [frame.memory,frame.registers .rsp (by decide)]
      exact pre.stack
    simp only [stageState,instruction,execute,X86.executeInstruction,X86.executeRet,
      loaded,pre.returnCanonical,ite_true,ok_bind,pure_ok,Instruction.operandReads,
      observation,finalState,finish]
    rw [frame.registers .rsp (by decide)]

theorem stage_decoded {operation input initial} (pre : Pre (bytes operation) input initial)
    (stage : Stage) (logicalAF : Bool) :
    Sequential.decodeAt (stageState operation stage initial logicalAF) = .ok (instruction operation stage) := by
  have code : CodeAt (stageState operation stage initial logicalAF).memory initial.rip (bytes operation) := by
    rw [(stage_frame ..).memory]
    exact pre.code
  exact decode code stage (stage_pc ..)

theorem step_stage {operation input initial} (pre : Pre (bytes operation) input initial)
    (stage : Stage) (logicalAF stepAF : Bool) :
    Sequential.step stepAF (stageState operation stage initial logicalAF) =
      .ok (observation operation stage initial input.returnAddress logicalAF stepAF) :=
  (step_eq_execute stepAF (stage_decoded pre stage logicalAF)).trans
    (execute_stage pre stage logicalAF stepAF)

theorem selected_result {operation input initial} (pre : Pre (bytes operation) input initial) (af : Bool) :
    MathematicalResult operation input.left input.right
      ((secondState operation initial af).registers .rax) := by
  cases operation <;> intro index <;>
    simp [secondState,logical,copy,opcode,LogicalOp.eval,State.writeRegister,pre.left,pre.right,
      HasBit,BitVec.testBit_toNat]
  cases input.left[index.val] <;> cases input.right[index.val] <;> decide

theorem final_post {operation input initial} (pre : Pre (bytes operation) input initial) (af : Bool) :
    Post operation input initial (finalState operation initial input.returnAddress af) := by
  have frame := stage_frame operation .ret initial af
  change Frame initial (secondState operation initial af) at frame
  refine ⟨?_,frame.memory,rfl,?_,?_,frame.flags⟩
  · simpa only [finalState,finish,State.writeRegister,reduceCtorEq,ite_false] using selected_result pre af
  · simp only [finalState,finish,State.writeRegister,ite_true]
    exact congrArg (· + 8) (frame.registers .rsp (by decide))
  · intro register member
    have notStack : register ≠ .rsp := by
      intro same; subst register; simp [Logical64.calleeSaved] at member
    have notResult : register ≠ .rax := by
      intro same; subst register; simp [Logical64.calleeSaved] at member
    simpa only [finalState,finish,State.writeRegister,notStack,ite_false] using
      frame.registers register notResult

/-- Three actual retirements for these seven bytes, for every AF stream.
The logical instruction consumes stream index 1; MOV and RET ignore theirs. -/
theorem executions {operation input initial} (pre : Pre (bytes operation) input initial) (choices : Choices) :
    Sequential.Executes choices initial
      ⟨finalState operation initial input.returnAddress (choices 1),3,[⟨.stack,initial.registers .rsp,8⟩]⟩ := by
  have execution := Sequential.Executes.next (step_stage pre .copy false (choices 0))
    (Sequential.Executes.next (step_stage pre .logical false ((choices.drop 1) 0))
      (Sequential.Executes.ret (step_stage pre .ret ((choices.drop 1) 0)
        (((choices.drop 1).drop 1) 0))))
  simpa only [stageState,observation,Result.prepend,List.nil_append,Choices.drop,Nat.add_zero]
    using execution

theorem raw_semantics {operation input initial} (pre : Pre (bytes operation) input initial) :
    AllExecutions initial (fun result => Post operation input initial result.state ∧
      result.instructions = 3 ∧ result.reads = [⟨.stack,initial.registers .rsp,8⟩]) := by
  intro choices
  exact ⟨_,executions pre choices,final_post pre (choices 1),rfl,rfl⟩

theorem execution_exact {operation input initial choices result} (pre : Pre (bytes operation) input initial)
    (execution : Sequential.Executes choices initial result) :
    result = ⟨finalState operation initial input.returnAddress (choices 1),3,
      [⟨.stack,initial.registers .rsp,8⟩]⟩ :=
  execution.fixed_choices_unique (executions pre choices)

/-- Prefix witnesses describe only actual pre-states and prior AF choices.
They do not assume a future successful run. -/
def Prefix (operation : Operation) (initial before : State) : Prop :=
  ∃ stage af, before = stageState operation stage initial af

theorem prefix_continues {operation input initial before after af outcome reads}
    (pre : Pre (bytes operation) input initial) (inside : Prefix operation initial before)
    (actual : Sequential.step af before = .ok ⟨outcome,reads⟩)
    (next : nextState outcome = some after) : Prefix operation initial after := by
  obtain ⟨stage,logicalAF,rfl⟩ := inside
  have same := Except.ok.inj ((step_stage pre stage logicalAF af).symm.trans actual)
  cases stage with
  | copy =>
    cases same
    cases next
    exact ⟨.logical,false,rfl⟩
  | logical =>
    cases same
    cases next
    exact ⟨.ret,af,rfl⟩
  | ret =>
    cases same
    cases next

theorem prefix_block {operation input initial before final choices count reads}
    (pre : Pre (bytes operation) input initial) (inside : Prefix operation initial before)
    (block : Sequential.Block choices before final count reads) : Prefix operation initial final := by
  induction block with
  | nil => exact inside
  | next step tail induction | atomic step tail induction =>
    exact induction (prefix_continues pre inside step rfl)

theorem prefix_reachable {operation input initial before} (pre : Pre (bytes operation) input initial)
    (reachable : Sequential.Reachable initial before) : Prefix operation initial before := by
  obtain ⟨_,_,_,block⟩ := reachable
  exact prefix_block pre ⟨.copy,false,rfl⟩ block

theorem raw_policy {operation input initial} (pre : Pre (bytes operation) input initial) : RawPolicy initial := by
  intro before reachable
  obtain ⟨stage,logicalAF,rfl⟩ := prefix_reachable pre reachable
  have frame := stage_frame operation stage initial logicalAF
  refine ⟨frame.memory,⟨instruction operation stage,stage_decoded pre stage logicalAF,?_⟩,?_⟩
  · cases stage <;> rfl
  · intro af
    refine ⟨observation operation stage initial input.returnAddress logicalAF af,
      step_stage pre stage logicalAF af,?_,?_⟩
    · intro read member
      cases stage with
      | copy | logical => cases member
      | ret =>
        simp only [observation,List.mem_singleton] at member
        subst read
        refine ⟨⟨rfl,rfl,rfl⟩,rfl,input.returnAddress,?_⟩
        rw [frame.memory]
        exact pre.stack
    · cases stage with
      | copy => exact (stage_frame operation .logical initial false).memory.trans frame.memory.symm
      | logical => exact (stage_frame operation .ret initial af).memory.trans frame.memory.symm
      | ret => rfl

/-- Correctness and current-resource policy follow from the independently
specified result and the actual reachable-prefix proof. The trusted registry
imports the contract and domain, while this implementation remains a client. -/
theorem readOnly_semantic_claim (operation : Operation) :
    Grading.ReadOnlySemanticClaim (readOnlyTask operation) (bytes operation) := by
  apply readOnly_semantics_of_raw
  intro input initial pre
  refine ⟨?_,raw_policy pre⟩
  intro choices
  obtain ⟨result,execution,post,_,_⟩ := raw_semantics pre choices
  exact ⟨result,execution,post⟩

/-- The same complete OS world and original reusable code/caller loans survive
actual return, together with the independently specified result and exact
accounting for this implementation. -/
theorem returned_resources {operation resource initial}
    (pre : ResourcePre (bytes operation) resource initial) (choices : Choices) :
    ∃ result, Sequential.Executes choices initial result ∧
      Post operation (resourceInput resource) initial result.state ∧ result.instructions = 3 ∧
      result.reads = [⟨.stack,resource.call.stack,8⟩] ∧
      OS.CallResources.Current resource.call resource.shared result.state ∧
      OS.Threads.HasLoan resource.shared resource.call.worker resource.call.codeLoan
        ⟨resource.call.code,resource.call.bytes.length⟩ ∧
      OS.Threads.HasLoan resource.shared resource.call.worker resource.call.stackLoan
        ⟨resource.call.stack,8⟩ ∧
      OS.CallResources.ReadAllowed resource.call resource.shared ⟨.stack,resource.call.stack,8⟩ := by
  obtain ⟨result,execution,post,count,reads⟩ := raw_semantics pre.machine choices
  have current := pre.current.sameMemory post.memory
  refine ⟨result,execution,post,count,?_,current,current.contract.codeLoan,
    current.contract.stackLoan,OS.CallResources.stackRead_permission current.contract⟩
  simpa only [pre.stack] using reads

end EDSL.Logical64.Client
