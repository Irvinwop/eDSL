/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Comparison64.Contract
import EDSL.X86.Sequential.ConditionFlags
import EDSL.CountedStore64.Bridges

set_option warningAsError true

namespace EDSL.Comparison64.Client
open X86 X86.Sequential

inductive Variant where
  | gcc | clang
  deriving DecidableEq, Repr

/-- Complete final linked compiler windows, independently decoded below. -/
def bytes : Variant → Operation → List Byte
  | .gcc, .unsignedMaximum => [0x48,0x39,0xf7,0x48,0x89,0xf0,0x48,0x0f,0x43,0xc7,0xc3]
  | .gcc, .unsignedMinimum => [0x48,0x39,0xfe,0x48,0x89,0xf8,0x48,0x0f,0x46,0xc6,0xc3]
  | .gcc, .signedMaximum => [0x48,0x39,0xf7,0x48,0x89,0xf0,0x48,0x0f,0x4d,0xc7,0xc3]
  | .clang, .unsignedMaximum => [0x48,0x89,0xf0,0x48,0x39,0xf7,0x48,0x0f,0x47,0xc7,0xc3]
  | .clang, .unsignedMinimum => [0x48,0x89,0xf0,0x48,0x39,0xf7,0x48,0x0f,0x42,0xc7,0xc3]
  | .clang, .signedMaximum => [0x48,0x89,0xf0,0x48,0x39,0xf7,0x48,0x0f,0x4f,0xc7,0xc3]

inductive Stage where
  | first | second | select | ret
  deriving DecidableEq, Repr

def offset : Stage → Nat
  | .first => 0 | .second => 3 | .select => 6 | .ret => 10

def condition : Variant → Operation → Condition
  | .gcc, .unsignedMaximum => .aboveEqual
  | .gcc, .unsignedMinimum => .belowEqual
  | .gcc, .signedMaximum => .greaterEqual
  | .clang, .unsignedMaximum => .above
  | .clang, .unsignedMinimum => .below
  | .clang, .signedMaximum => .greater

def reversed : Variant → Operation → Bool
  | .gcc, .unsignedMinimum => true
  | _, _ => false

def compareLeft (variant : Variant) (operation : Operation) : Register :=
  if reversed variant operation then .rsi else .rdi
def compareRight (variant : Variant) (operation : Operation) : Register :=
  if reversed variant operation then .rdi else .rsi
def copySource := compareRight
def selectSource := compareLeft

def instruction (variant : Variant) (operation : Operation) : Stage → Sequential.Instruction
  | .first => match variant with
    | .gcc => .cmp64 (compareLeft variant operation) (compareRight variant operation)
    | .clang => .movReg64 .rax (copySource variant operation)
  | .second => match variant with
    | .gcc => .movReg64 .rax (copySource variant operation)
    | .clang => .cmp64 (compareLeft variant operation) (compareRight variant operation)
  | .select => .cmovReg64 (condition variant operation) .rax (selectSource variant operation)
  | .ret => .legacy .ret

theorem inside (variant : Variant) (operation : Operation) (stage : Stage) :
    offset stage < (bytes variant operation).length := by
  cases variant <;> cases operation <;> cases stage <;> decide

theorem span (variant : Variant) (operation : Operation) (stage : Stage) :
    offset stage + (instruction variant operation stage).length ≤ (bytes variant operation).length := by
  cases variant <;> cases operation <;> cases stage <;> decide

theorem static_decode (variant : Variant) (operation : Operation) (stage : Stage) :
    Sequential.decodeAt (codeState (bytes variant operation) (offset stage)) =
      .ok (instruction variant operation stage) := by
  cases variant <;> cases operation <;> cases stage <;> rfl

theorem decode {variant operation} {state : State} {base : Word}
    (code : CodeAt state.memory base (bytes variant operation)) (stage : Stage)
    (pc : state.rip = base + BitVec.ofNat 64 (offset stage)) :
    Sequential.decodeAt state = .ok (instruction variant operation stage) :=
  decodeAt_transport (code_fetch_transport code (by cases variant <;> cases operation <;> decide)
    (offset stage) (inside variant operation stage) state rfl pc) (static_decode variant operation stage)

theorem fetch_at {variant operation} {state : State} {base : Word}
    (code : CodeAt state.memory base (bytes variant operation)) (stage : Stage)
    (pc : state.rip = base + BitVec.ofNat 64 (offset stage)) :
    OS.Borrowing.Subregion ⟨state.rip,(instruction variant operation stage).length⟩
      ⟨base,(bytes variant operation).length⟩ :=
  code_fetch_span code state (instruction variant operation stage) (offset stage) pc
    (span variant operation stage)

def compare (variant : Variant) (operation : Operation) (state : State) : State :=
  { state with
    rip := state.rip + 3
    flags := cmpFlags64 state.flags (state.registers (compareLeft variant operation))
      (state.registers (compareRight variant operation)) }
def copy (variant : Variant) (operation : Operation) (state : State) : State :=
  { state.writeRegister .rax (state.registers (copySource variant operation)) with rip := state.rip + 3 }
def select (variant : Variant) (operation : Operation) (state : State) : State :=
  { state.writeRegister .rax
      (if (condition variant operation).holds state.flags then
        state.registers (selectSource variant operation) else state.registers .rax) with
    rip := state.rip + 4 }
def finish (state : State) (target : Word) : State :=
  { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target }

def firstState (variant : Variant) (operation : Operation) (initial : State) : State :=
  match variant with | .gcc => compare variant operation initial | .clang => copy variant operation initial
def secondState (variant : Variant) (operation : Operation) (initial : State) : State :=
  match variant with
  | .gcc => copy variant operation (firstState variant operation initial)
  | .clang => compare variant operation (firstState variant operation initial)
def thirdState (variant : Variant) (operation : Operation) (initial : State) : State :=
  select variant operation (secondState variant operation initial)
def finalState (variant : Variant) (operation : Operation) (initial : State) (target : Word) : State :=
  finish (thirdState variant operation initial) target

def stageState (variant : Variant) (operation : Operation) (stage : Stage) (initial : State) : State :=
  match stage with
  | .first => initial | .second => firstState variant operation initial
  | .select => secondState variant operation initial | .ret => thirdState variant operation initial

/-- Complete RAM, all non-result GPRs and non-arithmetic flags at each prefix. -/
structure Frame (initial current : State) : Prop where
  memory : current.memory = initial.memory
  registers : ∀ register, register ≠ .rax → current.registers register = initial.registers register
  flags : current.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem Frame.initial (initial : State) : Frame initial initial := ⟨rfl,fun _ _ => rfl,rfl⟩
theorem Frame.compare {initial current} (frame : Frame initial current) (variant operation) :
    Frame initial (compare variant operation current) :=
  ⟨frame.memory,frame.registers,(cmpFlags64_preserves ..).trans frame.flags⟩
theorem Frame.copy {initial current} (frame : Frame initial current) (variant operation) :
    Frame initial (copy variant operation current) := by
  refine ⟨frame.memory,?_,frame.flags⟩
  intro register different
  simpa [Client.copy,State.writeRegister,different] using frame.registers register different
theorem Frame.select {initial current} (frame : Frame initial current) (variant operation) :
    Frame initial (select variant operation current) := by
  refine ⟨frame.memory,?_,frame.flags⟩
  intro register different
  simpa [Client.select,State.writeRegister,different] using frame.registers register different

theorem stage_frame (variant operation stage initial) :
    Frame initial (stageState variant operation stage initial) := by
  cases stage with
  | first => exact .initial initial
  | second =>
    cases variant
    · exact (Frame.initial initial).compare _ _
    · exact (Frame.initial initial).copy _ _
  | select =>
    cases variant
    · exact ((Frame.initial initial).compare _ _).copy _ _
    · exact ((Frame.initial initial).copy _ _).compare _ _
  | ret =>
    cases variant
    · exact (((Frame.initial initial).compare _ _).copy _ _).select _ _
    · exact (((Frame.initial initial).copy _ _).compare _ _).select _ _

theorem stage_pc (variant operation stage initial) :
    (stageState variant operation stage initial).rip = initial.rip + BitVec.ofNat 64 (offset stage) := by
  cases variant <;> cases stage <;>
    simp only [stageState,firstState,secondState,thirdState,compare,copy,select,offset,
      BitVec.add_assoc,BitVec.add_zero] <;> rfl

def observation (variant : Variant) (operation : Operation) (stage : Stage)
    (initial : State) (target : Word) : Observation :=
  match stage with
  | .first => ⟨.next (firstState variant operation initial),[]⟩
  | .second => ⟨.next (secondState variant operation initial),[]⟩
  | .select => ⟨.next (thirdState variant operation initial),[]⟩
  | .ret => ⟨.returned (finalState variant operation initial target),[⟨.stack,initial.registers .rsp,8⟩]⟩

theorem execute_stage {variant operation input initial}
    (pre : Pre (bytes variant operation) input initial) (stage : Stage) (af : Bool) :
    execute (stageState variant operation stage initial) (instruction variant operation stage) af =
      .ok (observation variant operation stage initial input.returnAddress) := by
  cases stage with
  | first => cases variant <;> rfl
  | second => cases variant <;> rfl
  | select => rfl
  | ret =>
    have frame := stage_frame variant operation .ret initial
    change Frame initial (thirdState variant operation initial) at frame
    have loaded : readWord (thirdState variant operation initial).memory
        ((thirdState variant operation initial).registers .rsp) = .ok input.returnAddress := by
      rw [frame.memory,frame.registers .rsp (by decide)]
      exact pre.stack
    simp only [stageState,instruction,execute,X86.executeInstruction,X86.executeRet,
      loaded,pre.returnCanonical,ite_true,ok_bind,pure_ok,Instruction.operandReads,
      observation,finalState,finish]
    rw [frame.registers .rsp (by decide)]

theorem stage_decoded {variant operation input initial}
    (pre : Pre (bytes variant operation) input initial) (stage : Stage) :
    Sequential.decodeAt (stageState variant operation stage initial) =
      .ok (instruction variant operation stage) := by
  have code : CodeAt (stageState variant operation stage initial).memory initial.rip
      (bytes variant operation) := by rw [(stage_frame ..).memory]; exact pre.code
  exact decode code stage (stage_pc ..)

theorem step_stage {variant operation input initial}
    (pre : Pre (bytes variant operation) input initial) (stage : Stage) (af : Bool) :
    Sequential.step af (stageState variant operation stage initial) =
      .ok (observation variant operation stage initial input.returnAddress) :=
  (step_eq_execute af (stage_decoded pre stage)).trans (execute_stage pre stage af)

end EDSL.Comparison64.Client
