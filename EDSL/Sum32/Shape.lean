/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Model

namespace EDSL.Sum32
open X86
abbrev SeqInstruction := Sequential.Instruction

/-- Two loop-state representations for the same mathematical sum contract. -/
inductive Mode where
  | pointerCount | index
  deriving DecidableEq, Repr

structure Node where
  offset : Nat
  instruction : SeqInstruction
  deriving DecidableEq, Repr

structure Branch where
  offset : Nat
  displacement : Byte
  deriving DecidableEq, Repr

def Mode.guard : Mode → SeqInstruction
  | .pointerCount => .test64 .rsi .rsi
  | .index => .cmp64 .rsi .rcx

def Mode.load : Mode → SeqInstruction
  | .pointerCount => .addMem32 .rax (.base .rdi)
  | .index => .addMem32 .rax (.indexed .rdi .rcx 2)

/-- A proposed layout, checked against actual decoded bytes separately.
Offsets and branch displacements are certificate data, never decoder gates. -/
structure Plan where
  mode : Mode
  prologue : List Node
  header : Nat
  branch : Branch
  load : Nat
  updates : List Node
  back : Branch
  exit : Nat
  deriving DecidableEq, Repr

def Plan.nodes (plan : Plan) : List Node :=
  plan.prologue ++ [⟨plan.header, plan.mode.guard⟩,
    ⟨plan.branch.offset, .je plan.branch.displacement⟩,
    ⟨plan.load, plan.mode.load⟩] ++ plan.updates ++
    [⟨plan.back.offset, .jmp plan.back.displacement⟩, ⟨plan.exit, .legacy .ret⟩]

/-- Both XOR-zero and MOV-zero have the required register effect. Arithmetic
flag differences remain part of the sequential semantics. -/
def clearTarget : SeqInstruction → Option Register
  | .xorSelf32 destination => some destination
  | .legacy (.mov32 destination value) => if value = 0 then some destination else none
  | _ => none

def allowedClear (instruction : SeqInstruction) : Bool :=
  match clearTarget instruction with
  | some .rax | some .rcx => true
  | _ => false

def clears (nodes : List Node) (register : Register) : Bool :=
  nodes.any fun node => decide (clearTarget node.instruction = some register)

def Plan.prologueValid (plan : Plan) : Bool :=
  plan.prologue.all (fun node => allowedClear node.instruction) &&
    clears plan.prologue .rax &&
    match plan.mode with
    | .pointerCount => true
    | .index => clears plan.prologue .rcx

/-- Independent counter and pointer updates may be reordered. The indexed
form advances its full 64-bit index after the input read. -/
def Plan.updatesValid (plan : Plan) : Bool :=
  let instructions := plan.updates.map Node.instruction
  match plan.mode with
  | .pointerCount =>
    decide (instructions = [.dec64 .rsi, .addImm64 .rdi 4] ∨
      instructions = [.addImm64 .rdi 4, .dec64 .rsi])
  | .index => decide (instructions = [.inc64 .rcx])

def Plan.shapeValid (plan : Plan) : Bool := plan.prologueValid && plan.updatesValid

/-- The cost is derived from the certified block sizes. It counts modeled
retired instructions, including RET, rather than bytes or flag choices. -/
def Plan.cost (plan : Plan) (elements : Nat) : Nat :=
  (plan.updates.length + 4) * elements + plan.prologue.length + 3

theorem clearTarget_some {instruction : SeqInstruction} {register : Register}
    (cleared : clearTarget instruction = some register) :
    instruction = .xorSelf32 register ∨ instruction = .legacy (.mov32 register 0) := by
  cases instruction with
  | xorSelf32 destination =>
    have same : destination = register := Option.some.inj cleared
    subst destination
    exact Or.inl rfl
  | legacy old =>
    cases old <;> simp only [clearTarget] at cleared
    all_goals try { cases cleared }
    split at cleared
    next zero =>
      have same : _ = register := Option.some.inj cleared
      subst register
      subst zero
      exact Or.inr rfl
    next => cases cleared
  | test64 _ _ | cmp64 _ _ | addMem32 _ _ | addImm64 _ _ | inc64 _ | dec64 _ | je _ | jmp _ =>
    cases cleared

theorem Plan.prologue_rax {plan : Plan} (valid : plan.prologueValid = true) :
    ∃ node ∈ plan.prologue, clearTarget node.instruction = some .rax := by
  have present := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).2
  obtain ⟨node, member, cleared⟩ := List.any_eq_true.mp present
  exact ⟨node, member, of_decide_eq_true cleared⟩

theorem Plan.updates_length {plan : Plan} (valid : plan.updatesValid = true) :
    plan.updates.length = match plan.mode with | .pointerCount => 2 | .index => 1 := by
  cases kind : plan.mode with
  | pointerCount =>
    have selected := of_decide_eq_true (show decide
        (plan.updates.map Node.instruction = [.dec64 .rsi, .addImm64 .rdi 4] ∨
          plan.updates.map Node.instruction = [.addImm64 .rdi 4, .dec64 .rsi]) = true from
        by simpa only [updatesValid, kind] using valid)
    rcases selected with first | second
    · simpa using congrArg List.length first
    · simpa using congrArg List.length second
  | index =>
    have selected := of_decide_eq_true (show decide
        (plan.updates.map Node.instruction = [.inc64 .rcx]) = true from
        by simpa only [updatesValid, kind] using valid)
    simpa using congrArg List.length selected

end EDSL.Sum32
