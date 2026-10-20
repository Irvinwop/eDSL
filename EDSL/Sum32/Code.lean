/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Sum32.Shape
import EDSL.X86.Sequential.Machine
import EDSL.X86.Sequential.Code

namespace EDSL.Sum32
open X86

/-- The checker reads the candidate's own finite bytes. This memory has no
data or return stack; it is used solely for instruction decoding. -/
abbrev codeMemory := Sequential.codeMemory

abbrev codeState := Sequential.codeState

def linearFrom (start : Nat) : List Node → Nat → Bool
  | [], finish => decide (start = finish)
  | node :: rest, finish =>
    decide (node.offset = start) && linearFrom (start + node.instruction.length) rest finish

def nodeMatches (bytes : List Byte) (node : Node) : Bool :=
  decide (node.offset < bytes.length) &&
    match Sequential.decodeAt (codeState bytes node.offset) with
    | .ok instruction => decide (instruction = node.instruction)
    | .error _ => false

/-- All assertions are finite code/CFG facts. In particular the candidate
chooses instructions through actual decoding, before this checker classifies it. -/
def checkPlan (bytes : List Byte) (plan : Plan) : Bool :=
  decide (bytes.length ≤ 64) && decide (plan.nodes.length ≤ 32) && plan.shapeValid &&
    linearFrom 0 plan.prologue plan.header &&
    decide (plan.branch.offset = plan.header + 3) &&
    decide (plan.load = plan.branch.offset + 2) &&
    linearFrom (plan.load + plan.mode.load.length) plan.updates plan.back.offset &&
    decide (plan.exit = plan.back.offset + 2) && decide (plan.exit + 1 = bytes.length) &&
    decide ((BitVec.ofNat 64 plan.branch.offset + 2 + plan.branch.displacement.signExtend 64) =
      BitVec.ofNat 64 plan.exit) &&
    decide ((BitVec.ofNat 64 plan.back.offset + 2 + plan.back.displacement.signExtend 64) =
      BitVec.ofNat 64 plan.header) &&
    plan.nodes.all (nodeMatches bytes)

structure Valid (bytes : List Byte) (plan : Plan) : Prop where
  byteBound : bytes.length ≤ 64
  instructionBound : plan.nodes.length ≤ 32
  shape : plan.shapeValid = true
  prologue : linearFrom 0 plan.prologue plan.header = true
  headerNext : plan.branch.offset = plan.header + 3
  branchNext : plan.load = plan.branch.offset + 2
  updates : linearFrom (plan.load + plan.mode.load.length) plan.updates plan.back.offset = true
  backNext : plan.exit = plan.back.offset + 2
  finish : plan.exit + 1 = bytes.length
  forward : BitVec.ofNat 64 plan.branch.offset + 2 + plan.branch.displacement.signExtend 64 =
    BitVec.ofNat 64 plan.exit
  backward : BitVec.ofNat 64 plan.back.offset + 2 + plan.back.displacement.signExtend 64 =
    BitVec.ofNat 64 plan.header
  nodes : ∀ node ∈ plan.nodes, node.offset < bytes.length ∧
    Sequential.decodeAt (codeState bytes node.offset) = .ok node.instruction

theorem checkPlan_sound {bytes : List Byte} {plan : Plan}
    (checked : checkPlan bytes plan = true) : Valid bytes plan := by
  simp only [checkPlan, Bool.and_eq_true_iff, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨size, count⟩, shape⟩, prologue⟩, header⟩, branch⟩, updates⟩,
    back⟩, finish⟩, forward⟩, backward⟩, nodes⟩ := checked
  refine ⟨size, count, shape, prologue, header, branch, updates, back, finish,
    forward, backward, ?_⟩
  intro node member
  have matched := List.all_eq_true.mp nodes node member
  have parts := Bool.and_eq_true_iff.mp matched
  have bound := of_decide_eq_true parts.1
  refine ⟨bound, ?_⟩
  cases decoded : Sequential.decodeAt (codeState bytes node.offset) with
  | error fault => simp [nodeMatches, decoded] at matched
  | ok instruction =>
    have same : instruction = node.instruction := of_decide_eq_true
      (by simpa only [decoded] using parts.2)
    exact congrArg Except.ok same

theorem linearFrom_cons {start finish : Nat} {node : Node} {rest : List Node}
    (linear : linearFrom start (node :: rest) finish = true) :
    node.offset = start ∧ linearFrom (start + node.instruction.length) rest finish = true := by
  simpa only [linearFrom, Bool.and_eq_true_iff, decide_eq_true_eq] using linear

theorem linearFrom_append (start finish : Nat) (left right : List Node) :
    linearFrom start (left ++ right) finish =
      (linearFrom start left (start + (left.map fun node => node.instruction.length).sum) &&
        linearFrom (start + (left.map fun node => node.instruction.length).sum) right finish) := by
  induction left generalizing start with
  | nil => simp [linearFrom]
  | cons node rest induction =>
    simp only [List.cons_append, linearFrom, List.map_cons, List.sum_cons]
    rw [induction]
    simp only [Nat.add_assoc, Bool.and_assoc]

/-- Successful reads of finite candidate bytes transport to the corresponding
real code window. No padded bytes after a final one-byte RET are assumed. -/
theorem code_fetch_transport {bytes : List Byte} {memory : Memory} {base : Word}
    (code : CodeAt memory base bytes) (size : bytes.length ≤ 64) (offset : Nat)
    (inside : offset < bytes.length) (state : State)
    (currentMemory : state.memory = memory) (currentPC : state.rip = base + BitVec.ofNat 64 offset) :
    Sequential.SuccessfulFetchTransport (codeState bytes offset) state :=
  Sequential.code_fetch_transport code size offset inside state currentMemory currentPC

theorem Valid.node_bound {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan)
    (node : Node) (member : node ∈ plan.nodes) : node.offset < bytes.length :=
  (valid.nodes node member).1

theorem CodeAt.canonical_offset {bytes : List Byte} {memory : Memory} {base : Word}
    (code : CodeAt memory base bytes) (offset : Nat) (inside : offset < bytes.length) :
    canonical (base + BitVec.ofNat 64 offset) = true :=
  Sequential.code_canonical_offset code offset inside

theorem Plan.header_member (plan : Plan) : ⟨plan.header, plan.mode.guard⟩ ∈ plan.nodes := by
  simp [Plan.nodes]

theorem Plan.branch_member (plan : Plan) :
    ⟨plan.branch.offset, Sequential.Instruction.je plan.branch.displacement⟩ ∈ plan.nodes := by
  simp [Plan.nodes]

theorem Plan.load_member (plan : Plan) : ⟨plan.load, plan.mode.load⟩ ∈ plan.nodes := by
  simp [Plan.nodes]

theorem Plan.back_member (plan : Plan) :
    ⟨plan.back.offset, Sequential.Instruction.jmp plan.back.displacement⟩ ∈ plan.nodes := by
  simp [Plan.nodes]

theorem Plan.exit_member (plan : Plan) :
    ⟨plan.exit, Sequential.Instruction.legacy .ret⟩ ∈ plan.nodes := by
  simp [Plan.nodes]

theorem Plan.prologue_member (plan : Plan) {node : Node} (member : node ∈ plan.prologue) :
    node ∈ plan.nodes := by
  simp [Plan.nodes, member]

theorem Plan.update_member (plan : Plan) {node : Node} (member : node ∈ plan.updates) :
    node ∈ plan.nodes := by
  simp [Plan.nodes, member]

/-- Transfer a checked node to actual current RAM. This is a derived decode
fact, used to prove steps of the real sequential machine. -/
theorem Valid.decoded {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan)
    {memory : Memory} {base : Word} (code : X86.CodeAt memory base bytes)
    (node : Node) (member : node ∈ plan.nodes) (state : State)
    (currentMemory : state.memory = memory) (currentPC : state.rip = base + BitVec.ofNat 64 node.offset) :
    Sequential.decodeAt state = .ok node.instruction :=
  Sequential.decodeAt_transport
    (code_fetch_transport code valid.byteBound node.offset (valid.nodes node member).1
      state currentMemory currentPC) (valid.nodes node member).2

theorem Valid.canonical_node {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan)
    {memory : Memory} {base : Word} (code : X86.CodeAt memory base bytes)
    (node : Node) (member : node ∈ plan.nodes) :
    canonical (base + BitVec.ofNat 64 node.offset) = true :=
  CodeAt.canonical_offset code node.offset (valid.nodes node member).1

theorem Valid.forward_target {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan) (base : Word) :
    base + BitVec.ofNat 64 plan.branch.offset + 2 + plan.branch.displacement.signExtend 64 =
      base + BitVec.ofNat 64 plan.exit := by
  simpa only [BitVec.add_assoc] using congrArg (fun offset => base + offset) valid.forward

theorem Valid.backward_target {bytes : List Byte} {plan : Plan} (valid : Valid bytes plan) (base : Word) :
    base + BitVec.ofNat 64 plan.back.offset + 2 + plan.back.displacement.signExtend 64 =
      base + BitVec.ofNat 64 plan.header := by
  simpa only [BitVec.add_assoc] using congrArg (fun offset => base + offset) valid.backward

end EDSL.Sum32
