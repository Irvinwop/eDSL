/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Policy
import EDSL.X86.Sequential.ConditionFlags
import EDSL.Comparison64.Domain
import EDSL.Grading.Task

set_option warningAsError true

namespace EDSL.X86.VCGen.CompilerComparisons
open Sequential

/-- Frozen corpus/v1 default compiler outputs, without rebuilding or changing
the compiler's CET options. This parameter selects bytes, not a grading task. -/
inductive Compiler where
  | defaultGCC | defaultClang
  deriving DecidableEq, Repr

inductive Operation where
  | minimum | maximum
  deriving DecidableEq, Repr

def operation : Operation → Comparison64.Operation
  | .minimum => .unsignedMinimum
  | .maximum => .unsignedMaximum

def taskID : Operation → Grading.TaskID
  | .minimum => .minimum64
  | .maximum => .maximum64

/-- The fixed production sequential target: long mode, IBT and shadow stacks
disabled, multi-byte NOP supported. Decoding cannot establish CPU/MSR state.
In particular the GCC prefix is an actual retired ENDBR64 under this target. -/
abbrev targetProfile : TargetProfile := Sequential.targetProfile

/-- Complete literal windows from the immutable corpus/v1 manifests. File
offsets, symbol identities and actual ELF addresses require separate binding;
these byte claims alone do not certify a frozen ELF or its native mapping. -/
def bytes : Compiler → Operation → List Byte
  | .defaultGCC, .minimum =>
      [0xf3,0x0f,0x1e,0xfa,0x48,0x39,0xfe,0x48,0x89,0xf8,0x48,0x0f,0x46,0xc6,0xc3]
  | .defaultGCC, .maximum =>
      [0xf3,0x0f,0x1e,0xfa,0x48,0x39,0xfe,0x48,0x89,0xf8,0x48,0x0f,0x43,0xc6,0xc3]
  | .defaultClang, .minimum =>
      [0x48,0x89,0xf0,0x48,0x39,0xf7,0x48,0x0f,0x42,0xc7,0xc3]
  | .defaultClang, .maximum =>
      [0x48,0x89,0xf0,0x48,0x39,0xf7,0x48,0x0f,0x47,0xc7,0xc3]

private def instructions (compiler : Compiler) (op : Operation) :
    List Sequential.Instruction :=
  match compiler with
  | .defaultGCC => [.endbr64IbtDisabled, .cmp64 .rsi .rdi, .movReg64 .rax .rdi,
      .cmovReg64 (if op = .minimum then .belowEqual else .aboveEqual) .rax .rsi,
      .legacy .ret]
  | .defaultClang => [.movReg64 .rax .rsi, .cmp64 .rdi .rsi,
      .cmovReg64 (if op = .minimum then .below else .above) .rax .rdi, .legacy .ret]

private def nodesFrom (offset : Nat) : List Sequential.Instruction → List CFG.Node
  | [] => []
  | instruction :: rest => ⟨offset,instruction,false,0⟩ ::
      nodesFrom (offset + instruction.length) rest

/-- Proposed graph data. Every byte and successor is independently checked by
the production CFG checker; no instruction list is trusted as a decoder. -/
def graph (compiler : Compiler) (op : Operation) : CFG.Graph :=
  let nodes := nodesFrom 0 (instructions compiler op)
  ⟨nodes.mapIdx (fun index node => { node with
    cutpoint := decide (index = 0), depth := nodes.length - index }), nodes.length⟩

theorem valid (compiler : Compiler) (op : Operation) :
    CFG.Valid (bytes compiler op) (graph compiler op) := by
  cases compiler <;> cases op <;> exact CFG.check_sound (by decide)

def entry (compiler : Compiler) (op : Operation) : (graph compiler op).Index :=
  ⟨0, by cases compiler <;> cases op <;> decide⟩

@[simp] theorem entry_offset (compiler : Compiler) (op : Operation) :
    ((graph compiler op).node (entry compiler op)).offset = 0 := by
  cases compiler <;> cases op <;> rfl

/-- Independent observable retired count, including GCC's ENDBR64 and RET.
This is not computed from graph metadata or the instruction list. -/
def retired : Compiler → Nat
  | .defaultGCC => 5
  | .defaultClang => 4

def stackRead (initial : State) : Read := ⟨.stack,initial.registers .rsp,8⟩

/-- Logical permission for only the original caller slot, together with the
complete initial RAM/permission frame at the actual pre-instruction state. -/
def Allowed (initial before : State) (read : Read) : Prop :=
  before.memory = initial.memory ∧ read = stackRead initial

/-- The registered independent full64 mathematical/ABI/frame contract and
separate exact observations. The contract itself does not fix an encoding,
instruction count, flag condition, or ordered operand-read trace. -/
def Post (compiler : Compiler) (op : Operation) (input : Comparison64.Input)
    (initial : State) (result : Result) : Prop :=
  Comparison64.Post (operation op) input initial result.state ∧
    result.instructions = retired compiler ∧ result.reads = [stackRead initial]

/- Reduce the SAME production executor through generated WP. Only matching a
generated successor RIP against candidate graph offsets requires search. No
per-instruction execution proof, localVC or alternative evaluator is supplied. -/
local macro "reduce_generated" stack:ident target:ident : tactic => `(tactic|
  (rw [wp]
   intro af
   conv in (CFG.Graph.node _ _).instruction =>
     simp [graph,instructions,nodesFrom,
       CFG.Graph.node,Sequential.Instruction.length]
   simp only [Sequential.execute,Sequential.Instruction.operandReads,
     Sequential.Instruction.length,
     X86.executeInstruction,X86.executeRet,State.writeRegister,ok_bind,pure_ok]
   simp [Allowed,stackRead,State.writeRegister,$stack:ident,$target:ident]))

local macro "next_generated_at" index:num : tactic => `(tactic|
  (refine ⟨⟨$index:num,?_⟩,?_,?_⟩
   · decide
   · solve | simp [graph,instructions,nodesFrom,
       CFG.Graph.node,Sequential.Instruction.length,BitVec.add_assoc]))

local macro "next_generated" : tactic => `(tactic|
  first
  | next_generated_at 0
  | next_generated_at 1
  | next_generated_at 2
  | next_generated_at 3
  | next_generated_at 4)

/-- One generated formula proof for both compiler profiles and operations.
Only current code/arguments/caller-slot premises are admitted. Registers,
flags, memory and all AF choices remain arbitrary; no future run is assumed. -/
theorem generated_vc (compiler : Compiler) (op : Operation)
    (input : Comparison64.Input) (initial : State)
    (pre : Comparison64.Pre (bytes compiler op) input initial) :
    wp (graph compiler op) initial.rip (Allowed initial) (retired compiler)
      (entry compiler op) initial (Post compiler op input initial) := by
  have stack := pre.stack
  have target := pre.returnCanonical
  cases compiler <;> cases op <;> simp only [retired,entry] <;>
    repeat' (reduce_generated stack target; first | next_generated | skip)
  all_goals refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  all_goals simp [operation,Comparison64.MathematicalResult,
    Comparison64.calleeSaved,stackRead,Result.prepend,retired,
    Condition.cmp_below,Condition.cmp_above,
    Condition.cmp_belowEqual,Condition.cmp_aboveEqual,
    cmpFlags64_preserves,pre.left,pre.right]
  all_goals simp_all only [Nat.min_def,Nat.max_def]
  all_goals repeat' split
  all_goals (try simp_all) <;> omega

/-- Universal execution of exact current bytes and every AF stream, with the
registered independent postcondition, exact count/read order and permission
at each actual operand-read origin. The fixed targetProfile is environmental. -/
theorem verifies (compiler : Compiler) (op : Operation)
    (input : Comparison64.Input) (initial : State)
    (pre : Comparison64.Pre (bytes compiler op) input initial) (choices : Choices) :
    ∃ result, Sequential.run choices (retired compiler) initial = .ok result ∧
      Post compiler op input initial result ∧ CheckedTrace (Allowed initial) choices initial result := by
  have pc : initial.rip = initial.rip +
      BitVec.ofNat 64 ((graph compiler op).node (entry compiler op)).offset := by simp
  obtain ⟨result,actual,post,_,trace⟩ := VCGen.run_sound (valid compiler op) pre.code pc
    (generated_vc compiler op input initial pre) choices
  exact ⟨result,actual,post,trace⟩

/-- Exact retired count and ordered STACK8 trace for ANY actual execution,
separately from the mathematical task registration and its resource adapter. -/
theorem observations (compiler : Compiler) (op : Operation)
    {input : Comparison64.Input} {initial : State}
    (pre : Comparison64.Pre (bytes compiler op) input initial)
    {choices : Choices} {result : Result} (execution : Sequential.Executes choices initial result) :
    result.instructions = retired compiler ∧ result.reads = [stackRead initial] := by
  obtain ⟨verified,actual,post,_⟩ := verifies compiler op input initial pre choices
  have same := execution.fixed_choices_unique (Sequential.run_sound actual)
  subst verified
  exact post.2

/-- Shared production every-prefix policy, transported into the existing raw
comparison contract. No program-specific resource invariant is supplied. -/
theorem raw_semantics (compiler : Compiler) (op : Operation)
    (input : Comparison64.Input) (initial : State)
    (pre : Comparison64.Pre (bytes compiler op) input initial) :
    AllExecutions initial (fun result =>
      Comparison64.Post (operation op) input initial result.state) ∧
      Comparison64.RawPolicy initial := by
  have pc : initial.rip = initial.rip +
      BitVec.ofNat 64 ((graph compiler op).node (entry compiler op)).offset := by simp
  constructor
  · intro choices
    obtain ⟨result,actual,post,_⟩ := verifies compiler op input initial pre choices
    exact ⟨result,Sequential.run_sound actual,post.1⟩
  · have policy := readOnly_policy_memory (valid compiler op) pre.code pc
      (generated_vc compiler op input initial pre)
    refine policy.mono (fun _ memory => memory) ?_
    intro before read allowed
    rw [allowed.2]
    exact ⟨rfl,rfl,rfl⟩

/-- Existing complete OS-world/code/caller-loan adapter, including current
resources at every actual prefix and after the real RET. -/
theorem readOnly_semantics (compiler : Compiler) (op : Operation) :
    Grading.ReadOnlySemanticClaim (Comparison64.readOnlyTask (operation op))
      (bytes compiler op) :=
  Comparison64.readOnly_semantics_of_raw (raw_semantics compiler op)

/-- Existing registered minimum64/maximum64 claims. Useful raw and current
resource witnesses are independent of decoding and execution. This conditional
byte/resource result does not raise frozen corpus certification counts. -/
theorem claim (compiler : Compiler) (op : Operation) :
    Grading.Claim (taskID op) (bytes compiler op) := by
  have witnesses := Comparison64.Domain.nonvacuous (operation op) (bytes compiler op)
    (by cases compiler <;> cases op <;> decide)
    (by cases compiler <;> cases op <;> decide)
  have registered := (Grading.old_claim_iff _ _).mpr
    ⟨readOnly_semantics compiler op,witnesses⟩
  cases op <;> exact registered

end EDSL.X86.VCGen.CompilerComparisons
