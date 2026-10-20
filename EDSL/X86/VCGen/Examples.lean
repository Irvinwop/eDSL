/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Core
import EDSL.X86.Sequential.ConditionFlags

namespace EDSL.X86.VCGen.Examples
open Sequential

/- These are complete functions from linked ELF .text sections, not snippets
with an unsupported prefix removed. These Clang 18.1.3 outputs use
-std=gnu2x -O2. Sources, commands, exit statuses, disassembly and SHA256s
are retained locally in .cache/corpus-work/vcgen/examples/compiler.log.
That historical log also retains separate GCC experiments; their nondefault
CET-disabled variants are outside this public example interface.

The C bodies are identity x; unsigned a+b; a^b; a<b?a:b; a>b?a:b; *p;
and `if (x<lo) return lo; if (x>hi) return hi; return x;`.
The add/min/max contracts also match corpus-v1 c_add_mod64/c_min_u64/c_max_u64.
No source-language preservation or atomic/acquire interpretation is asserted. -/
inductive Routine where
  | identity64 | add64 | xor64 | minClang | maxClang | load64 | clampClang
  deriving DecidableEq, Repr

def bytes : Routine → List Byte
  | .identity64 => [0x48,0x89,0xf8,0xc3]
  | .add64 => [0x48,0x8d,0x04,0x37,0xc3]
  | .xor64 => [0x48,0x89,0xf8,0x48,0x31,0xf0,0xc3]
  | .minClang => [0x48,0x89,0xf0,0x48,0x39,0xf7,0x48,0x0f,0x42,0xc7,0xc3]
  | .maxClang => [0x48,0x89,0xf0,0x48,0x39,0xf7,0x48,0x0f,0x47,0xc7,0xc3]
  | .load64 => [0x48,0x8b,0x07,0xc3]
  | .clampClang => [0x48,0x89,0xd0,0x48,0x39,0xd7,0x48,0x0f,0x42,0xc7,
      0x48,0x39,0xf7,0x48,0x0f,0x42,0xc6,0xc3]

private def instructions : Routine → List Sequential.Instruction
  | .identity64 => [.movReg64 .rax .rdi, .legacy .ret]
  | .add64 => [.lea64 .rax (.indexed .rdi .rsi 0), .legacy .ret]
  | .xor64 => [.movReg64 .rax .rdi, .logicalReg64 .bxor .rax .rsi, .legacy .ret]
  | .minClang => [.movReg64 .rax .rsi, .cmp64 .rdi .rsi,
      .cmovReg64 .below .rax .rdi, .legacy .ret]
  | .maxClang => [.movReg64 .rax .rsi, .cmp64 .rdi .rsi,
      .cmovReg64 .above .rax .rdi, .legacy .ret]
  | .load64 => [.loadMem64 .rax (.base .rdi), .legacy .ret]
  | .clampClang => [.movReg64 .rax .rdx, .cmp64 .rdi .rdx,
      .cmovReg64 .below .rax .rdi, .cmp64 .rdi .rsi,
      .cmovReg64 .below .rax .rsi, .legacy .ret]

private def nodesFrom (offset : Nat) : List Sequential.Instruction → List CFG.Node
  | [] => []
  | instruction :: rest => ⟨offset,instruction,false,0⟩ ::
      nodesFrom (offset + instruction.length) rest

/-- Proposed graph data are checked against every actual instruction byte. -/
def graph (routine : Routine) : CFG.Graph :=
  let nodes := nodesFrom 0 (instructions routine)
  ⟨nodes.mapIdx (fun index node => { node with
    cutpoint := decide (index = 0), depth := nodes.length - index }), nodes.length⟩

theorem valid (routine : Routine) : CFG.Valid (bytes routine) (graph routine) := by
  cases routine <;> exact CFG.check_sound (by decide)

def entry (routine : Routine) : (graph routine).Index :=
  ⟨0, by cases routine <;> decide⟩

@[simp] theorem entry_offset (routine : Routine) :
    ((graph routine).node (entry routine)).offset = 0 := by cases routine <;> rfl

/-- Independent retired-instruction budgets, not derived from graph metadata. -/
def cost : Routine → Nat
  | .identity64 | .add64 | .load64 => 2
  | .xor64 => 3
  | .minClang | .maxClang => 4
  | .clampClang => 6

def stackRead (initial : State) : Read := ⟨.stack,initial.registers .rsp,8⟩
def dataRead (initial : State) : Read := ⟨.data,initial.registers .rdi,8⟩

/-- Permission is tied to the original caller slot and, only for load64,
the original DATA8 argument. It also requires complete memory preservation. -/
def Allowed (routine : Routine) (initial before : State) (read : Read) : Prop :=
  before.memory = initial.memory ∧
    (read = stackRead initial ∨ routine = .load64 ∧ read = dataRead initial)

def footprint (routine : Routine) (initial : State) : List Read :=
  if routine = .load64 then [dataRead initial,stackRead initial] else [stackRead initial]

def calleeSaved : List Register := [.rbx,.rbp,.r12,.r13,.r14,.r15]

/-- Mathematical specifications are independent of instruction selection and
flags. The XOR clause specifies each bit; addition uses natural modular sum;
min/max/clamp use mathematical order, rather than a copied CMOV condition. -/
def Value (routine : Routine) (initial : State) (payload output : Word) : Prop :=
  match routine with
  | .identity64 => output = initial.registers .rdi
  | .add64 => output.toNat =
      ((initial.registers .rdi).toNat + (initial.registers .rsi).toNat) % 2^64
  | .xor64 => ∀ bit, bit < 64 → output.getLsbD bit =
      ((initial.registers .rdi).getLsbD bit ^^ (initial.registers .rsi).getLsbD bit)
  | .minClang => output.toNat =
      min (initial.registers .rdi).toNat (initial.registers .rsi).toNat
  | .maxClang => output.toNat =
      max (initial.registers .rdi).toNat (initial.registers .rsi).toNat
  | .load64 => output = payload
  | .clampClang => output.toNat =
      max (initial.registers .rsi).toNat
        (min (initial.registers .rdi).toNat (initial.registers .rdx).toNat)

/-- The independent observable contract includes the complete memory and
permission maps, SysV callee registers, nonarithmetic flags, actual return
target and stack adjustment, ordered read footprint and EXACT retired cost. -/
def Post (routine : Routine) (initial : State) (returnAddress payload : Word)
    (result : Result) : Prop :=
  Value routine initial payload (result.state.registers .rax) ∧
  result.state.memory = initial.memory ∧ result.state.rip = returnAddress ∧
  result.state.registers .rsp = initial.registers .rsp + 8 ∧
  (∀ register ∈ calleeSaved, result.state.registers register = initial.registers register) ∧
  result.state.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask ∧
  result.instructions = cost routine ∧ result.reads = footprint routine initial

/-- Current ordinary RAM/caller-stack premises only. No future execution,
per-instruction invariant, chosen AF value or concrete memory fixture appears. -/
structure ReturnReady (initial : State) (returnAddress : Word) : Prop where
  stack : readWord initial.memory (initial.registers .rsp) = .ok returnAddress
  returnCanonical : canonical returnAddress = true
  stackBound : (initial.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : canonical (initial.registers .rsp + 8) = true

def DataReady (routine : Routine) (initial : State) (payload : Word) : Prop :=
  routine = .load64 → loadQWord initial.memory (initial.registers .rdi) = .ok payload

def OrderReady (routine : Routine) (initial : State) : Prop :=
  routine = .clampClang →
    (initial.registers .rsi).toNat ≤ (initial.registers .rdx).toNat

/- Generic proof automation reduces the SAME production executor through wp.
The only search is for a graph index whose offset matches the generated RIP;
the equality is proved by kernel-checked arithmetic simplification. No localVC,
instruction execution lemma or routine-specific transition is supplied. -/
local macro "reduce_generated" stack:ident target:ident data:ident : tactic => `(tactic|
  (rw [wp]
   intro af
   conv in (CFG.Graph.node _ _).instruction =>
     simp [graph,instructions,nodesFrom,
       CFG.Graph.node,Sequential.Instruction.length]
   simp only [Sequential.execute,Sequential.Instruction.operandReads,
     Sequential.Instruction.length,
     X86.executeInstruction,X86.executeRet,State.writeRegister,Address.eval,
     LogicalOp.eval,BitVec.shiftLeft_zero,ok_bind,pure_ok]
   simp [Allowed,stackRead,dataRead,State.writeRegister,
     $stack:ident,$target:ident,$data:ident]))

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
  | next_generated_at 4
  | next_generated_at 5)

theorem generated_vc (routine : Routine) (initial : State) (returnAddress payload : Word)
    (ready : ReturnReady initial returnAddress)
    (data : DataReady routine initial payload) (order : OrderReady routine initial) :
    wp (graph routine) initial.rip (Allowed routine initial) (cost routine)
      (entry routine) initial (Post routine initial returnAddress payload) := by
  have stack := ready.stack
  have target := ready.returnCanonical
  unfold DataReady at data
  unfold OrderReady at order
  cases routine <;> simp only [cost,entry] <;>
    repeat' (reduce_generated stack target data; first | next_generated | skip)
  all_goals simp [Post,Value,footprint,stackRead,dataRead,calleeSaved,
    Result.prepend,cost,Condition.cmp_below,Condition.cmp_above,
    logicalFlags64_preserves,
    cmpFlags64_preserves,BitVec.toNat_add]
  all_goals simp_all only [Nat.min_def,Nat.max_def]
  all_goals repeat' split
  all_goals simp_all <;> omega

/-- One shared checked-binary theorem covers all seven Clang outputs, for
arbitrary initial registers, flags, memory and every undefined-AF sequence. -/
theorem verifies (routine : Routine) (initial : State) (returnAddress payload : Word)
    (code : CodeAt initial.memory initial.rip (bytes routine))
    (ready : ReturnReady initial returnAddress)
    (data : DataReady routine initial payload) (order : OrderReady routine initial)
    (choices : Choices) :
    ∃ result, Sequential.run choices (cost routine) initial = .ok result ∧
      Post routine initial returnAddress payload result ∧
      CheckedTrace (Allowed routine initial) choices initial result := by
  have pc : initial.rip = initial.rip +
      BitVec.ofNat 64 ((graph routine).node (entry routine)).offset := by simp
  obtain ⟨result,actual,post,_,trace⟩ := VCGen.run_sound (valid routine) code pc
    (generated_vc routine initial returnAddress payload ready data order) choices
  exact ⟨result,actual,post,trace⟩

end EDSL.X86.VCGen.Examples
