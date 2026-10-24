/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CounterIncrement
import EDSL.X86.Sequential.CounterArithmetic
import EDSL.OS.TSO64.EffectSimulation.Mixed.Local
import EDSL.OS.TSO64.EffectSimulation.Mixed.CallerContinuation
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Complete local rules and annotations for all 28 nodes of the frozen 86-byte
Clang counter. Each ordinary continuation uses its actual current CPU execution;
the nine locked continuations retain typed INC, joint effect, current authority,
full log and exact Nat count. The independent uint32 contract includes UINT32_MAX,
arbitrary upper RSI and initial flags, actor distinct from tid, and well-formed
nonempty incoming FIFOs. The zero-remainder join leaves skipped RDX unrestricted.

Entry uses only current Pre; the builder takes only its canonical caller and
original stack facts. Shared LocalRules.annotations supplies the finite blocks.
Returned schedules have the exact entire-log count and void ABI postcondition,
without fairness or termination. Native target, protected resource, lifetime,
translation, CET-off and coherent scalar WB assumptions are inherited. Cohort
and lifecycle corpus gates remain; no new corpus credit is claimed.
-/

namespace EDSL.Corpus.V1.CounterClang
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation CounterCommon
open X86.Sequential

/-- Normalize the frozen graph's definitionally equal index type so literal
indices elaborate within the fixed recursion limit. -/
abbrev Index := Fin 28

local instance : NeZero (CounterMixedGraphs.graph .defaultClang).nodes.length :=
  ⟨by decide +kernel⟩

local instance (source destination : Index) :
    Decidable ((CounterMixedGraphs.graph .defaultClang).Edge source destination) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Only the unsigned low32 register participates in loop arithmetic. -/
def u32 (context : Context) (register : Register) : Nat :=
  ((context.registers register).setWidth 32).toNat

def remainder (call : Call) : Nat := call.iterations.toNat % 8

def mainCount (call : Call) : Nat := call.iterations.toNat - remainder call

/-- Remainder-loop facts before its locked INC. RAX still holds the full
requested count; neither the shared word nor arithmetic flags is saved. -/
def RemainderHead (call : Call) (context : Context) (count : Nat) : Prop :=
  0 < remainder call ∧ remainder call < 8 ∧
  u32 context .rcx = remainder call ∧
  u32 context .rdx < remainder call ∧
  count = u32 context .rdx ∧ u32 context .rax = call.iterations.toNat

/-- Between the memory INC and register INC the Nat tally is one ahead of EDX. -/
def RemainderIssued (call : Call) (context : Context) (count : Nat) : Prop :=
  0 < remainder call ∧ remainder call < 8 ∧
  u32 context .rcx = remainder call ∧
  u32 context .rdx < remainder call ∧
  count = u32 context .rdx + 1 ∧ u32 context .rax = call.iterations.toNat

/-- INC EDX is bounded by r, hence cannot wrap width32. -/
def RemainderCompared (call : Call) (context : Context) (count : Nat) : Prop :=
  0 < remainder call ∧ remainder call < 8 ∧
  u32 context .rcx = remainder call ∧
  0 < u32 context .rdx ∧ u32 context .rdx ≤ remainder call ∧
  count = u32 context .rdx ∧ u32 context .rax = call.iterations.toNat

/-- The join at offset30 deliberately places no condition on RCX or RDX.
For r=0 the JE at11 skips both EDX initialization and SUB at28. -/
def PrologueDone (call : Call) (context : Context) (count : Nat) : Prop :=
  count = remainder call ∧ u32 context .rax = mainCount call

/-- Before main INC number j, 0≤j≤7, A still names the pre-ADD amount. -/
def MainHead (call : Call) (context : Context) (count issued : Nat) : Prop :=
  8 ≤ u32 context .rax ∧ u32 context .rax % 8 = 0 ∧
  count + u32 context .rax = call.iterations.toNat + issued

/-- Every one of the 28 decoded nodes has a current register/count assertion.
Flags are constrained only at the consuming branches, by the immediately
preceding TEST/AND/CMP/ADD. PF is never identified with Nat parity. -/
def localInvariant (call : Call) (node : Index) (context : Context) (count : Nat) : Prop :=
  u32 context .rsi = call.iterations.toNat ∧
  match node.val with
  | 0 => count = 0
  | 1 => count = 0 ∧ context.flags.getLsbD 6 = decide (call.iterations.toNat = 0)
  | 2 => count = 0 ∧ 0 < call.iterations.toNat
  | 3 => count = 0 ∧ 0 < call.iterations.toNat ∧
      u32 context .rcx = call.iterations.toNat
  | 4 => count = 0 ∧ 0 < call.iterations.toNat ∧
      u32 context .rcx = call.iterations.toNat ∧ u32 context .rax = call.iterations.toNat
  | 5 => count = 0 ∧ 0 < call.iterations.toNat ∧
      u32 context .rcx = remainder call ∧ u32 context .rax = call.iterations.toNat ∧
      context.flags.getLsbD 6 = decide (remainder call = 0)
  | 6 => count = 0 ∧ 0 < remainder call ∧
      u32 context .rcx = remainder call ∧ u32 context .rax = call.iterations.toNat
  | 7 => RemainderHead call context count
  | 8 => RemainderHead call context count
  | 9 => RemainderIssued call context count
  | 10 => RemainderCompared call context count
  | 11 => RemainderCompared call context count ∧
      context.flags.getLsbD 6 = decide (remainder call = u32 context .rdx)
  | 12 => count = remainder call ∧ u32 context .rdx = remainder call ∧
      u32 context .rax = call.iterations.toNat
  | 13 => count = remainder call ∧ u32 context .rdx = remainder call ∧
      u32 context .rax = call.iterations.toNat
  | 14 => PrologueDone call context count
  | 15 => PrologueDone call context count ∧
      Sequential.Condition.holds .below context.flags = decide (call.iterations.toNat < 8)
  | 16 => MainHead call context count 0
  | 17 => MainHead call context count 0
  | 18 => MainHead call context count 1
  | 19 => MainHead call context count 2
  | 20 => MainHead call context count 3
  | 21 => MainHead call context count 4
  | 22 => MainHead call context count 5
  | 23 => MainHead call context count 6
  | 24 => MainHead call context count 7
  | 25 => MainHead call context count 8
  | 26 => u32 context .rax % 8 = 0 ∧ count + u32 context .rax = call.iterations.toNat ∧
      context.flags.getLsbD 6 = decide (u32 context .rax = 0)
  | 27 => count = call.iterations.toNat
  | _ => False

abbrev invariant (site : Site .defaultClang) (call : Call) :=
  CounterCommon.Inv site call (localInvariant call)

theorem invariant_idle {site : Site .defaultClang} {call : Call}
    {node : Index} {before after : S} {history extended : Log}
    (idle : Mixed.Idle site.profile site.tid (before, history) (after, extended) .arithmetic)
    (prior : invariant site call node before history) :
    invariant site call node after extended := CounterCommon.Inv.idle idle prior

/-- Arithmetic entry follows solely from the independent uint32 argument. -/
theorem initial_arithmetic {site : Site .defaultClang} {call : Call} {state : S}
    (pre : CounterCommon.Pre site call state) :
    localInvariant call (0 : Index) site.original.context 0 := by
  refine ⟨?_, rfl⟩
  exact congrArg BitVec.toNat pre.count

theorem invariant_of_pre {site : Site .defaultClang} {call : Call} {state : S}
    (pre : CounterCommon.Pre site call state) :
    invariant site call (0 : Index) state [] :=
  pre.inv rfl (initial_arithmetic pre)

theorem remainder_lt (call : Call) : remainder call < 8 :=
  Nat.mod_lt _ (by decide)

theorem remainder_le (call : Call) : remainder call ≤ call.iterations.toNat :=
  Nat.mod_le _ _

theorem split_count (call : Call) : remainder call + mainCount call = call.iterations.toNat := by
  have := remainder_le call
  unfold mainCount
  omega

theorem mainCount_multiple (call : Call) : mainCount call % 8 = 0 := by
  have division := Nat.mod_add_div call.iterations.toNat 8
  have bound := remainder_le call
  have multiple : mainCount call = 8 * (call.iterations.toNat / 8) := by
    unfold mainCount remainder at *
    omega
  rw [multiple]
  simp

theorem mainCount_positive {call : Call} (large : 8 ≤ call.iterations.toNat) :
    8 ≤ mainCount call := by
  have split := split_count call
  have remBound := remainder_lt call
  have multiple := mainCount_multiple call
  omega

theorem small_remainder {call : Call} (small : call.iterations.toNat < 8) :
    remainder call = call.iterations.toNat := Nat.mod_eq_of_lt small

/-- A zero remainder imposes no condition on the skipped EDX computation. -/
theorem zero_remainder_join {call : Call} {context : Context}
    (zero : remainder call = 0) (rax : u32 context .rax = call.iterations.toNat) :
    PrologueDone call context 0 := by
  simp [PrologueDone, mainCount, zero, rax]

theorem u32_lt (context : Context) (register : Register) : u32 context register < 2^32 :=
  BitVec.isLt _

/-- Nat refinement of the exact register INC expression, with unrestricted
high32 and flags in the input context. -/
theorem remainder_inc_nat {call : Call} {context : Context} {count : Nat}
    (head : RemainderIssued call context count) :
    ((((context.registers .rdx).setWidth 32 + 1).setWidth 64).toNat) =
      u32 context .rdx + 1 := by
  obtain ⟨_positive, small, _rcx, below, _count, _rax⟩ := head
  have bounded : u32 context .rdx + 1 < 2^32 := by
    have room : 8 < 2^32 := by decide +kernel
    omega
  exact Sequential.counter32_increment_nat (context.registers .rdx)
    (u32 context .rdx) rfl bounded

/-- Actual width32 SUB at28 subtracts r without wrap. -/
theorem remainder_sub_nat {call : Call} {context : Context}
    (rax : u32 context .rax = call.iterations.toNat)
    (rdx : u32 context .rdx = remainder call) :
    ((((context.registers .rax).setWidth 32 -
      (context.registers .rdx).setWidth 32).setWidth 64).toNat) = mainCount call := by
  have ordered : (context.registers .rdx).setWidth 32 ≤
      (context.registers .rax).setWidth 32 := by
    change u32 context .rdx ≤ u32 context .rax
    rw [rax, rdx]
    exact remainder_le call
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64), BitVec.toNat_sub_of_le ordered]
  change u32 context .rax - u32 context .rdx = _
  rw [rax, rdx]
  rfl

/-- This is the signed imm8 ADD expression, using the imported ADD result law;
no SUB-flags identity is asserted. -/
theorem main_add_nat {call : Call} {context : Context} {count : Nat}
    (head : MainHead call context count 8) :
    ((((context.registers .rax).setWidth 32 + (0xf8 : Byte).signExtend 32).setWidth 64).toNat) =
      u32 context .rax - 8 :=
  Sequential.addImm32_minus_eight_nat _ _ rfl head.1

theorem main_add_conservation {call : Call} {context : Context} {count : Nat}
    (head : MainHead call context count 8) :
    count + (u32 context .rax - 8) = call.iterations.toNat := by
  obtain ⟨enough, _multiple, balance⟩ := head
  omega

theorem main_add_multiple {call : Call} {context : Context} {count : Nat}
    (head : MainHead call context count 8) : (u32 context .rax - 8) % 8 = 0 := by
  obtain ⟨enough, multiple, _balance⟩ := head
  omega

/-- The fresh ADD ZF is determined by the ADD result, including unsigned
inputs above INT32_MAX. The ADD carry/overflow/parity flags remain untouched. -/
theorem main_add_zero {call : Call} {context : Context} {count : Nat}
    (head : MainHead call context count 8) :
    (addFlags32 context.flags ((context.registers .rax).setWidth 32)
      ((0xf8 : Byte).signExtend 32)).getLsbD 6 = decide (u32 context .rax - 8 = 0) := by
  rw [(addFlags32_bits ..).2.2.2.1, Bool.beq_eq_decide_eq]
  have result : (((context.registers .rax).setWidth 32 +
      (0xf8 : Byte).signExtend 32)).toNat = u32 context .rax - 8 := by
    simpa only [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using main_add_nat head
  have zero : ((context.registers .rax).setWidth 32 + (0xf8 : Byte).signExtend 32 = 0) ↔
      u32 context .rax - 8 = 0 := by
    rw [← BitVec.toNat_inj, result]
    rfl
  simp only [zero]

theorem main_backedge {call : Call} {context : Context} {count : Nat}
    (head : MainHead call context count 8) :
    (!(addFlags32 context.flags ((context.registers .rax).setWidth 32)
      ((0xf8 : Byte).signExtend 32)).getLsbD 6) =
      decide (0 < u32 context .rax - 8) := by
  rw [main_add_zero head]
  simp only [← decide_not, Nat.pos_iff_ne_zero]

/-- Main-loop exit has exhausted the exact Nat tally, rather than only a
modular difference of shared words. -/
theorem main_exit_count {call : Call} {context : Context} {count : Nat}
    (head : MainHead call context count 8) (zero : u32 context .rax - 8 = 0) :
    count = call.iterations.toNat := by
  have conserved := main_add_conservation head
  omega

/-- The remainder branch uses the fresh CMP's ZF, independently of INC flags. -/
theorem remainder_cmp_zero (context : Context) :
    (cmpFlags32 context.flags ((context.registers .rcx).setWidth 32)
      ((context.registers .rdx).setWidth 32)).getLsbD 6 =
      decide (u32 context .rcx = u32 context .rdx) := by
  exact Sequential.Condition.cmp32_equal_nat context.flags
    ((context.registers .rcx).setWidth 32) ((context.registers .rdx).setWidth 32)

theorem remainder_backedge {call : Call} {context : Context} {count : Nat}
    (compared : RemainderCompared call context count) :
    (!(cmpFlags32 context.flags ((context.registers .rcx).setWidth 32)
      ((context.registers .rdx).setWidth 32)).getLsbD 6) =
      decide (u32 context .rdx < remainder call) := by
  rw [remainder_cmp_zero, compared.2.2.1]
  simp only [← decide_not]
  have equivalent : (¬remainder call = u32 context .rdx) ↔
      u32 context .rdx < remainder call := by
    have bounded := compared.2.2.2.2.1
    omega
  simp only [equivalent]

/-- JB reads the unsigned low32 count and CMP's actual borrow flag. -/
theorem small_count_branch {call : Call} {context : Context}
    (rsi : u32 context .rsi = call.iterations.toNat) :
    Sequential.Condition.holds .below
      (cmpFlags32 context.flags ((context.registers .rsi).setWidth 32)
        ((8 : Byte).signExtend 32)) = decide (call.iterations.toNat < 8) := by
  rw [Sequential.Condition.cmp32_below]
  change decide (u32 context .rsi < 8) = _
  rw [rsi]

/-- Exactly the nine native four-byte INC nodes; no other tag is admitted. -/
def LockedNode (node : Index) : Prop := node.val = 8 ∨ (17 ≤ node.val ∧ node.val ≤ 24)

private def incInstruction : AddRMW64.Instruction := .inc {
  rex := 0x48, modrm := 0x07
  rexSupported := by decide
  indirect := by decide
  groupZero := by decide }

def lockedSuccessor (node : Index) (locked : LockedNode node) : Index :=
  ⟨node.val + 1, by
    change node.val + 1 < 28
    unfold LockedNode at locked
    omega⟩

private theorem locked_cases {node : Index} (locked : LockedNode node) :
    node.val = 8 ∨ node.val = 17 ∨ node.val = 18 ∨ node.val = 19 ∨
    node.val = 20 ∨ node.val = 21 ∨ node.val = 22 ∨ node.val = 23 ∨ node.val = 24 := by
  unfold LockedNode at locked
  omega

private theorem locked_selected (site : Site .defaultClang) (call : Call)
    (node : Index) (locked : LockedNode node) :
    ((descriptor site call).graph.node node).instruction = .locked incInstruction := by
  obtain ⟨n, bound⟩ := node
  rcases locked_cases locked with h | h | h | h | h | h | h | h | h <;>
    dsimp only at h <;> subst n <;> rfl

private theorem locked_edge (site : Site .defaultClang) (call : Call)
    (node : Index) (locked : LockedNode node) :
    (descriptor site call).graph.Edge node (lockedSuccessor node locked) := by
  obtain ⟨n, bound⟩ := node
  rcases locked_cases locked with h | h | h | h | h | h | h | h | h <;>
    dsimp only at h <;> subst n <;>
    apply List.mem_singleton.mpr <;> rfl

private theorem locked_offsets (site : Site .defaultClang) (call : Call)
    (node : Index) (locked : LockedNode node) :
    BitVec.ofNat 64 ((descriptor site call).graph.node node).offset + 4 =
      BitVec.ofNat 64 ((descriptor site call).graph.node (lockedSuccessor node locked)).offset := by
  obtain ⟨n, bound⟩ := node
  rcases locked_cases locked with h | h | h | h | h | h | h | h | h <;>
    dsimp only at h <;> subst n <;> rfl

/-- All locked-node arithmetic ignores flags, because INC's flags are not
the fresh CMP/ADD flags used by a later branch. -/
theorem locked_arithmetic {call : Call} {node : Index} (locked : LockedNode node)
    {before after : Context} {count : Nat}
    (registers : after.registers = before.registers)
    (prior : localInvariant call node before count) :
    localInvariant call (lockedSuccessor node locked) after (count + 1) := by
  obtain ⟨n, bound⟩ := node
  rcases locked_cases locked with h | h | h | h | h | h | h | h | h <;>
    dsimp only at h <;> subst n <;>
    simp only [localInvariant, lockedSuccessor, u32, registers,
      RemainderHead, RemainderIssued, MainHead] at prior ⊢ <;>
    omega

/-- Complete existing `One` obligation at every typed locked INC, including
the native blocked-FIFO branch. The continuation is a real successor invariant,
not an assumed future successful execution or generated block. -/
theorem one_locked {site : Site .defaultClang} {call : Call}
    {node : Index} (locked : LockedNode node) {state : S} {history : Log} {worker : Worker}
    (frame : Mixed.Frame (descriptor site call) state)
    (binding : Mixed.Binding (descriptor site call) node state worker)
    (inv : invariant site call node state history) :
    Mixed.One (descriptor site call) node state
      (Mixed.Follow (descriptor site call) (CounterCommon.Post site call)
        (invariant site call) (invariant site call) node state history) := by
  obtain ⟨boundWorker, current, data, increments, arithmetic⟩ := inv
  have same : boundWorker = worker := Option.some.inj (current.live.symm.trans binding.live)
  subst boundWorker
  apply CounterCommon.oneLocked frame binding data increments
    (locked_selected site call node locked) (show (.locked incInstruction : Decoded .arithmetic) =
      tag .defaultClang from rfl) (show Increment64.IsIncrement incInstruction from True.intro)
    (show incInstruction.base = .rdi from rfl)
  intro af output machine step
  obtain ⟨_identifier, _handle, _cell, _chosen, _target, effect⟩ := step.effect
  have nextPC : machine.state.rip = (descriptor site call).base +
      BitVec.ofNat 64 ((descriptor site call).graph.node (lockedSuccessor node locked)).offset := by
    have rip : machine.state.rip = worker.context.rip + 4 := effect.rip
    rw [rip, binding.pc, BitVec.add_assoc, locked_offsets site call node locked]
  have nextBinding : Mixed.Binding (descriptor site call) (lockedSuccessor node locked)
      (install state site.tid output.1 {worker with context := .ofCPU machine.state})
      {worker with context := .ofCPU machine.state} :=
    ⟨step.live, step.resources, step.running, nextPC⟩
  have nextArithmetic : localInvariant call (lockedSuccessor node locked)
      (.ofCPU machine.state) (Mixed.Counts.logRMW site.tid
        (Mixed.issueLog (descriptor site call) state history af
          (install state site.tid output.1 {worker with context := .ofCPU machine.state},
            .rmw site.tid output.2))) := by
    rw [step.count]
    exact locked_arithmetic locked effect.registers arithmetic
  change Mixed.jump (descriptor site call) (invariant site call) (invariant site call)
    node machine.state.rip _ _
  refine ⟨lockedSuccessor node locked, locked_edge site call node locked, nextPC, ?_⟩
  have nextInvariant : invariant site call (lockedSuccessor node locked)
      (install state site.tid output.1 {worker with context := .ofCPU machine.state})
      (Mixed.issueLog (descriptor site call) state history af
        (install state site.tid output.1 {worker with context := .ofCPU machine.state},
          .rmw site.tid output.2)) :=
    ⟨_, nextBinding, step.data, step.increments, nextArithmetic⟩
  split <;> exact nextInvariant

/-- Ordinary propagation uses the actual current local CPU for every AF
choice. Its inputs describe one instruction's CPU output, never a future run
or generated block. The current FIFO is retained by CallerContinuation. -/
theorem one_next {site : Site .defaultClang} {call : Call}
    {node destination : Index} {state : S} {history : Log} {worker : Worker}
    {instruction : Sequential.Instruction}
    (frame : Mixed.Frame (descriptor site call) state)
    (binding : Mixed.Binding (descriptor site call) node state worker)
    (selected : ((descriptor site call).graph.node node).instruction = .ordinary instruction)
    (only : Sequential.CallerOnly instruction)
    (edge : (descriptor site call).graph.Edge node destination)
    (increments : OwnIncrements site call history)
    (execute : ∀ af, ∃ output : X86.State,
      Sequential.execute (localCPU state worker) instruction af = .ok ⟨.next output, []⟩ ∧
      output.rip = (descriptor site call).base +
        BitVec.ofNat 64 ((descriptor site call).graph.node destination).offset ∧
      LiveData site call state (.ofCPU output) ∧
      localInvariant call destination (.ofCPU output) (Mixed.Counts.logRMW site.tid history)) :
    Mixed.One (descriptor site call) node state
      (Mixed.Follow (descriptor site call) (CounterCommon.Post site call)
        (invariant site call) (invariant site call) node state history) := by
  apply Mixed.One.of_callerContinuation frame binding selected only
    (descriptor_policy site call state)
  intro af
  obtain ⟨output, executed, pc, data, arithmetic⟩ := execute af
  refine ⟨⟨.next output, []⟩, executed, ?_, ?_⟩
  · intro read member
    cases member
  · change Mixed.jump (descriptor site call) (invariant site call) (invariant site call)
      node output.rip
      (install state site.tid state.world {worker with context := .ofCPU output})
      (Mixed.issueLog (descriptor site call) state history af
        (install state site.tid state.world {worker with context := .ofCPU output}, .ordinary site.tid))
    refine ⟨destination, edge, pc, ?_⟩
    have live : (install state site.tid state.world
        {worker with context := .ofCPU output}).workers[site.tid]? =
        some {worker with context := .ofCPU output} :=
      List.getElem?_set_self (List.getElem_of_getElem? binding.live).1
    have afterData : LiveData site call
        (install state site.tid state.world {worker with context := .ofCPU output})
        (.ofCPU output) := ⟨data.pointer, data.stack, data.saved, data.selected⟩
    have nextInvariant : invariant site call destination
        (install state site.tid state.world {worker with context := .ofCPU output})
        (Mixed.issueLog (descriptor site call) state history af
          (install state site.tid state.world {worker with context := .ofCPU output},
            .ordinary site.tid)) := by
      refine ⟨{worker with context := .ofCPU output},
        ⟨live, binding.resources, binding.running, pc⟩, afterData,
        increments.snoc_ordinary _ _ af, ?_⟩
      change localInvariant call destination (.ofCPU output)
        (Mixed.Counts.logRMW site.tid (history ++
          [⟨state, .issue site.tid af,
            (install state site.tid state.world {worker with context := .ofCPU output},
              .ordinary site.tid)⟩]))
      rw [Mixed.Counts.logRMW_snoc_ordinary]
      exact arithmetic
    split <;> exact nextInvariant

/-- Bounded register INC arithmetic produces precisely the CMP-input facts;
the proof uses the real low32 expression and its zero extension. -/
theorem remainder_register_successor {call : Call} {before : Context} {count : Nat}
    (prior : localInvariant call (9 : Index) before count)
    (rip flags : Word) :
    localInvariant call (10 : Index)
      ⟨(fun register => if register = .rdx then
        (((before.registers .rdx).setWidth 32 + 1).setWidth 64) else before.registers register),
        rip, flags⟩ count := by
  obtain ⟨rsi, head⟩ := prior
  change RemainderIssued call before count at head
  have added := remainder_inc_nat head
  have lowAdded : (((before.registers .rdx).setWidth 32 + 1)).toNat =
      u32 before .rdx + 1 := by
    simpa only [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using added
  change u32 _ .rsi = _ ∧ RemainderCompared call _ count
  simp only [u32, RemainderCompared, ↓reduceIte, reduceCtorEq,
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq,
    lowAdded] at *
  unfold RemainderIssued u32 at head
  omega

/-- The exact ADD32 register/flags output establishes node26. In particular,
the ZF assertion comes from ADD, rather than from either the last memory INC
or a substituted SUB-flags formula. -/
theorem main_register_successor {call : Call} {before : Context} {count : Nat}
    (prior : localInvariant call (25 : Index) before count) (rip : Word) :
    let after : Context :=
      ⟨(fun register => if register = .rax then
        (((before.registers .rax).setWidth 32 + (0xf8 : Byte).signExtend 32).setWidth 64)
        else before.registers register), rip,
        addFlags32 before.flags ((before.registers .rax).setWidth 32)
          ((0xf8 : Byte).signExtend 32)⟩
    localInvariant call (26 : Index) after count := by
  obtain ⟨rsi, head⟩ := prior
  dsimp only
  let after : Context :=
    ⟨(fun register => if register = .rax then
      (((before.registers .rax).setWidth 32 + (0xf8 : Byte).signExtend 32).setWidth 64)
      else before.registers register), rip,
      addFlags32 before.flags ((before.registers .rax).setWidth 32)
        ((0xf8 : Byte).signExtend 32)⟩
  change localInvariant call (26 : Index) after count
  have result := main_add_nat head
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] at result
  have rax : u32 after .rax = u32 before .rax - 8 := by
    simpa only [u32, after, ↓reduceIte,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq] using result
  refine ⟨rsi, ?_, ?_, ?_⟩
  · rw [rax]
    exact main_add_multiple head
  · rw [rax]
    exact main_add_conservation head
  · change (addFlags32 before.flags ((before.registers .rax).setWidth 32)
      ((0xf8 : Byte).signExtend 32)).getLsbD 6 = _
    rw [rax]
    exact main_add_zero head

/-- CMP at22 refreshes ZF after both INC instructions. -/
theorem remainder_cmp_successor {call : Call} {before : Context} {count : Nat}
    (prior : localInvariant call (10 : Index) before count) (rip : Word) :
    localInvariant call (11 : Index)
      ⟨before.registers, rip,
        cmpFlags32 before.flags ((before.registers .rcx).setWidth 32)
          ((before.registers .rdx).setWidth 32)⟩ count := by
  obtain ⟨rsi, compared⟩ := prior
  refine ⟨rsi, compared, ?_⟩
  change (cmpFlags32 before.flags ((before.registers .rcx).setWidth 32)
    ((before.registers .rdx).setWidth 32)).getLsbD 6 = _
  rw [remainder_cmp_zero, compared.2.2.1]
  rfl

/-- Subtracting the remainder establishes the offset30 join in Nat arithmetic.
No modulo64 shared-word difference is used to recover the count. -/
theorem remainder_join {call : Call} {context : Context} {count : Nat}
    (counted : count = remainder call)
    (rax : u32 context .rax = call.iterations.toNat)
    (rdx : u32 context .rdx = remainder call) :
    let value := ((context.registers .rax).setWidth 32 - (context.registers .rdx).setWidth 32)
    value.toNat = mainCount call ∧ count + value.toNat = call.iterations.toNat := by
  have value := remainder_sub_nat rax rdx
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] at value
  exact ⟨value, by rw [value, counted]; exact split_count call⟩

/-- Pure branch obligations at24: the bounded post-INC counter is either
strictly below r, or equals r and discharges the prologue tally. -/
theorem remainder_branch_cases {call : Call} {context : Context} {count : Nat}
    (compared : RemainderCompared call context count) :
    (u32 context .rdx < remainder call ∧ RemainderHead call context count) ∨
    (u32 context .rdx = remainder call ∧ count = remainder call) := by
  obtain ⟨positive, small, rcx, _nonzero, bounded, counted, rax⟩ := compared
  by_cases below : u32 context .rdx < remainder call
  · exact .inl ⟨below, positive, small, rcx, below, counted, rax⟩
  · exact .inr ⟨by omega, by omega⟩

/-- Pure branch obligations at33, including the r=0 path with arbitrary RDX. -/
theorem prologue_branch_cases {call : Call} {context : Context} {count : Nat}
    (done : PrologueDone call context count) :
    (call.iterations.toNat < 8 ∧ count = call.iterations.toNat) ∨
    (8 ≤ call.iterations.toNat ∧ MainHead call context count 0) := by
  obtain ⟨counted, rax⟩ := done
  by_cases small : call.iterations.toNat < 8
  · exact .inl ⟨small, counted.trans (small_remainder small)⟩
  · have large : 8 ≤ call.iterations.toNat := by omega
    refine .inr ⟨large, ?_, ?_, ?_⟩
    · rw [rax]
      exact mainCount_positive large
    · rw [rax]
      exact mainCount_multiple call
    · simpa only [Nat.add_zero, counted, rax] using split_count call

/-- Pure branch obligations at83. A nonzero width32 multiple of eight is
at least eight; the zero branch supplies exactly the void-return count. -/
theorem main_branch_cases {call : Call} {context : Context} {count : Nat}
    (multiple : u32 context .rax % 8 = 0)
    (balance : count + u32 context .rax = call.iterations.toNat) :
    (0 < u32 context .rax ∧ MainHead call context count 0) ∨
    (u32 context .rax = 0 ∧ count = call.iterations.toNat) := by
  by_cases zero : u32 context .rax = 0
  · exact .inr ⟨zero, by omega⟩
  · exact .inl ⟨by omega, by omega, multiple, by omega⟩

/-- Actual current ADD EAX,-8, including its own flags and empty read trace. -/
theorem one_main_add {site : Site .defaultClang} {call : Call}
    {state : S} {history : Log} {worker : Worker}
    (frame : Mixed.Frame (descriptor site call) state)
    (binding : Mixed.Binding (descriptor site call) (25 : Index) state worker)
    (inv : invariant site call (25 : Index) state history) :
    Mixed.One (descriptor site call) (25 : Index) state
      (Mixed.Follow (descriptor site call) (CounterCommon.Post site call)
        (invariant site call) (invariant site call) (25 : Index) state history) := by
  obtain ⟨boundWorker, current, data, increments, arithmetic⟩ := inv
  have same : boundWorker = worker := Option.some.inj (current.live.symm.trans binding.live)
  subst boundWorker
  apply one_next (destination := (26 : Index)) frame binding
    (show ((descriptor site call).graph.node (25 : Index)).instruction =
      .ordinary (.addImm32 .rax 0xf8 false) from rfl) True.intro
    (show (CounterMixedGraphs.graph .defaultClang).Edge (25 : Index) (26 : Index)
      from by decide +kernel) increments
  intro af
  let input := localCPU state worker
  let output : X86.State := {
    input.writeRegister .rax
      (((input.registers .rax).setWidth 32 + (0xf8 : Byte).signExtend 32).setWidth 64) with
    rip := input.rip + 3
    flags := addFlags32 input.flags ((input.registers .rax).setWidth 32)
      ((0xf8 : Byte).signExtend 32) }
  refine ⟨output, rfl, ?_, ?_, ?_⟩
  · change worker.context.rip + 3 = _
    rw [binding.pc]
    change (base .defaultClang + 80) + 3 = base .defaultClang + 83
    decide
  · refine ⟨data.pointer, data.stack, ?_, data.selected⟩
    refine ⟨?_, (addFlags32_preserves ..).trans data.saved.2⟩
    intro register member
    have different : register ≠ .rax := by
      intro equal
      subst register
      simp [PureCall.calleeSaved] at member
    change (input.writeRegister .rax
      (((input.registers .rax).setWidth 32 + (0xf8 : Byte).signExtend 32).setWidth 64)).registers
        register = _
    simp only [State.writeRegister, different, ite_false]
    exact data.saved.1 register member
  · exact main_register_successor arithmetic output.rip

/-- Actual current INC EDX; AF and other INC flags retain their own semantics.
The bound r<8 discharges the register's width32 no-wrap obligation. -/
theorem one_remainder_inc {site : Site .defaultClang} {call : Call}
    {state : S} {history : Log} {worker : Worker}
    (frame : Mixed.Frame (descriptor site call) state)
    (binding : Mixed.Binding (descriptor site call) (9 : Index) state worker)
    (inv : invariant site call (9 : Index) state history) :
    Mixed.One (descriptor site call) (9 : Index) state
      (Mixed.Follow (descriptor site call) (CounterCommon.Post site call)
        (invariant site call) (invariant site call) (9 : Index) state history) := by
  obtain ⟨boundWorker, current, data, increments, arithmetic⟩ := inv
  have same : boundWorker = worker := Option.some.inj (current.live.symm.trans binding.live)
  subst boundWorker
  apply one_next (destination := (10 : Index)) frame binding
    (show ((descriptor site call).graph.node (9 : Index)).instruction =
      .ordinary (.inc32 .rdx false) from rfl) True.intro
    (show (CounterMixedGraphs.graph .defaultClang).Edge (9 : Index) (10 : Index)
      from by decide +kernel) increments
  intro af
  let input := localCPU state worker
  let output : X86.State := {
    input.writeRegister .rdx (((input.registers .rdx).setWidth 32 + 1).setWidth 64) with
    rip := input.rip + 2
    flags := incFlags32 input.flags ((input.registers .rdx).setWidth 32) }
  refine ⟨output, rfl, ?_, ?_, ?_⟩
  · change worker.context.rip + 2 = _
    rw [binding.pc]
    change (base .defaultClang + 20) + 2 = base .defaultClang + 22
    decide
  · refine ⟨data.pointer, data.stack, ?_, data.selected⟩
    refine ⟨?_, (incFlags32_preserves ..).trans data.saved.2⟩
    intro register member
    have different : register ≠ .rdx := by
      intro equal
      subst register
      simp [PureCall.calleeSaved] at member
    change (input.writeRegister .rdx
      (((input.registers .rdx).setWidth 32 + 1).setWidth 64)).registers register = _
    simp only [State.writeRegister, different, ite_false]
    exact data.saved.1 register member
  · exact remainder_register_successor arithmetic output.rip output.flags

/-- Actual CMP ECX,EDX refreshes the precise flag consumed by the backedge. -/
theorem one_remainder_cmp {site : Site .defaultClang} {call : Call}
    {state : S} {history : Log} {worker : Worker}
    (frame : Mixed.Frame (descriptor site call) state)
    (binding : Mixed.Binding (descriptor site call) (10 : Index) state worker)
    (inv : invariant site call (10 : Index) state history) :
    Mixed.One (descriptor site call) (10 : Index) state
      (Mixed.Follow (descriptor site call) (CounterCommon.Post site call)
        (invariant site call) (invariant site call) (10 : Index) state history) := by
  obtain ⟨boundWorker, current, data, increments, arithmetic⟩ := inv
  have same : boundWorker = worker := Option.some.inj (current.live.symm.trans binding.live)
  subst boundWorker
  apply one_next (destination := (11 : Index)) frame binding
    (show ((descriptor site call).graph.node (10 : Index)).instruction =
      .ordinary (.cmp32 .rcx .rdx false) from rfl) True.intro
    (show (CounterMixedGraphs.graph .defaultClang).Edge (10 : Index) (11 : Index)
      from by decide +kernel) increments
  intro af
  let input := localCPU state worker
  let output : X86.State := { input with
    rip := input.rip + 2
    flags := cmpFlags32 input.flags ((input.registers .rcx).setWidth 32)
      ((input.registers .rdx).setWidth 32) }
  refine ⟨output, rfl, ?_, ?_, ?_⟩
  · change worker.context.rip + 2 = _
    rw [binding.pc]
    change (base .defaultClang + 22) + 2 = base .defaultClang + 24
    decide
  · exact ⟨data.pointer, data.stack,
      ⟨data.saved.1, (cmpFlags32_preserves ..).trans data.saved.2⟩, data.selected⟩
  · exact remainder_cmp_successor arithmetic output.rip

/-- Exact current ordinary RET continuation. The two site facts are admitted
by the independent Pre: canonical caller and original protected stack slot.
The postcondition is void and leaves RAX unrestricted. -/
theorem one_return {site : Site .defaultClang} {call : Call}
    (callerCanonical : canonical call.returnAddress = true)
    (originalStack : site.original.context.registers .rsp = site.original.resources.callerAddress)
    {state : S} {history : Log} {worker : Worker}
    (frame : Mixed.Frame (descriptor site call) state)
    (binding : Mixed.Binding (descriptor site call) (27 : Index) state worker)
    (inv : invariant site call (27 : Index) state history) :
    Mixed.One (descriptor site call) (27 : Index) state
      (Mixed.Follow (descriptor site call) (CounterCommon.Post site call)
        (invariant site call) (invariant site call) (27 : Index) state history) := by
  obtain ⟨boundWorker, current, data, increments, arithmetic⟩ := inv
  have same : boundWorker = worker := Option.some.inj (current.live.symm.trans binding.live)
  subst boundWorker
  have counted : Mixed.Counts.logRMW site.tid history = call.iterations.toNat := arithmetic.2
  have caller : readWord (localCPU state worker).memory
      ((localCPU state worker).registers .rsp) = .ok call.returnAddress :=
    (binding.current_caller frame data.stack).2
  let input := localCPU state worker
  let output : X86.State := { input.writeRegister .rsp (input.registers .rsp + 8) with
    rip := call.returnAddress }
  have executed (af : Bool) : Sequential.execute input (.legacy .ret) af =
      .ok ⟨.returned output, [⟨.stack, input.registers .rsp, 8⟩]⟩ := by
    simp [Sequential.execute, X86.executeInstruction, X86.executeRet, input,
      caller, callerCanonical, output, Sequential.Instruction.operandReads]
  apply Mixed.One.of_callerContinuation frame binding
    (show ((descriptor site call).graph.node (27 : Index)).instruction =
      .ordinary (.legacy .ret) from rfl)
    (Or.inr rfl) (descriptor_policy site call state)
  intro af
  refine ⟨⟨.returned output, [⟨.stack, input.registers .rsp, 8⟩]⟩, executed af, ?_, ?_⟩
  · intro read member
    have readEq := List.mem_singleton.mp member
    subst read
    exact ⟨rfl, data.stack, rfl⟩
  · change CounterCommon.Post site call
      (install state site.tid state.world
        {worker with context := .ofCPU output, phase := .returned})
      (Mixed.issueLog (descriptor site call) state history af
        (install state site.tid state.world
          {worker with context := .ofCPU output, phase := .returned}, .returned site.tid))
    refine ⟨increments.snoc_returned _ _ af, ?_, ?_⟩
    · change Mixed.Counts.logRMW site.tid (history ++
        [⟨state, .issue site.tid af,
          (install state site.tid state.world
            {worker with context := .ofCPU output, phase := .returned}, .returned site.tid)⟩]) = _
      rw [Mixed.Counts.logRMW_snoc_returned]
      exact counted
    · refine ⟨{worker with context := .ofCPU output, phase := .returned}, ?_,
        binding.resources, rfl, rfl, ?_, ?_⟩
      · exact List.getElem?_set_self (List.getElem_of_getElem? binding.live).1
      · change (input.writeRegister .rsp (input.registers .rsp + 8)).registers .rsp = _
        simp only [State.writeRegister, ↓reduceIte]
        change worker.context.registers .rsp + 8 = site.original.context.registers .rsp + 8
        rw [data.stack, originalStack]
      · refine ⟨?_, data.saved.2⟩
        intro register member
        have different : register ≠ .rsp := by
          intro equal
          subst register
          simp [PureCall.calleeSaved] at member
        change (input.writeRegister .rsp (input.registers .rsp + 8)).registers register = _
        simp only [State.writeRegister, different, ite_false]
        exact data.saved.1 register member

private def pc (offset : Nat) : Word := base .defaultClang + BitVec.ofNat 64 offset

private structure Keeps (before after : X86.State) : Prop where
  registers : ∀ register, register ≠ .rax → register ≠ .rcx → register ≠ .rdx →
    after.registers register = before.registers register
  flags : after.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask

private theorem keeps_plain (before : X86.State) (rip : Word) :
    Keeps before {before with rip := rip} := ⟨fun _ _ _ _ => rfl, rfl⟩

private theorem keeps_flags (before : X86.State) (rip flags : Word)
    (same : flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask) :
    Keeps before {before with rip := rip, flags := flags} := ⟨fun _ _ _ _ => rfl, same⟩

private theorem keeps_write (before : X86.State) (rip flags value : Word)
    (destination : Register) (scratch : destination = .rax ∨ destination = .rcx ∨ destination = .rdx)
    (same : flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask) :
    Keeps before {before.writeRegister destination value with rip := rip, flags := flags} := by
  refine ⟨?_, same⟩
  intro register a c d
  have other : register ≠ destination := by rcases scratch with rfl | rfl | rfl <;> assumption
  simp only [State.writeRegister, other, ite_false]

private theorem Keeps.data {site : Site .defaultClang} {call : Call} {state : S}
    {worker : Worker} {after : X86.State} (data : LiveData site call state worker.context)
    (keeps : Keeps (localCPU state worker) after) : LiveData site call state (.ofCPU after) := by
  refine ⟨(keeps.registers .rdi (by decide) (by decide) (by decide)).trans data.pointer,
    (keeps.registers .rsp (by decide) (by decide) (by decide)).trans data.stack,
    ⟨?_, keeps.flags.trans data.saved.2⟩, data.selected⟩
  intro register member
  have others : register ≠ .rax ∧ register ≠ .rcx ∧ register ≠ .rdx := by
    simp [PureCall.calleeSaved] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact (keeps.registers register others.1 others.2.1 others.2.2).trans
    (data.saved.1 register member)

private theorem low_extend (value : BitVec 32) :
    ((value.setWidth 64).setWidth 32).toNat = value.toNat := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

private theorem beq_zero_nat {width : Nat} (value : BitVec width) (n : Nat)
    (matching : value.toNat = n) : (value == 0) = decide (n = 0) := by
  have zero : value = 0 ↔ value.toNat = 0 := by
    constructor
    · intro same; rw [same]; rfl
    · intro same; apply BitVec.toNat_inj.mp; exact same
  simp only [Bool.beq_eq_decide_eq, zero, matching]

private def OrdinaryNode (node : Index) : Prop :=
  node = 0 ∨ node = 1 ∨ node = 2 ∨ node = 3 ∨ node = 4 ∨ node = 5 ∨
  node = 6 ∨ node = 7 ∨ node = 11 ∨ node = 12 ∨ node = 13 ∨ node = 14 ∨
  node = 15 ∨ node = 16 ∨ node = 26

private theorem branch_taken (before : X86.State) (displacement : Byte) (target : Word)
    (destination : before.rip + 2 + displacement.signExtend 64 = target)
    (safe : canonical target = true) :
    executeShortBranch before true displacement = .ok {before with rip := target} := by
  simp only [executeShortBranch, ↓reduceIte, destination, safe]

private theorem je_next (before : X86.State) (displacement : Byte) (af : Bool) (target : Word)
    (branch : executeShortBranch before (before.flags.getLsbD 6) displacement =
      .ok {before with rip := target}) :
    Sequential.execute before (.je displacement) af =
      .ok ⟨.next {before with rip := target}, []⟩ := by
  change (do return (⟨.next (← executeShortBranch before (before.flags.getLsbD 6) displacement), []⟩ :
    Sequential.Observation)) = _
  rw [branch]; rfl

private theorem jnz_next (before : X86.State) (displacement : Byte) (af : Bool) (target : Word)
    (branch : executeShortBranch before (!before.flags.getLsbD 6) displacement =
      .ok {before with rip := target}) :
    Sequential.execute before (.legacy (.jnz displacement)) af =
      .ok ⟨.next {before with rip := target}, []⟩ := by
  simp only [Sequential.execute, X86.executeInstruction, executeJnz,
    Sequential.Instruction.operandReads, branch, ok_bind, pure_ok]

private theorem jb_next (before : X86.State) (displacement : Byte) (af : Bool) (target : Word)
    (branch : executeShortBranch before (Condition.holds .below before.flags) displacement =
      .ok {before with rip := target}) :
    Sequential.execute before (.jcc .below displacement) af =
      .ok ⟨.next {before with rip := target}, []⟩ := by
  change (do return (⟨.next (← executeShortBranch before (Condition.holds .below before.flags) displacement), []⟩ :
    Sequential.Observation)) = _
  rw [branch]; rfl

/-- Actual CPU execution for the remaining fifteen ordinary nodes. Only the
finite instruction indices are enumerated; counts and register values are universal. -/
private theorem ordinary_next_early (call : Call) (node : Index)
    (ordinary : node = 0 ∨ node = 1 ∨ node = 2 ∨ node = 3 ∨ node = 4 ∨ node = 5 ∨
      node = 6 ∨ node = 7)
    (before : X86.State) (count : Nat) (instruction : Sequential.Instruction)
    (selected : ((CounterMixedGraphs.graph .defaultClang).node node).instruction =
      .ordinary instruction)
    (rip : before.rip = pc ((CounterMixedGraphs.graph .defaultClang).node node).offset)
    (prior : localInvariant call node (.ofCPU before) count) (af : Bool) :
    ∃ after, Sequential.execute before instruction af = .ok ⟨.next after, []⟩ ∧
      ∃ destination : Index, (CounterMixedGraphs.graph .defaultClang).Edge node destination ∧
        after.rip = pc ((CounterMixedGraphs.graph .defaultClang).node destination).offset ∧
        localInvariant call destination (.ofCPU after) count ∧ Keeps before after := by
  rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases selected
    obtain ⟨matching, zero⟩ := prior
    have zf : (logicalFlags32 before.flags
        ((before.registers .rsi).setWidth 32 &&& (before.registers .rsi).setWidth 32) af).getLsbD 6 =
        decide (call.iterations.toNat = 0) := by
      rw [logicalFlags32_zero, BitVec.and_self]
      exact beq_zero_nat _ _ matching
    refine ⟨_, rfl, 1, by decide +kernel, ?_, ⟨matching, zero, zf⟩,
      keeps_flags before _ _ (logicalFlags32_preserves ..)⟩
    change before.rip + 2 = pc 2
    rw [rip]; rfl
  · cases selected
    obtain ⟨matching, zero, zf⟩ := prior
    change before.flags.getLsbD 6 = decide (call.iterations.toNat = 0) at zf
    change before.rip = pc 2 at rip
    by_cases empty : call.iterations.toNat = 0
    · refine ⟨{before with rip := pc 85}, ?_, 27, by decide +kernel, rfl,
        ⟨matching, zero.trans empty.symm⟩, keeps_plain ..⟩
      apply je_next
      have flag : before.flags.getLsbD 6 = true := zf.trans (by simp [empty])
      rw [flag]
      apply branch_taken
      · rw [rip]; rfl
      · decide +kernel
    · refine ⟨{before with rip := before.rip + 2}, ?_, 2, by decide +kernel, ?_,
        ⟨matching, zero, by omega⟩, keeps_plain ..⟩
      · apply je_next
        have flag : before.flags.getLsbD 6 = false := zf.trans (by simp [empty])
        rw [flag]; rfl
      · change before.rip + 2 = pc 4
        rw [rip]; rfl
  · cases selected
    obtain ⟨matching, zero, positive⟩ := prior
    refine ⟨_, rfl, 3, by decide +kernel, ?_, ?_,
      keeps_write before _ _ _ .rcx (.inr (.inl rfl)) rfl⟩
    · change before.rip + 2 = pc 6
      rw [rip]; rfl
    · change u32 _ .rsi = _ ∧ count = 0 ∧ 0 < call.iterations.toNat ∧ _
      refine ⟨matching, zero, positive, ?_⟩
      change ((((before.registers .rsi).setWidth 32).setWidth 64).setWidth 32).toNat = _
      rw [low_extend]
      exact matching
  · cases selected
    obtain ⟨matching, zero, positive, rcx⟩ := prior
    refine ⟨_, rfl, 4, by decide +kernel, ?_, ?_,
      keeps_write before _ _ _ .rax (.inl rfl) rfl⟩
    · change before.rip + 2 = pc 8
      rw [rip]; rfl
    · refine ⟨matching, zero, positive, rcx, ?_⟩
      change ((((before.registers .rsi).setWidth 32).setWidth 64).setWidth 32).toNat = _
      rw [low_extend]
      exact matching
  · cases selected
    obtain ⟨matching, zero, positive, rcx, rax⟩ := prior
    have result := logicalImm32_and_seven_nat (before.registers .rcx) _ rcx
    rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] at result
    have zf := beq_zero_nat _ _ result
    refine ⟨_, rfl, 5, by decide +kernel, ?_, ?_,
      keeps_write before _ _ _ .rcx (.inr (.inl rfl)) (logicalFlags32_preserves ..)⟩
    · change before.rip + 3 = pc 11
      rw [rip]; rfl
    · refine ⟨matching, zero, positive, ?_, rax, ?_⟩
      · change (((LogicalOp.band.eval ((before.registers .rcx).setWidth 32)
          ((7 : Byte).signExtend 32)).setWidth 64).setWidth 32).toNat = _
        rw [low_extend]
        exact result
      · change (logicalFlags32 before.flags _ af).getLsbD 6 = _
        rw [logicalFlags32_zero]
        exact zf
  · cases selected
    obtain ⟨matching, zero, positive, rcx, rax, zf⟩ := prior
    change before.flags.getLsbD 6 = decide (remainder call = 0) at zf
    change before.rip = pc 11 at rip
    by_cases empty : remainder call = 0
    · refine ⟨{before with rip := pc 30}, ?_, 14, by decide +kernel, rfl,
        ⟨matching, ?_⟩, keeps_plain ..⟩
      · apply je_next
        have flag : before.flags.getLsbD 6 = true := zf.trans (by simp [empty])
        rw [flag]
        apply branch_taken
        · rw [rip]; rfl
        · decide +kernel
      · change PrologueDone call _ count
        refine ⟨zero.trans empty.symm, ?_⟩
        change u32 (.ofCPU before) .rax = mainCount call
        simpa only [mainCount, empty, Nat.sub_zero] using rax
    · refine ⟨{before with rip := before.rip + 2}, ?_, 6, by decide +kernel, ?_,
        ⟨matching, zero, by omega, rcx, rax⟩, keeps_plain ..⟩
      · apply je_next
        have flag : before.flags.getLsbD 6 = false := zf.trans (by simp [empty])
        rw [flag]; rfl
      · change before.rip + 2 = pc 13
        rw [rip]; rfl
  · cases selected
    obtain ⟨matching, zero, positive, rcx, rax⟩ := prior
    refine ⟨_, rfl, 7, by decide +kernel, ?_, ?_,
      keeps_write before _ _ _ .rdx (.inr (.inr rfl)) (logicalFlags32_preserves ..)⟩
    · change before.rip + 2 = pc 15
      rw [rip]; rfl
    · change u32 _ .rsi = _ ∧ RemainderHead call _ count
      refine ⟨matching, positive, remainder_lt call, rcx, ?_, ?_, rax⟩
      · exact positive
      · exact zero
  · cases selected
    refine ⟨_, rfl, 8, by decide +kernel, ?_, prior, keeps_plain ..⟩
    change before.rip + 1 = pc 16
    rw [rip]; rfl

private theorem ordinary_next_middle (call : Call) (node : Index)
    (ordinary : node = 11 ∨ node = 12 ∨ node = 13)
    (before : X86.State) (count : Nat) (instruction : Sequential.Instruction)
    (selected : ((CounterMixedGraphs.graph .defaultClang).node node).instruction =
      .ordinary instruction)
    (rip : before.rip = pc ((CounterMixedGraphs.graph .defaultClang).node node).offset)
    (prior : localInvariant call node (.ofCPU before) count) (af : Bool) :
    ∃ after, Sequential.execute before instruction af = .ok ⟨.next after, []⟩ ∧
      ∃ destination : Index, (CounterMixedGraphs.graph .defaultClang).Edge node destination ∧
        after.rip = pc ((CounterMixedGraphs.graph .defaultClang).node destination).offset ∧
        localInvariant call destination (.ofCPU after) count ∧ Keeps before after := by
  rcases ordinary with rfl | rfl | rfl
  · cases selected
    obtain ⟨matching, compared, zf⟩ := prior
    change before.flags.getLsbD 6 = decide (remainder call = u32 (.ofCPU before) .rdx) at zf
    change before.rip = pc 24 at rip
    rcases remainder_branch_cases (context := .ofCPU before) compared with
      ⟨below, head⟩ | ⟨equal, counted⟩
    · have different : ¬remainder call = u32 (.ofCPU before) .rdx := by omega
      refine ⟨{before with rip := pc 16}, ?_, 8, by decide +kernel, rfl,
        ⟨matching, head⟩, keeps_plain ..⟩
      apply jnz_next
      have flag : before.flags.getLsbD 6 = false := zf.trans (by simp [different])
      rw [flag]
      apply branch_taken
      · rw [rip]; rfl
      · decide +kernel
    · refine ⟨{before with rip := before.rip + 2}, ?_, 12, by decide +kernel, ?_,
        ⟨matching, counted, equal, compared.2.2.2.2.2.2⟩, keeps_plain ..⟩
      · apply jnz_next
        have flag : before.flags.getLsbD 6 = true := zf.trans (by simp [equal])
        rw [flag]; rfl
      · change before.rip + 2 = pc 26
        rw [rip]; rfl
  · cases selected
    obtain ⟨matching, counted, rdx, _rax⟩ := prior
    refine ⟨_, rfl, 13, by decide +kernel, ?_, ?_,
      keeps_write before _ _ _ .rax (.inl rfl) rfl⟩
    · change before.rip + 2 = pc 28
      rw [rip]; rfl
    · refine ⟨matching, counted, rdx, ?_⟩
      change ((((before.registers .rsi).setWidth 32).setWidth 64).setWidth 32).toNat = _
      rw [low_extend]
      exact matching
  · cases selected
    obtain ⟨matching, counted, rdx, rax⟩ := prior
    have result := remainder_sub_nat (context := .ofCPU before) rax rdx
    rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] at result
    refine ⟨_, rfl, 14, by decide +kernel, ?_, ?_,
      keeps_write before _ _ _ .rax (.inl rfl) (cmpFlags32_preserves ..)⟩
    · change before.rip + 2 = pc 30
      rw [rip]; rfl
    · refine ⟨matching, counted, ?_⟩
      change (((((before.registers .rax).setWidth 32 -
        (before.registers .rdx).setWidth 32).setWidth 64).setWidth 32).toNat) = _
      rw [low_extend]
      exact result

private theorem ordinary_next_late (call : Call) (node : Index)
    (ordinary : node = 14 ∨ node = 15 ∨ node = 16 ∨ node = 26)
    (before : X86.State) (count : Nat) (instruction : Sequential.Instruction)
    (selected : ((CounterMixedGraphs.graph .defaultClang).node node).instruction =
      .ordinary instruction)
    (rip : before.rip = pc ((CounterMixedGraphs.graph .defaultClang).node node).offset)
    (prior : localInvariant call node (.ofCPU before) count) (af : Bool) :
    ∃ after, Sequential.execute before instruction af = .ok ⟨.next after, []⟩ ∧
      ∃ destination : Index, (CounterMixedGraphs.graph .defaultClang).Edge node destination ∧
        after.rip = pc ((CounterMixedGraphs.graph .defaultClang).node destination).offset ∧
        localInvariant call destination (.ofCPU after) count ∧ Keeps before after := by
  rcases ordinary with rfl | rfl | rfl | rfl
  · cases selected
    obtain ⟨matching, done⟩ := prior
    have fresh := small_count_branch (call := call) (context := .ofCPU before) matching
    refine ⟨_, rfl, 15, by decide +kernel, ?_, ⟨matching, done, fresh⟩,
      keeps_flags before _ _ (cmpFlags32_preserves ..)⟩
    change before.rip + 3 = pc 33
    rw [rip]; rfl
  · cases selected
    obtain ⟨matching, done, cf⟩ := prior
    change Condition.holds .below before.flags = decide (call.iterations.toNat < 8) at cf
    change before.rip = pc 33 at rip
    rcases prologue_branch_cases (context := .ofCPU before) done with
      ⟨small, counted⟩ | ⟨large, head⟩
    · refine ⟨{before with rip := pc 85}, ?_, 27, by decide +kernel, rfl,
        ⟨matching, counted⟩, keeps_plain ..⟩
      apply jb_next
      have flag : Condition.holds .below before.flags = true := cf.trans (by simp [small])
      rw [flag]
      apply branch_taken
      · rw [rip]; rfl
      · decide +kernel
    · have notSmall : ¬call.iterations.toNat < 8 := by omega
      refine ⟨{before with rip := before.rip + 2}, ?_, 16, by decide +kernel, ?_,
        ⟨matching, head⟩, keeps_plain ..⟩
      · apply jb_next
        have flag : Condition.holds .below before.flags = false := cf.trans (by simp [notSmall])
        rw [flag]; rfl
      · change before.rip + 2 = pc 35
        rw [rip]; rfl
  · cases selected
    refine ⟨_, rfl, 17, by decide +kernel, ?_, prior, keeps_plain ..⟩
    change before.rip + 13 = pc 48
    rw [rip]; rfl
  · cases selected
    obtain ⟨matching, multiple, balance, zf⟩ := prior
    change before.flags.getLsbD 6 = decide (u32 (.ofCPU before) .rax = 0) at zf
    change before.rip = pc 83 at rip
    rcases main_branch_cases (context := .ofCPU before) multiple balance with
      ⟨positive, head⟩ | ⟨zero, counted⟩
    · have nonzero : ¬u32 (.ofCPU before) .rax = 0 := by omega
      refine ⟨{before with rip := pc 48}, ?_, 17, by decide +kernel, rfl,
        ⟨matching, head⟩, keeps_plain ..⟩
      apply jnz_next
      have flag : before.flags.getLsbD 6 = false := zf.trans (by simp [nonzero])
      rw [flag]
      apply branch_taken
      · rw [rip]; rfl
      · decide +kernel
    · refine ⟨{before with rip := before.rip + 2}, ?_, 27, by decide +kernel, ?_,
        ⟨matching, counted⟩, keeps_plain ..⟩
      · apply jnz_next
        have flag : before.flags.getLsbD 6 = true := zf.trans (by simp [zero])
        rw [flag]; rfl
      · change before.rip + 2 = pc 85
        rw [rip]; rfl

private theorem ordinary_next (call : Call) (node : Index) (ordinary : OrdinaryNode node)
    (before : X86.State) (count : Nat) (instruction : Sequential.Instruction)
    (selected : ((CounterMixedGraphs.graph .defaultClang).node node).instruction =
      .ordinary instruction)
    (rip : before.rip = pc ((CounterMixedGraphs.graph .defaultClang).node node).offset)
    (prior : localInvariant call node (.ofCPU before) count) (af : Bool) :
    ∃ after, Sequential.execute before instruction af = .ok ⟨.next after, []⟩ ∧
      ∃ destination : Index, (CounterMixedGraphs.graph .defaultClang).Edge node destination ∧
        after.rip = pc ((CounterMixedGraphs.graph .defaultClang).node destination).offset ∧
        localInvariant call destination (.ofCPU after) count ∧ Keeps before after := by
  by_cases early : node.val < 8
  · apply ordinary_next_early call node ?_ before count instruction selected rip prior af
    simp only [Fin.ext_iff]
    omega
  · by_cases middle : node.val < 14
    · apply ordinary_next_middle call node ?_ before count instruction selected rip prior af
      unfold OrdinaryNode at ordinary
      simp only [Fin.ext_iff] at ordinary ⊢
      omega
    · apply ordinary_next_late call node ?_ before count instruction selected rip prior af
      unfold OrdinaryNode at ordinary
      simp only [Fin.ext_iff] at ordinary ⊢
      omega

private theorem ordinary_only (node : Index) (ordinary : OrdinaryNode node)
    (instruction : Sequential.Instruction)
    (selected : ((CounterMixedGraphs.graph .defaultClang).node node).instruction =
      .ordinary instruction) : Sequential.CallerOnly instruction := by
  rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases selected <;> decide +kernel

private theorem one_ordinary {site : Site .defaultClang} {call : Call} {node : Index}
    (ordinary : OrdinaryNode node) {state : S} {history : Log} {worker : Worker}
    (frame : Mixed.Frame (descriptor site call) state)
    (binding : Mixed.Binding (descriptor site call) node state worker)
    (inv : invariant site call node state history) :
    Mixed.One (descriptor site call) node state
      (Mixed.Follow (descriptor site call) (CounterCommon.Post site call)
        (invariant site call) (invariant site call) node state history) := by
  obtain ⟨boundWorker, current, data, increments, arithmetic⟩ := inv
  have same : boundWorker = worker := Option.some.inj (current.live.symm.trans binding.live)
  subst boundWorker
  have selected : ∃ instruction, ((descriptor site call).graph.node node).instruction =
      .ordinary instruction := by
    rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  obtain ⟨instruction, selected⟩ := selected
  apply Mixed.One.of_callerContinuation frame binding selected
    (ordinary_only node ordinary instruction selected) (descriptor_policy site call state)
  intro af
  obtain ⟨output, executed, destination, edge, nextPC, arithmeticNext, keeps⟩ :=
    ordinary_next call node ordinary (localCPU state worker)
      (Mixed.Counts.logRMW site.tid history) instruction selected binding.pc arithmetic af
  refine ⟨⟨.next output, []⟩, executed, ?_, ?_⟩
  · intro read member; cases member
  · change Mixed.jump (descriptor site call) (invariant site call) (invariant site call)
      node output.rip (install state site.tid state.world {worker with context := .ofCPU output})
      (Mixed.issueLog (descriptor site call) state history af
        (install state site.tid state.world {worker with context := .ofCPU output}, .ordinary site.tid))
    refine ⟨destination, edge, nextPC, ?_⟩
    have nextData := Keeps.data data keeps
    have installedData : LiveData site call
        (install state site.tid state.world {worker with context := .ofCPU output}) (.ofCPU output) :=
      ⟨nextData.pointer, nextData.stack, nextData.saved, nextData.selected⟩
    have nextInv : invariant site call destination
        (install state site.tid state.world {worker with context := .ofCPU output})
        (Mixed.issueLog (descriptor site call) state history af
          (install state site.tid state.world {worker with context := .ofCPU output}, .ordinary site.tid)) := by
      refine ⟨{worker with context := .ofCPU output},
        ⟨List.getElem?_set_self (List.getElem_of_getElem? binding.live).1,
          binding.resources, binding.running, nextPC⟩, installedData,
        increments.snoc_ordinary _ _ af, ?_⟩
      change localInvariant call destination (.ofCPU output)
        (Mixed.Counts.logRMW site.tid (history ++
          [⟨state, .issue site.tid af,
            (install state site.tid state.world {worker with context := .ofCPU output},
              .ordinary site.tid)⟩]))
      rw [Mixed.Counts.logRMW_snoc_ordinary]
      exact arithmeticNext
    split <;> exact nextInv

/-- All 28 current instruction obligations, including nine actual LOCK INCs. -/
theorem one {site : Site .defaultClang} {call : Call} {node : Index}
    (canonicalCaller : canonical call.returnAddress = true)
    (originalStack : site.original.context.registers .rsp = site.original.resources.callerAddress)
    {state : S} {history : Log} {worker : Worker}
    (frame : Mixed.Frame (descriptor site call) state)
    (binding : Mixed.Binding (descriptor site call) node state worker)
    (inv : invariant site call node state history) :
    Mixed.One (descriptor site call) node state
      (Mixed.Follow (descriptor site call) (CounterCommon.Post site call)
        (invariant site call) (invariant site call) node state history) := by
  by_cases locked : LockedNode node
  · exact one_locked locked frame binding inv
  by_cases nine : node = 9
  · subst node; exact one_remainder_inc frame binding inv
  by_cases ten : node = 10
  · subst node; exact one_remainder_cmp frame binding inv
  by_cases add : node = 25
  · subst node; exact one_main_add frame binding inv
  by_cases ret : node = 27
  · subst node; exact one_return canonicalCaller originalStack frame binding inv
  apply one_ordinary (node := node) ?_ frame binding inv
  unfold OrdinaryNode
  simp only [Fin.ext_iff] at nine ten add ret ⊢
  unfold LockedNode at locked
  have bound := node.isLt
  omega

/-- Only present caller and stack facts parameterize the complete builder. -/
def rules (site : Site .defaultClang) (call : Call)
    (canonicalCaller : canonical call.returnAddress = true)
    (originalStack : site.original.context.registers .rsp = site.original.resources.callerAddress) :
    Mixed.LocalRules (descriptor site call) (CounterCommon.Post site call) where
  Inv := invariant site call
  idle := invariant_idle
  step := fun _node _state _history _worker frame binding inv =>
    one canonicalCaller originalStack frame binding inv

def annotations (site : Site .defaultClang) (call : Call)
    (canonicalCaller : canonical call.returnAddress = true)
    (originalStack : site.original.context.registers .rsp = site.original.resources.callerAddress) :
    Mixed.Annotations (descriptor site call) (CounterCommon.Post site call) :=
  (rules site call canonicalCaller originalStack).annotations

theorem entry_of_pre {site : Site .defaultClang} {call : Call} {state : S}
    (pre : Pre site call state) :
    Mixed.Entry (annotations site call pre.callerCanonical pre.stack) state (0 : Index) :=
  ⟨pre.admitted, rfl, pre.binding rfl, invariant_of_pre pre⟩

/-- Entire-log exact count for every actual finite schedule that returns.
No fairness, termination, clean upper RSI, empty FIFO or signed input bound. -/
theorem completed_count {site : Site .defaultClang} {call : Call} {initial final : S}
    (pre : Pre site call initial) {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions site.profile .arithmetic = .ok (final, observations))
    {worker : Worker} (live : final.workers[site.tid]? = some worker)
    (returned : worker.phase = .returned) :
    Mixed.Counts.countRMW site.tid observations = call.iterations.toNat :=
  CounterCommon.completed_count (annotations site call pre.callerCanonical pre.stack)
    (entry_of_pre pre) actual live returned

#print axioms ordinary_next
#print axioms one_ordinary
#print axioms one
#print axioms rules
#print axioms annotations
#print axioms entry_of_pre
#print axioms completed_count
#print axioms localInvariant
#print axioms invariant_idle
#print axioms initial_arithmetic
#print axioms invariant_of_pre
#print axioms split_count
#print axioms mainCount_multiple
#print axioms mainCount_positive
#print axioms small_remainder
#print axioms zero_remainder_join
#print axioms remainder_inc_nat
#print axioms remainder_sub_nat
#print axioms main_add_nat
#print axioms main_add_conservation
#print axioms main_add_multiple
#print axioms main_add_zero
#print axioms main_backedge
#print axioms main_exit_count
#print axioms remainder_cmp_zero
#print axioms remainder_backedge
#print axioms small_count_branch
#print axioms locked_arithmetic
#print axioms one_locked
#print axioms one_next
#print axioms remainder_register_successor
#print axioms main_register_successor
#print axioms remainder_cmp_successor
#print axioms remainder_join
#print axioms remainder_branch_cases
#print axioms prologue_branch_cases
#print axioms main_branch_cases
#print axioms one_main_add
#print axioms one_remainder_inc
#print axioms one_remainder_cmp
#print axioms one_return

end EDSL.Corpus.V1.CounterClang

#audit_edsl
