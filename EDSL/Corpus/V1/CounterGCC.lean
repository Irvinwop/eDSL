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
Local annotations for the complete frozen GCC counter, including both RETs.
The count is a Nat count of the full native log, not a modular word difference.
The input has arbitrary upper RSI bits and initial flags. Actual current
caller/atomic authority, the incoming well-formed FIFO and every AF choice
remain those of the production mixed semantics. The return contract is void.

The imported target, resource, lifetime, CET-off and memory-model assumptions
remain in force. Finite returned schedules are conditional: neither fairness
nor termination nor physical compiler/LOCK refinement is claimed. This module
does not grant new corpus credit.
-/

namespace EDSL.Corpus.V1.CounterGCC
open X86 OS OS.TSO64 OS.TSO64.EffectSimulation CounterCommon
open X86.Sequential

abbrev Index := (CounterMixedGraphs.graph .defaultGCC).Index

/-- The frozen graph has seventeen nodes. This instance exposes its nonempty
index type without adding a runtime premise. -/
local instance : NeZero (CounterMixedGraphs.graph .defaultGCC).nodes.length :=
  ⟨by decide +kernel⟩

local instance (source destination : Index) :
    Decidable ((CounterMixedGraphs.graph .defaultGCC).Edge source destination) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Only the low uint32 portion participates in loop arithmetic. -/
def low32 (context : Context) (register : Register) : Nat :=
  ((context.registers register).setWidth 32).toNat

def pc (offset : Nat) : Word := base .defaultGCC + BitVec.ofNat 64 offset

/-- Arithmetic at every instruction boundary, including the interiors between
the two cutpoints. Branch nodes retain the freshly computed ZF explicitly. -/
def arithmetic (call : Call) (node : Index) (context : Context) (count : Nat) : Prop :=
  let n := call.iterations.toNat
  let r := low32 context .rsi
  let a := low32 context .rax
  match node.val with
  | 0 | 1 => count = 0 ∧ r = n
  | 2 => count = 0 ∧ r = n ∧ context.flags.getLsbD 6 = decide (n = 0)
  | 3 => count = 0 ∧ r = n ∧ 0 < n
  | 4 => count = 0 ∧ r = n ∧ a = n - 1 ∧ 0 < n
  | 5 => count = 0 ∧ r = n ∧ a = n - 1 ∧ 0 < n ∧
      context.flags.getLsbD 6 = decide (n % 2 = 0)
  | 6 => count = 0 ∧ r = n ∧ a = n - 1 ∧ 0 < n ∧ n % 2 = 1
  | 7 => count = 1 ∧ r = n ∧ a = n - 1 ∧ 0 < n ∧ n % 2 = 1
  | 8 => count = 1 ∧ r + 1 = n ∧ r % 2 = 0 ∧ a = r
  | 9 => count = 1 ∧ r + 1 = n ∧ r % 2 = 0 ∧ a = r ∧
      context.flags.getLsbD 6 = decide (r = 0)
  | 10 | 11 => 2 ≤ r ∧ r % 2 = 0 ∧ count + r = n
  | 12 => 2 ≤ r ∧ r % 2 = 0 ∧ count + r = n + 1
  | 13 => 2 ≤ r ∧ r % 2 = 0 ∧ count + r = n + 2
  | 14 => r % 2 = 0 ∧ count + r = n ∧
      context.flags.getLsbD 6 = decide (r = 0)
  | 15 | 16 => count = n
  | _ => False

/-- The original stack identity is a present-input fact, carried unchanged
alongside arithmetic so the annotation builder needs no extra stack premise. -/
def localInvariant (site : Site .defaultGCC) (call : Call)
    (node : Index) (context : Context) (count : Nat) : Prop :=
  site.original.context.registers .rsp = site.original.resources.callerAddress ∧
    arithmetic call node context count

def invariant (site : Site .defaultGCC) (call : Call) :
    Mixed.CutAssertion (descriptor site call) :=
  CounterCommon.Inv site call (localInvariant site call)

theorem invariant_idle {site : Site .defaultGCC} {call : Call} {node : Index}
    {before after : S} {history extended : Log}
    (idle : Mixed.Idle site.profile site.tid (before, history) (after, extended) .arithmetic)
    (prior : invariant site call node before history) :
    invariant site call node after extended :=
  CounterCommon.Inv.idle idle prior

theorem initial_invariant {site : Site .defaultGCC} {call : Call} {state : S}
    (pre : Pre site call state) : invariant site call (0 : Index) state [] := by
  apply pre.inv (by rfl)
  refine ⟨pre.stack, rfl, ?_⟩
  exact congrArg BitVec.toNat pre.count

private theorem beq_zero_nat {width : Nat} (value : BitVec width) (n : Nat)
    (matching : value.toNat = n) : (value == 0) = decide (n = 0) := by
  have zero : value = 0 ↔ value.toNat = 0 := by
    constructor
    · intro same; rw [same]; rfl
    · intro same; apply BitVec.toNat_inj.mp; exact same
  simp only [Bool.beq_eq_decide_eq, zero, matching]

private theorem test_self_zero (before : X86.State) (register : Register) (af : Bool) :
    (logicalFlags32 before.flags
      ((before.registers register).setWidth 32 &&& (before.registers register).setWidth 32)
      af).getLsbD 6 = decide (low32 (.ofCPU before) register = 0) := by
  rw [logicalFlags32_zero, BitVec.and_self]
  exact beq_zero_nat _ _ rfl

private theorem test_one_zero (before : X86.State) (n : Nat) (af : Bool)
    (matching : low32 (.ofCPU before) .rsi = n) :
    (logicalFlags8 before.flags ((before.registers .rsi).setWidth 8 &&& 1) af).getLsbD 6 =
      decide (n % 2 = 0) := by
  rw [(logicalFlags8_bits ..).2.2.2.1]
  exact beq_zero_nat _ _ (testImm8_and_one_nat _ _ matching)

private theorem low32_extend (value : BitVec 32) :
    ((value.setWidth 64).setWidth 32).toNat = value.toNat := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

/-- Ordinary nonreturning instructions may change RAX/RSI and arithmetic
flags. All other GPRs, including RDI and RSP, are retained. -/
private structure Keeps (before after : X86.State) : Prop where
  registers : ∀ register, register ≠ .rax → register ≠ .rsi →
    after.registers register = before.registers register
  flags : after.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask

private def Next (call : Call) (node : Index) (count : Nat)
    (before after : X86.State) : Prop :=
  ∃ destination : Index,
    (CounterMixedGraphs.graph .defaultGCC).Edge node destination ∧
    after.rip = pc ((CounterMixedGraphs.graph .defaultGCC).node destination).offset ∧
    arithmetic call destination (.ofCPU after) count ∧ Keeps before after

private theorem keeps_plain (before : X86.State) (rip : Word) :
    Keeps before {before with rip := rip} :=
  ⟨fun _ _ _ => rfl, rfl⟩

private theorem keeps_logical32 (before : X86.State) (rip : Word)
    (result : BitVec 32) (af : Bool) :
    Keeps before {before with rip := rip, flags := logicalFlags32 before.flags result af} :=
  ⟨fun _ _ _ => rfl, logicalFlags32_preserves ..⟩

private theorem keeps_logical8 (before : X86.State) (rip : Word)
    (result : Byte) (af : Bool) :
    Keeps before {before with rip := rip, flags := logicalFlags8 before.flags result af} :=
  ⟨fun _ _ _ => rfl, logicalFlags8_preserves ..⟩

private theorem keeps_write_rax (before : X86.State) (rip value : Word) :
    Keeps before {before.writeRegister .rax value with rip := rip} := by
  refine ⟨?_, rfl⟩
  intro register other _other
  simp only [State.writeRegister, other, ite_false]

private theorem keeps_write_rsi (before : X86.State) (rip value : Word) :
    Keeps before {before.writeRegister .rsi value with rip := rip} := by
  refine ⟨?_, rfl⟩
  intro register _other other
  simp only [State.writeRegister, other, ite_false]

private theorem keeps_sub_rsi (before : X86.State) (rip value : Word) :
    Keeps before {before.writeRegister .rsi value with
      rip := rip
      flags := cmpFlags32 before.flags ((before.registers .rsi).setWidth 32) 2} := by
  refine ⟨?_, cmpFlags32_preserves ..⟩
  intro register _other other
  simp only [State.writeRegister, other, ite_false]

private theorem index_cases (node : Index) :
    node = 0 ∨ node = 1 ∨ node = 2 ∨ node = 3 ∨ node = 4 ∨ node = 5 ∨
    node = 6 ∨ node = 7 ∨ node = 8 ∨ node = 9 ∨ node = 10 ∨ node = 11 ∨
    node = 12 ∨ node = 13 ∨ node = 14 ∨ node = 15 ∨ node = 16 := by
  have bound : node.val < 17 := node.isLt
  have alternatives : node.val = 0 ∨ node.val = 1 ∨ node.val = 2 ∨ node.val = 3 ∨
      node.val = 4 ∨ node.val = 5 ∨ node.val = 6 ∨ node.val = 7 ∨ node.val = 8 ∨
      node.val = 9 ∨ node.val = 10 ∨ node.val = 11 ∨ node.val = 12 ∨ node.val = 13 ∨
      node.val = 14 ∨ node.val = 15 ∨ node.val = 16 := by omega
  simp only [Fin.ext_iff]
  exact alternatives

/-- All ordinary non-RET instructions execute on actual local memory, with
every genuine AF choice. Only the finite instruction indices are split. -/
private theorem ordinary_next (call : Call) (node : Index) (before : X86.State)
    (count : Nat) (instruction : Sequential.Instruction)
    (selected : ((CounterMixedGraphs.graph .defaultGCC).node node).instruction =
      .ordinary instruction)
    (notReturn : instruction ≠ .legacy .ret)
    (rip : before.rip = pc ((CounterMixedGraphs.graph .defaultGCC).node node).offset)
    (prior : arithmetic call node (.ofCPU before) count) (af : Bool) :
    ∃ after, Sequential.execute before instruction af = .ok ⟨.next after, []⟩ ∧
      Next call node count before after := by
  rcases index_cases node with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases selected
    refine ⟨_, rfl, 1, by decide +kernel, ?_, prior, keeps_plain ..⟩
    change before.rip + 4 = pc 4
    rw [rip] <;> rfl
  · cases selected
    obtain ⟨zero, matching⟩ := prior
    refine ⟨_, rfl, 2, by decide +kernel, ?_, ?_, keeps_logical32 ..⟩
    · change before.rip + 2 = pc 6
      rw [rip] <;> rfl
    · exact ⟨zero, matching, (test_self_zero before .rsi af).trans (by rw [matching])⟩
  · cases selected
    obtain ⟨zero, matching, zf⟩ := prior
    change before.flags.getLsbD 6 = _ at zf
    change before.rip = pc 6 at rip
    by_cases empty : call.iterations.toNat = 0
    · refine ⟨{before with rip := pc 47}, ?_, 15, by decide +kernel, rfl, ?_, keeps_plain ..⟩
      · simp only [Sequential.execute, Sequential.Instruction.operandReads, executeShortBranch, zf]
        simp [empty, rip, pc, base, CounterMixedGraphs.function, canonical]
      · exact zero.trans empty.symm
    · refine ⟨{before with rip := before.rip + 2}, ?_, 3, by decide +kernel, ?_, ?_, keeps_plain ..⟩
      · simp only [Sequential.execute, Sequential.Instruction.operandReads, executeShortBranch, zf]
        simp [empty]
      · change before.rip + 2 = pc 8
        rw [rip] <;> rfl
      · exact ⟨zero, matching, by omega⟩
  · cases selected
    obtain ⟨zero, matching, positive⟩ := prior
    refine ⟨_, rfl, 4, by decide +kernel, ?_, ?_, keeps_write_rax ..⟩
    · change before.rip + 3 = pc 11
      rw [rip] <;> rfl
    · refine ⟨zero, matching, ?_, positive⟩
      change (((((Sequential.Address.baseDisp8 .rsi 0xff).eval before).setWidth 32).setWidth 64).setWidth 32).toNat = _
      rw [low32_extend]
      have value := Sequential.Address.baseDisp8_minus_one_nat before .rsi
        call.iterations.toNat matching positive
      rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] at value
      exact value
  · cases selected
    obtain ⟨zero, matching, accumulator, positive⟩ := prior
    refine ⟨_, rfl, 5, by decide +kernel, ?_, ?_, keeps_logical8 ..⟩
    · change before.rip + 4 = pc 15
      rw [rip] <;> rfl
    · exact ⟨zero, matching, accumulator, positive, test_one_zero before _ af matching⟩
  · cases selected
    obtain ⟨zero, matching, accumulator, positive, zf⟩ := prior
    change before.flags.getLsbD 6 = _ at zf
    change before.rip = pc 15 at rip
    by_cases even : call.iterations.toNat % 2 = 0
    · refine ⟨{before with rip := pc 32}, ?_, 11, by decide +kernel, rfl, ?_, keeps_plain ..⟩
      · simp only [Sequential.execute, Sequential.Instruction.operandReads, executeShortBranch, zf]
        simp [even, rip, pc, base, CounterMixedGraphs.function, canonical]
      · change 2 ≤ low32 (.ofCPU before) .rsi ∧
          low32 (.ofCPU before) .rsi % 2 = 0 ∧ count + low32 (.ofCPU before) .rsi = _
        exact ⟨by omega, by rw [matching]; exact even, by omega⟩
    · refine ⟨{before with rip := before.rip + 2}, ?_, 6, by decide +kernel, ?_, ?_, keeps_plain ..⟩
      · simp only [Sequential.execute, Sequential.Instruction.operandReads, executeShortBranch, zf]
        simp [even]
      · change before.rip + 2 = pc 17
        rw [rip] <;> rfl
      · exact ⟨zero, matching, accumulator, positive, by omega⟩
  · cases selected
  · cases selected
    obtain ⟨one, _matching, accumulator, positive, odd⟩ := prior
    refine ⟨_, rfl, 8, by decide +kernel, ?_, ?_, keeps_write_rsi ..⟩
    · change before.rip + 2 = pc 24
      rw [rip] <;> rfl
    · refine ⟨one, ?_, ?_, ?_⟩
      · change ((((before.registers .rax).setWidth 32).setWidth 64).setWidth 32).toNat + 1 = _
        rw [low32_extend]
        change low32 (.ofCPU before) .rax + 1 = call.iterations.toNat
        omega
      · change ((((before.registers .rax).setWidth 32).setWidth 64).setWidth 32).toNat % 2 = 0
        rw [low32_extend]
        change low32 (.ofCPU before) .rax % 2 = 0
        omega
      · change ((before.registers .rax).setWidth 32).toNat =
          ((((before.registers .rax).setWidth 32).setWidth 64).setWidth 32).toNat
        rw [low32_extend]
  · cases selected
    obtain ⟨one, total, even, accumulator⟩ := prior
    refine ⟨_, rfl, 9, by decide +kernel, ?_, ?_, keeps_logical32 ..⟩
    · change before.rip + 2 = pc 26
      rw [rip] <;> rfl
    · exact ⟨one, total, even, accumulator,
        (test_self_zero before .rax af).trans (congrArg (fun n => decide (n = 0)) accumulator)⟩
  · cases selected
    obtain ⟨one, total, even, accumulator, zf⟩ := prior
    change before.flags.getLsbD 6 = _ at zf
    change before.rip = pc 26 at rip
    by_cases empty : low32 (.ofCPU before) .rsi = 0
    · refine ⟨{before with rip := pc 48}, ?_, 16, by decide +kernel, rfl, ?_, keeps_plain ..⟩
      · simp only [Sequential.execute, Sequential.Instruction.operandReads, executeShortBranch, zf]
        simp [empty, rip, pc, base, CounterMixedGraphs.function, canonical]
      · change count = call.iterations.toNat
        omega
    · refine ⟨{before with rip := before.rip + 2}, ?_, 10, by decide +kernel, ?_, ?_, keeps_plain ..⟩
      · simp only [Sequential.execute, Sequential.Instruction.operandReads, executeShortBranch, zf]
        simp [empty]
      · change before.rip + 2 = pc 28
        rw [rip] <;> rfl
      · change 2 ≤ low32 (.ofCPU before) .rsi ∧
          low32 (.ofCPU before) .rsi % 2 = 0 ∧ count + low32 (.ofCPU before) .rsi = _
        exact ⟨by omega, even, by omega⟩
  · cases selected
    refine ⟨_, rfl, 11, by decide +kernel, ?_, prior, keeps_plain ..⟩
    change before.rip + 4 = pc 32
    rw [rip] <;> rfl
  · cases selected
  · cases selected
  · cases selected
    obtain ⟨enough, even, total⟩ := prior
    have result := subImm32_two_nat (before.registers .rsi)
      (low32 (.ofCPU before) .rsi) rfl enough
    rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] at result
    have zf : (cmpFlags32 before.flags ((before.registers .rsi).setWidth 32)
        ((2 : Byte).signExtend 32)).getLsbD 6 =
        decide (low32 (.ofCPU before) .rsi - 2 = 0) := by
      rw [cmpFlags32_zero, Bool.beq_eq_decide_eq]
      have equiv : (before.registers .rsi).setWidth 32 = (2 : Byte).signExtend 32 ↔
          low32 (.ofCPU before) .rsi - 2 = 0 := by
        rw [← BitVec.toNat_inj]
        change low32 (.ofCPU before) .rsi = 2 ↔ _
        omega
      simp only [equiv]
    refine ⟨_, rfl, 14, by decide +kernel, ?_, ?_, keeps_sub_rsi ..⟩
    · change before.rip + 3 = pc 45
      rw [rip] <;> rfl
    · refine ⟨?_, ?_, ?_⟩
      · change (((((before.registers .rsi).setWidth 32 - (2 : Byte).signExtend 32).setWidth 64).setWidth 32).toNat) % 2 = 0
        rw [low32_extend, result]
        omega
      · change count + (((((before.registers .rsi).setWidth 32 - (2 : Byte).signExtend 32).setWidth 64).setWidth 32).toNat) = _
        rw [low32_extend, result]
        omega
      · change (cmpFlags32 before.flags ((before.registers .rsi).setWidth 32)
          ((2 : Byte).signExtend 32)).getLsbD 6 =
          decide ((((((before.registers .rsi).setWidth 32 - (2 : Byte).signExtend 32).setWidth 64).setWidth 32).toNat) = 0)
        rw [low32_extend, result]
        exact zf
  · cases selected
    obtain ⟨even, total, zf⟩ := prior
    change before.flags.getLsbD 6 = _ at zf
    change before.rip = pc 45 at rip
    by_cases empty : low32 (.ofCPU before) .rsi = 0
    · refine ⟨{before with rip := before.rip + 2}, ?_, 15, by decide +kernel, ?_, ?_, keeps_plain ..⟩
      · simp only [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
          executeJnz, executeShortBranch, zf]
        simp [empty]
      · change before.rip + 2 = pc 47
        rw [rip] <;> rfl
      · change count = call.iterations.toNat
        omega
    · refine ⟨{before with rip := pc 32}, ?_, 11, by decide +kernel, rfl, ?_, keeps_plain ..⟩
      · simp only [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
          executeJnz, executeShortBranch, zf]
        simp [empty, rip, pc, base, CounterMixedGraphs.function, canonical]
      · change 2 ≤ low32 (.ofCPU before) .rsi ∧
          low32 (.ofCPU before) .rsi % 2 = 0 ∧ count + low32 (.ofCPU before) .rsi = _
        exact ⟨by omega, even, total⟩
  · cases selected
    exact False.elim (notReturn rfl)
  · cases selected
    exact False.elim (notReturn rfl)

private theorem ordinary_only (node : Index) (instruction : Sequential.Instruction)
    (selected : ((CounterMixedGraphs.graph .defaultGCC).node node).instruction =
      .ordinary instruction) : Sequential.CallerOnly instruction := by
  rcases index_cases node with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases selected <;> decide +kernel

private theorem return_count (call : Call) (node : Index) (context : Context) (count : Nat)
    (selected : ((CounterMixedGraphs.graph .defaultGCC).node node).instruction =
      .ordinary (.legacy .ret)) (prior : arithmetic call node context count) :
    count = call.iterations.toNat := by
  rcases index_cases node with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact prior | cases selected

private theorem Keeps.data {site : Site .defaultGCC} {call : Call} {state : S}
    {worker : Worker} {after : X86.State}
    (data : LiveData site call state worker.context)
    (keeps : Keeps (localCPU state worker) after) :
    LiveData site call state (.ofCPU after) := by
  refine ⟨?_, ?_, ?_, data.selected⟩
  · exact (keeps.registers .rdi (by decide) (by decide)).trans data.pointer
  · exact (keeps.registers .rsp (by decide) (by decide)).trans data.stack
  · refine ⟨?_, keeps.flags.trans data.saved.2⟩
    intro register member
    have others : register ≠ .rax ∧ register ≠ .rsi := by
      simp [PureCall.calleeSaved] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (keeps.registers register others.1 others.2).trans (data.saved.1 register member)

/-- Install the exact ordinary result and append its complete native position.
No FIFO or shared-memory simplification is used to establish the successor. -/
private theorem one_next {site : Site .defaultGCC} {call : Call} {node : Index}
    {state : S} {history : Log} {worker : Worker} {instruction : Sequential.Instruction}
    (frame : Mixed.Frame (descriptor site call) state)
    (binding : Mixed.Binding (descriptor site call) node state worker)
    (data : LiveData site call state worker.context)
    (increments : OwnIncrements site call history)
    (localFact : localInvariant site call node worker.context (Mixed.Counts.logRMW site.tid history))
    (selected : ((descriptor site call).graph.node node).instruction = .ordinary instruction)
    (notReturn : instruction ≠ .legacy .ret) :
    Mixed.One (descriptor site call) node state
      (Mixed.Follow (descriptor site call) (Post site call) (invariant site call)
        (invariant site call) node state history) := by
  have only := ordinary_only node instruction selected
  apply Mixed.One.of_callerContinuation frame binding selected only (descriptor_policy site call state)
  intro af
  obtain ⟨after, executed, destination, edge, nextPC, arithmeticNext, keeps⟩ :=
    ordinary_next call node (localCPU state worker) (Mixed.Counts.logRMW site.tid history)
      instruction selected notReturn binding.pc localFact.2 af
  refine ⟨⟨.next after, []⟩, executed, ?_, ?_⟩
  · intro read member
    cases member
  · change Mixed.jump (descriptor site call) (invariant site call) (invariant site call)
      node after.rip (install state site.tid state.world {worker with context := .ofCPU after})
      (Mixed.issueLog (descriptor site call) state history af
        (install state site.tid state.world {worker with context := .ofCPU after}, .ordinary site.tid))
    refine ⟨destination, edge, nextPC, ?_⟩
    have nextData := Keeps.data data keeps
    have installedData : LiveData site call
        (install state site.tid state.world {worker with context := .ofCPU after}) (.ofCPU after) :=
      ⟨nextData.pointer, nextData.stack, nextData.saved, nextData.selected⟩
    have installedLive : (install state site.tid state.world
        {worker with context := .ofCPU after}).workers[site.tid]? =
        some {worker with context := .ofCPU after} := by
      exact List.getElem?_set_self (List.getElem_of_getElem? binding.live).1
    have nextInv : invariant site call destination
        (install state site.tid state.world {worker with context := .ofCPU after})
        (Mixed.issueLog (descriptor site call) state history af
          (install state site.tid state.world {worker with context := .ofCPU after}, .ordinary site.tid)) := by
      refine ⟨{worker with context := .ofCPU after},
        ⟨installedLive, binding.resources, binding.running, nextPC⟩,
        installedData, increments.snoc_ordinary _ _ af, localFact.1, ?_⟩
      simp only [Mixed.issueLog, Mixed.Counts.logRMW_snoc,
        Mixed.Counts.ownRMW_ordinary, Nat.add_zero]
      exact arithmeticNext
    split <;> exact nextInv

private theorem one_return {site : Site .defaultGCC} {call : Call} {node : Index}
    {state : S} {history : Log} {worker : Worker}
    (canonicalCaller : canonical call.returnAddress = true)
    (frame : Mixed.Frame (descriptor site call) state)
    (binding : Mixed.Binding (descriptor site call) node state worker)
    (data : LiveData site call state worker.context)
    (increments : OwnIncrements site call history)
    (localFact : localInvariant site call node worker.context (Mixed.Counts.logRMW site.tid history))
    (selected : ((descriptor site call).graph.node node).instruction = .ordinary (.legacy .ret)) :
    Mixed.One (descriptor site call) node state
      (Mixed.Follow (descriptor site call) (Post site call) (invariant site call)
        (invariant site call) node state history) := by
  have only : Sequential.CallerOnly (.legacy .ret) := Or.inr rfl
  have currentCaller :
      readWord (localCPU state worker).memory ((localCPU state worker).registers .rsp) =
        .ok call.returnAddress := (binding.current_caller frame data.stack).2
  have count := return_count call node worker.context _ selected localFact.2
  apply Mixed.One.of_callerContinuation frame binding selected only (descriptor_policy site call state)
  intro af
  let after : X86.State :=
    {(localCPU state worker).writeRegister .rsp (worker.context.registers .rsp + 8) with
      rip := call.returnAddress}
  have executed : Sequential.execute (localCPU state worker) (.legacy .ret) af =
      .ok ⟨.returned after, [⟨.stack, worker.context.registers .rsp, 8⟩]⟩ := by
    simp [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
      executeRet, currentCaller, canonicalCaller, after]
    exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  refine ⟨⟨.returned after, [⟨.stack, worker.context.registers .rsp, 8⟩]⟩,
    executed, ?_, ?_⟩
  · intro read member
    have same := List.mem_singleton.mp member
    subst read
    exact ⟨rfl, data.stack, rfl⟩
  · change Post site call
      (install state site.tid state.world {worker with context := .ofCPU after, phase := .returned})
      (Mixed.issueLog (descriptor site call) state history af
        (install state site.tid state.world {worker with context := .ofCPU after, phase := .returned},
          .returned site.tid))
    refine ⟨increments.snoc_returned _ _ af, ?_, ?_⟩
    · simp only [Mixed.issueLog, Mixed.Counts.logRMW_snoc,
        Mixed.Counts.ownRMW_returned, Nat.add_zero]
      exact count
    · refine ⟨{worker with context := .ofCPU after, phase := .returned}, ?_,
        binding.resources, rfl, rfl, ?_, ?_⟩
      · exact List.getElem?_set_self (List.getElem_of_getElem? binding.live).1
      · change worker.context.registers .rsp + 8 = site.original.context.registers .rsp + 8
        rw [data.stack, localFact.1]
      · refine ⟨?_, data.saved.2⟩
        intro register member
        have other : register ≠ .rsp := by
          simp [PureCall.calleeSaved] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        change (if register = .rsp then _ else worker.context.registers register) = _
        rw [ite_eq_right other]
        exact data.saved.1 register member

private def addInstruction : AddRMW64.Instruction := .addImm8 {
  rex := 0x48, modrm := 0x07, imm8 := 1
  rexSupported := by decide +kernel
  indirect := by decide +kernel
  groupZero := by decide +kernel }

private theorem locked_instruction (node : Index) (instruction : AddRMW64.Instruction)
    (selected : ((CounterMixedGraphs.graph .defaultGCC).node node).instruction =
      .locked instruction) : instruction = addInstruction := by
  rcases index_cases node with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases selected <;> rfl

private theorem locked_next (call : Call) (node : Index) (before : Context)
    (after : X86.State) (count : Nat)
    (selected : ((CounterMixedGraphs.graph .defaultGCC).node node).instruction =
      .locked addInstruction)
    (registers : after.registers = before.registers)
    (rip : after.rip = before.rip + 5)
    (bound : before.rip = pc ((CounterMixedGraphs.graph .defaultGCC).node node).offset)
    (prior : arithmetic call node before count) :
    ∃ destination : Index,
      (CounterMixedGraphs.graph .defaultGCC).Edge node destination ∧
      after.rip = pc ((CounterMixedGraphs.graph .defaultGCC).node destination).offset ∧
      arithmetic call destination (.ofCPU after) (count + 1) := by
  have alternatives : node = 6 ∨ node = 11 ∨ node = 12 := by
    rcases index_cases node with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr rfl)
      | cases selected
  rcases alternatives with rfl | rfl | rfl
  · refine ⟨7, by decide +kernel, ?_, ?_⟩
    · change after.rip = pc 22
      change before.rip = pc 17 at bound
      rw [rip, bound] <;> rfl
    · change count = 0 ∧ _ at prior
      change count + 1 = 1 ∧ _
      simp only [low32, Context.ofCPU, registers] at prior ⊢
      exact ⟨by omega, prior.2⟩
  · refine ⟨12, by decide +kernel, ?_, ?_⟩
    · change after.rip = pc 37
      change before.rip = pc 32 at bound
      rw [rip, bound] <;> rfl
    · change 2 ≤ low32 before .rsi ∧ low32 before .rsi % 2 = 0 ∧ count + low32 before .rsi = _ at prior
      change 2 ≤ low32 (.ofCPU after) .rsi ∧ low32 (.ofCPU after) .rsi % 2 = 0 ∧
        count + 1 + low32 (.ofCPU after) .rsi = _
      simp only [low32, Context.ofCPU, registers] at prior ⊢
      omega
  · refine ⟨13, by decide +kernel, ?_, ?_⟩
    · change after.rip = pc 42
      change before.rip = pc 37 at bound
      rw [rip, bound] <;> rfl
    · change 2 ≤ low32 before .rsi ∧ low32 before .rsi % 2 = 0 ∧ count + low32 before .rsi = _ at prior
      change 2 ≤ low32 (.ofCPU after) .rsi ∧ low32 (.ofCPU after) .rsi % 2 = 0 ∧
        count + 1 + low32 (.ofCPU after) .rsi = _
      simp only [low32, Context.ofCPU, registers] at prior ⊢
      omega

private theorem one_locked {site : Site .defaultGCC} {call : Call} {node : Index}
    {state : S} {history : Log} {worker : Worker}
    (frame : Mixed.Frame (descriptor site call) state)
    (binding : Mixed.Binding (descriptor site call) node state worker)
    (data : LiveData site call state worker.context)
    (increments : OwnIncrements site call history)
    (localFact : localInvariant site call node worker.context (Mixed.Counts.logRMW site.tid history))
    (selected : ((descriptor site call).graph.node node).instruction = .locked addInstruction) :
    Mixed.One (descriptor site call) node state
      (Mixed.Follow (descriptor site call) (Post site call) (invariant site call)
        (invariant site call) node state history) := by
  apply CounterCommon.oneLocked frame binding data increments selected rfl rfl rfl
  intro af output machine step
  obtain ⟨_identifier, _handle, _cell, _chosen, _target, effect⟩ := step.effect
  obtain ⟨destination, edge, nextPC, arithmeticNext⟩ := locked_next call node worker.context
    machine.state (Mixed.Counts.logRMW site.tid history) selected effect.registers
    effect.rip binding.pc localFact.2
  change Mixed.jump (descriptor site call) (invariant site call) (invariant site call)
    node machine.state.rip
    (install state site.tid output.1 {worker with context := .ofCPU machine.state})
    (Mixed.issueLog (descriptor site call) state history af
      (install state site.tid output.1 {worker with context := .ofCPU machine.state},
        .rmw site.tid output.2))
  refine ⟨destination, edge, nextPC, ?_⟩
  have nextInv : invariant site call destination
      (install state site.tid output.1 {worker with context := .ofCPU machine.state})
      (Mixed.issueLog (descriptor site call) state history af
        (install state site.tid output.1 {worker with context := .ofCPU machine.state},
          .rmw site.tid output.2)) := by
    refine ⟨{worker with context := .ofCPU machine.state},
      ⟨step.live, step.resources, step.running, nextPC⟩, step.data, step.increments,
      localFact.1, ?_⟩
    rw [step.count]
    exact arithmeticNext
  split <;> exact nextInv

/-- Current local preservation at every actual selected GCC node. -/
theorem one {site : Site .defaultGCC} {call : Call} {node : Index}
    {state : S} {history : Log}
    (canonicalCaller : canonical call.returnAddress = true)
    (frame : Mixed.Frame (descriptor site call) state)
    (prior : invariant site call node state history) :
    Mixed.One (descriptor site call) node state
      (Mixed.Follow (descriptor site call) (Post site call) (invariant site call)
        (invariant site call) node state history) := by
  obtain ⟨worker, binding, data, increments, localFact⟩ := prior
  cases selected : ((descriptor site call).graph.node node).instruction with
  | ordinary instruction =>
    by_cases ret : instruction = .legacy .ret
    · subst instruction
      exact one_return canonicalCaller frame binding data increments localFact selected
    · exact one_next frame binding data increments localFact selected ret
  | locked instruction =>
    have same := locked_instruction node instruction selected
    subst instruction
    exact one_locked frame binding data increments localFact selected

/-- The builder's sole extra input is canonicality of the independent caller.
Entry derives it directly from current-only Pre. -/
def rules (site : Site .defaultGCC) (call : Call)
    (canonicalCaller : canonical call.returnAddress = true) :
    Mixed.LocalRules (descriptor site call) (Post site call) where
  Inv := invariant site call
  idle := invariant_idle
  step := fun _node _state _history _worker frame _binding prior =>
    one canonicalCaller frame prior

def annotations (site : Site .defaultGCC) (call : Call)
    (canonicalCaller : canonical call.returnAddress = true) :
    Mixed.Annotations (descriptor site call) (Post site call) :=
  (rules site call canonicalCaller).annotations

theorem entry_of_pre {site : Site .defaultGCC} {call : Call} {state : S}
    (pre : Pre site call state) :
    Mixed.Entry (annotations site call pre.callerCanonical) state (0 : Index) :=
  ⟨pre.admitted, rfl, pre.binding rfl, initial_invariant pre⟩

/-- Exact count of the entire observation list of every successful finite
production arithmetic schedule whose selected worker has returned. -/
theorem completed_count {site : Site .defaultGCC} {call : Call} {initial final : S}
    (pre : Pre site call initial) {actions : List Action} {observations : List O}
    (actual : TSO64.schedule initial actions site.profile .arithmetic = .ok (final, observations))
    {worker : Worker} (live : final.workers[site.tid]? = some worker)
    (returned : worker.phase = .returned) :
    Mixed.Counts.countRMW site.tid observations = call.iterations.toNat :=
  CounterCommon.completed_count (annotations site call pre.callerCanonical)
    (entry_of_pre pre) actual live returned

#print axioms low32
#print axioms pc
#print axioms arithmetic
#print axioms localInvariant
#print axioms invariant
#print axioms invariant_idle
#print axioms initial_invariant
#print axioms one
#print axioms rules
#print axioms annotations
#print axioms entry_of_pre
#print axioms completed_count

end EDSL.Corpus.V1.CounterGCC

#audit_edsl
