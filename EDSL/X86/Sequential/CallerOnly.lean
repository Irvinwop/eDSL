/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.MemoryTransport
import EDSL.X86.Sequential.CFGTransport
import EDSL.X86.Sequential.MachineChoices

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Caller-only operand effects and exact memory transport for the production
Bool executor. These laws transport complete observations and preserve exact
failure behavior under the stated caller-read agreement.

The finite admission below includes register/control operations and the original
STACK8 RET. It is stricter than `CFG.readOnly`, which also admits DATA loads.
RET agreement concerns the actual `readWord` at the current RSP, including its
error. Identifying that RSP with a protected original caller slot, authenticating
current decoding, and supplying current authority are separate obligations.
No equality of shared RAM, policy stability, successor, or future success is
assumed. The existing ISA semantics and target limitations are unchanged.
-/

namespace EDSL.X86.Sequential

/-- The admitted Bool register/control subset, plus legacy near RET. NOP is
admitted by encoding parameter, without enumerating the padding encodings.
Every DATA access, ordinary store and vector-only flag profile is excluded.
Legacy locked operations and syscalls fail `ContextOnly`; native locked
instructions inhabit a different instruction type and are not admitted here. -/
def CallerOnly : Instruction → Prop
  | .legacy old => ContextOnly old ∨ old = .ret
  | .xorSelf32 _ | .logicalReg32 _ _ _ _ | .logicalImm32 _ _ _ _
  | .test32 _ _ _ | .cmp32 _ _ _ | .cmpReg8 _ _ _ | .subReg32 _ _ _
  | .subImm32 _ _ _ | .cmpImm32 _ _ _
  | .negReg32 _ _ | .bswapReg64 _ | .shrOne64 _ | .rolCL64 _
  | .movzxReg8 _ _ _ | .endbr64IbtDisabled | .nop _
  | .test64 _ _ | .cmp64 _ _ | .cmpImm64 _ _
  | .movReg32 _ _ | .movReg64 _ _ | .movSignImm32 _ _
  | .setcc _ _ _ | .movImm8 _ _ _ | .cmovReg64 _ _ _ | .cmovReg32 _ _ _ _
  | .lea64 _ _ | .addReg64 _ _ | .logicalReg64 _ _ _
  | .xchgReg64 _ _ | .xchgRax64 _ | .addImm64 _ _ | .addImm32 _ _ _
  | .inc32 _ _ | .inc64 _ | .dec64 _ | .je _ | .jcc _ _ | .jmp _ => True
  | .imulReg64 _ _ | .shiftRightImm32 _ _ _ _
  | .movzxMem8 _ _ _ | .cmpMemImm8 _ _ | .cmpMemReg8 _ _
  | .cmpRegMem8 _ _ _ | .cmpMemReg32 _ _ | .addMem32 _ _ | .addMem64 _ _
  | .loadMem32 _ _ | .storeMem32 _ _ | .loadMem64 _ _ | .storeMem64 _ _ => False

instance (instruction : Instruction) : Decidable (CallerOnly instruction) := by
  cases instruction with
  | legacy old =>
    cases old <;> first
      | exact isTrue (Or.inl True.intro)
      | exact isTrue (Or.inr rfl)
      | exact isFalse (fun impossible => impossible.elim id (fun same => by cases same))
  | _ => first | exact isTrue True.intro | exact isFalse id

/-- Uniform vectors may use the production Bool interface for this subset. -/
theorem CallerOnly.boolChoiceProfile {instruction : Instruction}
    (only : CallerOnly instruction) : instruction.boolChoiceProfile = true := by
  cases instruction <;> first | rfl | exact False.elim only

/-- This implication permits reuse of the existing ordinary-result laws.
Its converse is false: read-only DATA loads are outside `CallerOnly`. -/
theorem CallerOnly.readOnly {instruction : Instruction}
    (only : CallerOnly instruction) : CFG.readOnly instruction = true := by
  cases instruction with
  | legacy old =>
    rcases only with contextOnly | rfl
    · cases old <;> simp_all [ContextOnly, CFG.readOnly]
    · rfl
  | _ => first | rfl | exact False.elim only

/-- Neither ordinary store width has an intent, for every input context. -/
theorem CallerOnly.noStore {instruction : Instruction}
    (only : CallerOnly instruction) (input : State) :
    instruction.storeIntent input = none ∧ instruction.storeIntent64 input = none := by
  cases instruction with
  | legacy old =>
    rcases only with contextOnly | rfl
    · cases old <;> simp_all [ContextOnly, Instruction.storeIntent,
        Instruction.storeIntent64, X86.Instruction.storeIntent]
    · exact ⟨rfl, rfl⟩
  | _ => first | exact ⟨rfl, rfl⟩ | exact False.elim only

theorem CallerOnly.unlocked {instruction : Instruction}
    (only : CallerOnly instruction) : instruction.isLocked = false := by
  cases instruction with
  | legacy old =>
    rcases only with contextOnly | rfl
    · cases old <;> simp_all [ContextOnly, Instruction.isLocked, X86.Instruction.isLocked]
    · rfl
  | _ => rfl

/-- Exact prestate operand footprint. RET is the sole reader and uses current
RSP, not a caller-selected address or a cached entry value. -/
theorem CallerOnly.operandReads {instruction : Instruction}
    (only : CallerOnly instruction) (input : State) :
    instruction.operandReads input =
      if instruction = .legacy .ret then [⟨.stack, input.registers .rsp, 8⟩] else [] := by
  cases instruction with
  | legacy old =>
    rcases only with contextOnly | rfl
    · cases old <;> simp_all [ContextOnly, Instruction.operandReads]
    · rfl
  | _ => first | rfl | exact False.elim only

/-- Footprints come from successful production execution. Read success and
its primitive result remain governed by `execute_reads_succeed`. -/
theorem CallerOnly.reads {input : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (only : CallerOnly instruction)
    (actual : execute input instruction af = .ok observation) :
    observation.reads =
      if instruction = .legacy .ret then [⟨.stack, input.registers .rsp, 8⟩] else [] :=
  (execute_reads actual).trans (only.operandReads input)

/-- No DATA read can occur in an actual successful observation. -/
theorem CallerOnly.noDataReads {input : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (only : CallerOnly instruction)
    (actual : execute input instruction af = .ok observation) (read : Read)
    (member : read ∈ observation.reads) : read.kind ≠ .data := by
  rw [only.reads actual] at member
  split at member
  · simp only [List.mem_singleton] at member
    subst read
    intro impossible
    cases impossible
  · cases member

/-- Every actual success is ordinary or the original RET, with complete
memory preserved. In particular atomic and syscall results are impossible. -/
theorem CallerOnly.result {input : State} {instruction : Instruction} {af : Bool}
    {observation : Observation} (only : CallerOnly instruction)
    (actual : execute input instruction af = .ok observation) :
    ∃ output, output.memory = input.memory ∧
      (observation.result = .next output ∨
        (observation.result = .returned output ∧ instruction = .legacy .ret)) := by
  obtain ⟨output, next | ⟨returned, ret⟩⟩ := CFG.execute_result only.readOnly actual
  · exact ⟨output, CFG.execute_next_memory only.readOnly actual next, Or.inl next⟩
  · exact ⟨output, CFG.execute_returned_memory only.readOnly actual returned,
      Or.inr ⟨returned, ret⟩⟩

/-- Change only the memory carried by the result, retaining the complete
read trace and all registers, RIP, flags and result constructors. -/
def Observation.mapMemory (function : Memory → Memory) (observation : Observation) : Observation :=
  { observation with result := observation.result.mapMemory function }

private theorem contextOnly_reads (input : State) (old : X86.Instruction)
    (contextOnly : ContextOnly old) :
    (Instruction.legacy old).operandReads input = [] := by
  cases old <;> simp_all [ContextOnly, Instruction.operandReads]

private theorem shortBranch_memory_eq (input : State) (memory : Memory)
    (taken : Bool) (displacement : Byte) :
    executeShortBranch { input with memory := memory } taken displacement =
      (executeShortBranch input taken displacement).map
        (fun output => { output with memory := memory }) := by
  unfold executeShortBranch
  cases taken <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · rfl
  · split <;> rfl

private theorem ret_memory_eq (input : State) (memory : Memory)
    (caller : readWord memory (input.registers .rsp) =
      readWord input.memory (input.registers .rsp)) :
    executeRet { input with memory := memory } =
      (executeRet input).map (fun output => { output with memory := memory }) := by
  unfold executeRet
  dsimp only
  rw [caller]
  cases readWord input.memory (input.registers .rsp) with
  | error fault => rfl
  | ok target =>
    simp only [ok_bind]
    split <;> rfl

/-- Exact transport of the production observation, including every error.
The sole memory premise is conditional on actual RET and compares its actual
STACK8 primitive, allowing equal faults as well as equal returned words.
For success the output CPU contains `memory`; its entire context and read
trace agree with the original observation. No code or permission-map equality
is required by execution of an already decoded instruction. -/
theorem CallerOnly.execute_memory_eq {instruction : Instruction}
    (only : CallerOnly instruction) (input : State) (memory : Memory) (af : Bool)
    (caller : instruction = .legacy .ret →
      readWord memory (input.registers .rsp) = readWord input.memory (input.registers .rsp)) :
    execute { input with memory := memory } instruction af =
      (execute input instruction af).map (Observation.mapMemory (fun _ => memory)) := by
  cases instruction with
  | legacy old =>
    rcases only with contextOnly | rfl
    · simp only [execute_legacy,
        contextOnly_reads { input with memory := memory } old contextOnly,
        contextOnly_reads input old contextOnly]
      rw [X86.execute_contextOnly_memory_eq input memory old contextOnly]
      cases X86.executeInstruction input old <;> rfl
    · simp only [execute, X86.executeInstruction]
      rw [ret_memory_eq input memory (caller rfl)]
      cases executeRet input <;> rfl
  | lea64 destination address => cases address <;> rfl
  | je displacement =>
    simp only [execute_je]
    rw [shortBranch_memory_eq input memory (input.flags.getLsbD 6) displacement]
    cases executeShortBranch input (input.flags.getLsbD 6) displacement <;> rfl
  | jcc condition displacement =>
    simp only [execute_jcc]
    rw [shortBranch_memory_eq input memory (condition.holds input.flags) displacement]
    cases executeShortBranch input (condition.holds input.flags) displacement <;> rfl
  | jmp displacement =>
    simp only [execute_jmp]
    rw [shortBranch_memory_eq input memory true displacement]
    cases executeShortBranch input true displacement <;> rfl
  | _ => first | rfl | exact False.elim only

/-- Memory replacement neither masks an error nor creates a new one. -/
theorem CallerOnly.execute_error_iff {instruction : Instruction}
    (only : CallerOnly instruction) (input : State) (memory : Memory) (af : Bool)
    (caller : instruction = .legacy .ret →
      readWord memory (input.registers .rsp) = readWord input.memory (input.registers .rsp))
    (fault : Error) :
    execute { input with memory := memory } instruction af = .error fault ↔
      execute input instruction af = .error fault := by
  rw [only.execute_memory_eq input memory af caller]
  cases execute input instruction af <;> simp [Except.map]

/-- The same observation law for the uniform vectors used by ordinary
resumable heads, through the existing supported-profile bridge. -/
theorem CallerOnly.executeWith_uniform_memory_eq {instruction : Instruction}
    (only : CallerOnly instruction) (input : State) (memory : Memory) (af : Bool)
    (caller : instruction = .legacy .ret →
      readWord memory (input.registers .rsp) = readWord input.memory (input.registers .rsp)) :
    executeWith { input with memory := memory } instruction (FlagChoices.uniform af) =
      (executeWith input instruction (FlagChoices.uniform af)).map
        (Observation.mapMemory (fun _ => memory)) := by
  rw [executeWith_uniform { input with memory := memory } instruction af only.boolChoiceProfile,
    executeWith_uniform input instruction af only.boolChoiceProfile]
  exact only.execute_memory_eq input memory af caller

end EDSL.X86.Sequential
