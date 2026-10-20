/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Control
import EDSL.OS.MutexReplay.Ready
import EDSL.X86.ControlFlow

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

/-- Exact instructions at the worker's phase offsets in its 37-byte image. -/
def expected : Phase → Option Instruction
  | .entry => some (.mov32 .rax 1)
  | .acquiring | .releasing => some .exchangeEaxRdi
  | .comparing => some .cmpEaxZero
  | .branching => some (.jnz 0xf4)
  | .loading => some .loadEaxRsi
  | .incrementingFirst | .incrementingSecond => some (.leaEaxRaxDisp8 1)
  | .storingFirst | .storingSecond => some .storeEaxRsi
  | .preparingRelease | .finishing => some (.mov32 .rax 0)
  | .returning => some .ret
  | .completed => none

/-- Decode the actual executable bytes in current shared memory. -/
theorem decode_expected (shared : Mutex.State) (worker : Worker) (instruction : Instruction)
    (context : contextValid worker = true)
    (code : CodeAt (toMemory shared.shared.resources.space) worker.entry.rip bytes)
    (selected : expected worker.phase = some instruction) :
    decodeAt (worker.context.snapshot shared.shared.resources.space) = .ok instruction := by
  have pc := (of_decide_eq_true context).2.2.2
  cases phase : worker.phase with
  | completed => simp [expected, phase] at selected
  | entry =>
    have a := code.2 0 0xb8 (by decide)
    have b := code.2 1 1 (by decide)
    have c := code.2 2 0 (by decide)
    have d := code.2 3 0 (by decide)
    have e := code.2 4 0 (by decide)
    simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
    simp only [expected, phase, Option.some.injEq] at selected
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at a b c d e
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, c, d, e, joinDWord]
  | acquiring =>
    have a := code.2 5 0x87 (by decide)
    have b := code.2 6 0x07 (by decide)
    simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
    simp only [expected, phase, Option.some.injEq] at selected
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, BitVec.add_assoc, joinDWord]
  | comparing =>
    have a := code.2 7 0x83 (by decide)
    have b := code.2 8 0xf8 (by decide)
    have c := code.2 9 0 (by decide)
    simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
    simp only [expected, phase, Option.some.injEq] at selected
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b c
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, c, BitVec.add_assoc, joinDWord]
  | branching =>
    have a := code.2 10 0x75 (by decide)
    have b := code.2 11 0xf4 (by decide)
    simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
    simp only [expected, phase, Option.some.injEq] at selected
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, BitVec.add_assoc, joinDWord]
  | loading =>
    have a := code.2 12 0x8b (by decide)
    have b := code.2 13 0x06 (by decide)
    simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
    simp only [expected, phase, Option.some.injEq] at selected
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, BitVec.add_assoc, joinDWord]
  | incrementingFirst =>
    have a := code.2 14 0x8d (by decide)
    have b := code.2 15 0x40 (by decide)
    have c := code.2 16 1 (by decide)
    simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
    simp only [expected, phase, Option.some.injEq] at selected
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b c
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, c, BitVec.add_assoc, joinDWord]
  | storingFirst =>
    have a := code.2 17 0x89 (by decide)
    have b := code.2 18 0x06 (by decide)
    simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
    simp only [expected, phase, Option.some.injEq] at selected
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, BitVec.add_assoc, joinDWord]
  | incrementingSecond =>
    have a := code.2 19 0x8d (by decide)
    have b := code.2 20 0x40 (by decide)
    have c := code.2 21 1 (by decide)
    simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
    simp only [expected, phase, Option.some.injEq] at selected
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b c
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, c, BitVec.add_assoc, joinDWord]
  | storingSecond =>
    have a := code.2 22 0x89 (by decide)
    have b := code.2 23 0x06 (by decide)
    simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
    simp only [expected, phase, Option.some.injEq] at selected
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, BitVec.add_assoc, joinDWord]
  | preparingRelease =>
    have a := code.2 24 0xb8 (by decide)
    have b := code.2 25 0 (by decide)
    have c := code.2 26 0 (by decide)
    have d := code.2 27 0 (by decide)
    have e := code.2 28 0 (by decide)
    simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
    simp only [expected, phase, Option.some.injEq] at selected
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b c d e
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, c, d, e, BitVec.add_assoc, joinDWord]
  | releasing =>
    have a := code.2 29 0x87 (by decide)
    have b := code.2 30 0x07 (by decide)
    simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
    simp only [expected, phase, Option.some.injEq] at selected
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, BitVec.add_assoc, joinDWord]
  | finishing =>
    have a := code.2 31 0xb8 (by decide)
    have b := code.2 32 0 (by decide)
    have c := code.2 33 0 (by decide)
    have d := code.2 34 0 (by decide)
    have e := code.2 35 0 (by decide)
    simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
    simp only [expected, phase, Option.some.injEq] at selected
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b c d e
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, c, d, e, BitVec.add_assoc, joinDWord]
  | returning =>
    have a := code.2 36 0xc3 (by decide)
    simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
    simp only [expected, phase, Option.some.injEq] at selected
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a
    simp [decodeAt, Threads.Context.snapshot, pc, a, BitVec.add_assoc, joinDWord]

/-- Full private contexts, including untouched registers and flags. -/
def immediateContext (context : Context) (value : BitVec 32) : Context :=
  { context with
    registers := fun register => if register = .rax then value.setWidth 64 else context.registers register
    rip := context.rip + 5 }

def incrementContext (context : Context) : Context :=
  { context with
    registers := fun register => if register = .rax then
      (((context.registers .rax + (1 : Byte).signExtend 64).setWidth 32).setWidth 64)
      else context.registers register
    rip := context.rip + 3 }

def compareContext (context : Context) : Context :=
  { context with
    rip := context.rip + 3
    flags := cmpZeroFlags32 context.flags ((context.registers .rax).setWidth 32) }

def branchContext (context : Context) : Context :=
  { context with rip := if context.flags.getLsbD 6 then context.rip + 2
      else context.rip + 2 + (0xf4 : Byte).signExtend 64 }

def exchangedContext (context : Context) (old : BitVec 32) : Context :=
  { context with
    registers := fun register => if register = .rax then old.setWidth 64 else context.registers register
    rip := context.rip + 2 }

def storedContext (context : Context) : Context :=
  { context with rip := context.rip + 2 }

def returnedContext (context : Context) (target : Word) : Context :=
  { context with
    registers := fun register => if register = .rsp then context.registers .rsp + 8 else context.registers register
    rip := target }

/-- The signed backedge is exactly -12, including modular address arithmetic. -/
theorem branch_backedge (entry : Word) :
    (entry + 10) + 2 + (0xf4 : Byte).signExtend 64 = entry := by
  simp [BitVec.add_assoc]

theorem branch_fallthrough_ne (entry : Word) : entry + 12 ≠ entry := by
  intro same
  have zero : (12 : Word) = 0 := (BitVec.add_right_eq_self).mp same
  contradiction

theorem runNext_of_step (shared : Mutex.State) (context : Context) (instruction : Instruction)
    (output : X86.State)
    (decoded : decodeAt (context.snapshot shared.shared.resources.space) = .ok instruction)
    (stepped : X86.step (context.snapshot shared.shared.resources.space) = .ok (.next output)) :
    runNext shared context instruction = .ok (.ofState output) := by
  simp [runNext, decode, decoded, stepped, Except.mapError]

theorem runAtomic_of_step (shared : Mutex.State) (context : Context) (event : AtomicEvent)
    (output : X86.State)
    (decoded : decodeAt (context.snapshot shared.shared.resources.space) = .ok .exchangeEaxRdi)
    (stepped : X86.step (context.snapshot shared.shared.resources.space) = .ok (.atomic event output)) :
    runAtomic shared context event = .ok (.ofState output) := by
  simp [runAtomic, decode, decoded, stepped, Except.mapError]

theorem immediate_step (shared : Mutex.State) (worker : Worker) (value : BitVec 32)
    (context : contextValid worker = true)
    (code : CodeAt (toMemory shared.shared.resources.space) worker.entry.rip bytes)
    (selected : expected worker.phase = some (.mov32 .rax value)) :
    X86.step (worker.context.snapshot shared.shared.resources.space) =
      .ok (.next ((immediateContext worker.context value).snapshot shared.shared.resources.space)) := by
  have decoded := decode_expected _ _ _ context code selected
  simp only [X86.step, decoded, ok_bind, pure_ok]
  rfl

theorem increment_step (shared : Mutex.State) (worker : Worker)
    (context : contextValid worker = true)
    (code : CodeAt (toMemory shared.shared.resources.space) worker.entry.rip bytes)
    (selected : expected worker.phase = some (.leaEaxRaxDisp8 1)) :
    X86.step (worker.context.snapshot shared.shared.resources.space) =
      .ok (.next ((incrementContext worker.context).snapshot shared.shared.resources.space)) := by
  have decoded := decode_expected _ _ _ context code selected
  simp only [X86.step, decoded, ok_bind, pure_ok]
  rfl

theorem compare_step (shared : Mutex.State) (worker : Worker)
    (context : contextValid worker = true)
    (code : CodeAt (toMemory shared.shared.resources.space) worker.entry.rip bytes)
    (phase : worker.phase = .comparing) :
    X86.step (worker.context.snapshot shared.shared.resources.space) =
      .ok (.next ((compareContext worker.context).snapshot shared.shared.resources.space)) := by
  have decoded := decode_expected _ _ .cmpEaxZero context code (by simp [expected, phase])
  simp only [X86.step, decoded, ok_bind, pure_ok]
  rfl

theorem branch_step (shared : Mutex.State) (worker : Worker)
    (context : contextValid worker = true)
    (code : CodeAt (toMemory shared.shared.resources.space) worker.entry.rip bytes)
    (phase : worker.phase = .branching) :
    X86.step (worker.context.snapshot shared.shared.resources.space) =
      .ok (.next ((branchContext worker.context).snapshot shared.shared.resources.space)) := by
  have decoded := decode_expected _ _ (.jnz 0xf4) context code (by simp [expected, phase])
  have entryByte := code.2 0 0xb8 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at entryByte
  have canonicalEntry := X86.fetch_canonical entryByte
  have pc := (of_decide_eq_true context).2.2.2
  simp only [phase, Phase.offset, reduceCtorEq, ite_false] at pc
  simp only [X86.step, decoded, ok_bind, executeInstruction]
  cases zero : worker.context.flags.getLsbD 6
  all_goals
    simp only [executeJnz, executeShortBranch, Threads.Context.snapshot, branchContext]
    simp only [zero, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_true, ite_false, pc]
    simp [BitVec.add_assoc, canonicalEntry]

theorem return_step (shared : Mutex.State) (identifier : Nat) (worker : Worker)
    (context : contextValid worker = true)
    (ready : WorkerExecutionReady shared.shared identifier worker)
    (phase : worker.phase = .returning) :
    X86.step (worker.context.snapshot shared.shared.resources.space) =
      .ok (.returned ((returnedContext worker.context worker.returnAddress).snapshot shared.shared.resources.space)) := by
  have decoded := decode_expected _ _ .ret context ready.code (by simp [expected, phase])
  have rsp := (of_decide_eq_true context).2.2.1
  simp [phase] at rsp
  simp only [X86.step, decoded, ok_bind]
  simp [executeRet, Threads.Context.snapshot, rsp, ready.stack,
    ready.canonical, returnedContext, X86.State.writeRegister]

/-- Ordinary phases retain the entry operands and unpopped stack. -/
theorem contextValid_fields (worker : Worker) (valid : contextValid worker = true)
    (unfinished : worker.phase ≠ .completed) :
    worker.context.registers .rdi = worker.entry.registers .rdi ∧
    worker.context.registers .rsi = worker.entry.registers .rsi ∧
    worker.context.registers .rsp = worker.entry.registers .rsp ∧
    worker.context.rip = worker.entry.rip + BitVec.ofNat 64 worker.phase.offset := by
  simpa [contextValid, unfinished] using valid

/-- Establish the post-context check directly from the exact constructed context. -/
theorem contextValid_next (worker : Worker) (result : Result)
    (before : contextValid worker = true) (unfinished : worker.phase ≠ .completed)
    (next : nextPhase worker result ≠ .completed)
    (rdi : result.context.registers .rdi = worker.context.registers .rdi)
    (rsi : result.context.registers .rsi = worker.context.registers .rsi)
    (rsp : result.context.registers .rsp = worker.context.registers .rsp)
    (pc : result.context.rip = worker.entry.rip + BitVec.ofNat 64 (nextPhase worker result).offset) :
    contextValid (evolved worker result) = true := by
  obtain ⟨entryRdi, entryRsi, entryRsp, _⟩ := contextValid_fields _ before unfinished
  simp [contextValid, evolved, next, rdi, rsi, rsp, entryRdi, entryRsi, entryRsp, pc]

end EDSL.OS.MutexReplay
