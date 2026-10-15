/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CounterThreads.Framing
import EDSL.OS.Threads.Machine
import EDSL.X86.ControlFlow

namespace EDSL.OS.CounterThreads
open X86 AddressSpace

theorem checkedAdvance_success (shared : Atomics.State) (worker : Worker) (context : Context)
    (event : Option AtomicEvent)
    (valid : PrivateValid { worker with phase := nextPhase worker.phase context, context := context }) :
    checkedAdvance shared worker context event =
      .ok ⟨shared, { worker with phase := nextPhase worker.phase context, context := context }, event⟩ := by
  simp [checkedAdvance, valid]

theorem decode_expected (shared : Atomics.State) (identifier : Nat) (worker : Worker) (instruction : Instruction)
    (valid : WorkerValid shared identifier worker) (live : expected worker.phase = some instruction) :
    decodeAt (worker.context.snapshot shared.shared.resources.space) = .ok instruction := by
  have code := valid.executable
  have privateContext := valid.privateContext
  cases phase : worker.phase with
  | completed => simp [expected, phase] at live
  | entry =>
    have a := code.2 0 0xe3 (by decide)
    have b := code.2 1 0x0b (by decide)
    simp only [PrivateValid, phase] at privateContext
    have pc := privateContext.2.2.2.1
    simp only [expected, phase, Option.some.injEq] at live
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at a b
    simp [decodeAt, Threads.Context.snapshot, pc, a, b]
  | preparing =>
    have a := code.2 2 0xb8 (by decide)
    have b := code.2 3 1 (by decide)
    have c := code.2 4 0 (by decide)
    have d := code.2 5 0 (by decide)
    have e := code.2 6 0 (by decide)
    simp only [PrivateValid, phase] at privateContext
    have pc := privateContext.2.2.2.1
    simp only [expected, phase, Option.some.injEq] at live
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b c d e
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, c, d, e, BitVec.add_assoc, joinDWord]
  | adding =>
    have a := code.2 7 0xf0 (by decide)
    have b := code.2 8 0x0f (by decide)
    have c := code.2 9 0xc1 (by decide)
    have d := code.2 10 0x07 (by decide)
    simp only [PrivateValid, phase] at privateContext
    have pc := privateContext.2.2.2.1
    simp only [expected, phase, Option.some.injEq] at live
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b c d
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, c, d, BitVec.add_assoc]
  | backedge =>
    have a := code.2 11 0xe2 (by decide)
    have b := code.2 12 0xf5 (by decide)
    simp only [PrivateValid, phase] at privateContext
    have pc := privateContext.2.2.2.1
    simp only [expected, phase, Option.some.injEq] at live
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, BitVec.add_assoc]
  | finishing =>
    have a := code.2 13 0xb8 (by decide)
    have b := code.2 14 0 (by decide)
    have c := code.2 15 0 (by decide)
    have d := code.2 16 0 (by decide)
    have e := code.2 17 0 (by decide)
    simp only [PrivateValid, phase] at privateContext
    have pc := privateContext.2.2.2.1
    simp only [expected, phase, Option.some.injEq] at live
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a b c d e
    simp [decodeAt, Threads.Context.snapshot, pc, a, b, c, d, e, BitVec.add_assoc, joinDWord]
  | returning =>
    have a := code.2 18 0xc3 (by decide)
    simp only [PrivateValid, phase] at privateContext
    have pc := privateContext.2.2.2.1
    simp only [expected, phase, Option.some.injEq] at live
    subst instruction
    simp only [BitVec.ofNat_eq_ofNat] at a
    simp [decodeAt, Threads.Context.snapshot, pc, a]

def entryContext (context : Context) : Context :=
  { context with rip := context.rip + if context.registers .rcx = 0 then 13 else 2 }

def immediateContext (context : Context) (value : BitVec 32) : Context :=
  { context with
    registers := fun register => if register = .rax then value.setWidth 64 else context.registers register
    rip := context.rip + 5 }

def addedContext (context : Context) (old : BitVec 32) : Context :=
  { context with
    registers := fun register => if register = .rax then old.setWidth 64 else context.registers register
    rip := context.rip + 4
    flags := addFlags32 context.flags old ((context.registers .rax).setWidth 32) }

def loopContext (context : Context) : Context :=
  let count := context.registers .rcx - 1
  { context with
    registers := fun register => if register = .rcx then count else context.registers register
    rip := if count = 0 then context.rip + 2 else context.rip + 2 + (0xf5 : Byte).signExtend 64 }

def returnedContext (context : Context) (target : Word) : Context :=
  { context with
    registers := fun register => if register = .rsp then context.registers .rsp + 8 else context.registers register
    rip := target }

theorem entry_step (shared : Atomics.State) (identifier : Nat) (worker : Worker)
    (valid : WorkerValid shared identifier worker) (phase : worker.phase = .entry) :
    X86.step (worker.context.snapshot shared.shared.resources.space) =
      .ok (.next ((entryContext worker.context).snapshot shared.shared.resources.space)) := by
  have decoded := decode_expected shared identifier worker (.jrcxz 0x0b) valid (by simp [expected, phase])
  have exit := valid.executable.2 13 0xb8 (by decide)
  have canonicalExit := X86.fetch_canonical exit
  have p := valid.privateContext
  simp only [PrivateValid, phase] at p
  have pc := p.2.2.2.1
  simp only [X86.step, decoded, ok_bind]
  by_cases zero : worker.context.registers .rcx = 0
  · simp only [BitVec.ofNat_eq_ofNat] at zero
    simp [executeJrcxz, executeShortBranch, Threads.Context.snapshot,
      pc, zero, canonicalExit, entryContext, BitVec.add_assoc]
  · simp only [BitVec.ofNat_eq_ofNat] at zero
    simp [executeJrcxz, executeShortBranch, Threads.Context.snapshot,
      zero, entryContext]

theorem immediate_step (shared : Atomics.State) (identifier : Nat) (worker : Worker) (value : BitVec 32)
    (valid : WorkerValid shared identifier worker) (selected : expected worker.phase = some (.mov32 .rax value)) :
    X86.step (worker.context.snapshot shared.shared.resources.space) =
      .ok (.next ((immediateContext worker.context value).snapshot shared.shared.resources.space)) := by
  have decoded := decode_expected shared identifier worker (.mov32 .rax value) valid selected
  simp only [X86.step, decoded, ok_bind, pure_ok]
  rfl

theorem adding_step (state : Atomics.State) (identifier : Nat) (worker : Worker) (result : Atomics.State × BitVec 32)
    (valid : WorkerValid state identifier worker) (phase : worker.phase = .adding)
    (success : Atomics.fetchAdd state (principal identifier) worker.handle 1 = .ok result) :
    X86.step (worker.context.snapshot state.shared.resources.space) = .ok (.atomic
      ⟨worker.entry.registers .rdi, result.2, result.2 + 1⟩
      ((addedContext worker.context result.2).snapshot result.1.shared.resources.space)) := by
  have decoded := decode_expected state identifier worker .fetchAddEaxRdi valid (by simp [expected, phase])
  obtain ⟨handle, authorized, address⟩ := valid.authorized
  have p := valid.privateContext
  simp only [PrivateValid, phase] at p
  have operand : (worker.context.snapshot state.shared.resources.space).registers .rdi = handle.address :=
    p.1.trans address.symm
  have replacement : ((worker.context.snapshot state.shared.resources.space).registers .rax).setWidth 32 = 1 := by
    simp [Threads.Context.snapshot, p.2.2.2.2.2]
  have actual := Atomics.fetchAdd_step state (principal identifier) worker.handle 1 result handle
    (worker.context.snapshot state.shared.resources.space) success authorized rfl operand replacement decoded
  simpa only [address, Atomics.afterFetchAdd, addedContext, Threads.Context.snapshot, X86.State.writeRegister] using actual

theorem return_step (shared : Atomics.State) (identifier : Nat) (worker : Worker)
    (valid : WorkerValid shared identifier worker) (phase : worker.phase = .returning) :
    X86.step (worker.context.snapshot shared.shared.resources.space) =
      .ok (.returned ((returnedContext worker.context worker.returnAddress).snapshot shared.shared.resources.space)) := by
  have decoded := decode_expected shared identifier worker .ret valid (by simp [expected, phase])
  have p := valid.privateContext
  simp only [PrivateValid, phase] at p
  simp only [X86.step, decoded, ok_bind]
  simp [executeRet, Threads.Context.snapshot, p.2.2.1, valid.target,
    valid.canonical, returnedContext, X86.State.writeRegister]

theorem entry_private (worker : Worker) (valid : PrivateValid worker) (phase : worker.phase = .entry) :
    PrivateValid { worker with phase := nextPhase worker.phase (entryContext worker.context), context := entryContext worker.context } := by
  simp only [PrivateValid, phase] at valid
  obtain ⟨rdi, bound, rsp, pc, _⟩ := valid
  by_cases zero : worker.context.registers .rcx = 0 <;>
    simp only [BitVec.ofNat_eq_ofNat] at zero <;>
    simp [PrivateValid, nextPhase, phase, entryContext, zero, rdi, bound, rsp, pc]

theorem preparing_private (worker : Worker) (valid : PrivateValid worker) (phase : worker.phase = .preparing) :
    PrivateValid { worker with phase := nextPhase worker.phase (immediateContext worker.context 1), context := immediateContext worker.context 1 } := by
  simp only [PrivateValid, phase] at valid
  obtain ⟨rdi, bound, rsp, pc, count⟩ := valid
  simp only [BitVec.ofNat_eq_ofNat] at count
  simp [PrivateValid, nextPhase, phase, immediateContext, rdi, bound, rsp, pc, count, BitVec.add_assoc]

theorem adding_private (worker : Worker) (old : BitVec 32) (valid : PrivateValid worker) (phase : worker.phase = .adding) :
    PrivateValid { worker with phase := nextPhase worker.phase (addedContext worker.context old), context := addedContext worker.context old } := by
  simp only [PrivateValid, phase] at valid
  obtain ⟨rdi, bound, rsp, pc, count, _⟩ := valid
  simp only [BitVec.ofNat_eq_ofNat] at count
  simp [PrivateValid, nextPhase, phase, addedContext, rdi, bound, rsp, pc, count, BitVec.add_assoc]

theorem finishing_private (worker : Worker) (valid : PrivateValid worker) (phase : worker.phase = .finishing) :
    PrivateValid { worker with phase := nextPhase worker.phase (immediateContext worker.context 0), context := immediateContext worker.context 0 } := by
  simp only [PrivateValid, phase] at valid
  obtain ⟨rdi, bound, rsp, pc, count⟩ := valid
  simp [PrivateValid, nextPhase, phase, immediateContext, rdi, rsp, pc, count, BitVec.add_assoc]

theorem returning_private (worker : Worker) (valid : PrivateValid worker) (phase : worker.phase = .returning) :
    PrivateValid { worker with
      phase := nextPhase worker.phase (returnedContext worker.context worker.returnAddress)
      context := returnedContext worker.context worker.returnAddress } := by
  simp only [PrivateValid, phase] at valid
  obtain ⟨rdi, bound, rsp, _, count, rax⟩ := valid
  simp [PrivateValid, nextPhase, phase, returnedContext, rdi, rsp, count, rax]

theorem loop_step (shared : Atomics.State) (identifier : Nat) (worker : Worker)
    (valid : WorkerValid shared identifier worker) (phase : worker.phase = .backedge) :
    X86.step (worker.context.snapshot shared.shared.resources.space) =
      .ok (.next ((loopContext worker.context).snapshot shared.shared.resources.space)) := by
  have decoded := decode_expected shared identifier worker (.loopRcx 0xf5) valid (by simp [expected, phase])
  have head := valid.executable.2 2 0xb8 (by decide)
  have canonicalHead := X86.fetch_canonical head
  have p := valid.privateContext
  simp only [PrivateValid, phase] at p
  have pc := p.2.2.2.1
  simp only [X86.step, decoded, ok_bind]
  by_cases zero : worker.context.registers .rcx - 1 = 0
  all_goals
    simp only [BitVec.ofNat_eq_ofNat] at zero
    simp [executeLoop, executeShortBranch, Threads.Context.snapshot, X86.State.writeRegister,
      loopContext, zero, pc, canonicalHead, BitVec.add_assoc]

theorem decrement_count (count : Word) (nonzero : count ≠ 0) : (count - 1).toNat + 1 = count.toNat := by
  have positive : 0 < count.toNat := BitVec.toNat_pos_of_ne_zero nonzero
  rw [BitVec.toNat_sub_of_le (by change (1 : Nat) ≤ count.toNat; omega)]
  change count.toNat - 1 + 1 = count.toNat
  omega

theorem backedge_private (worker : Worker) (valid : PrivateValid worker) (phase : worker.phase = .backedge) :
    PrivateValid { worker with phase := nextPhase worker.phase (loopContext worker.context), context := loopContext worker.context } := by
  simp only [PrivateValid, phase] at valid
  obtain ⟨rdi, bound, rsp, pc, count⟩ := valid
  have progress := decrement_count (worker.context.registers .rcx) count
  have nextBound : (worker.context.registers .rcx - 1).toNat ≤ (worker.entry.registers .rcx).toNat := by omega
  simp at nextBound
  by_cases zero : worker.context.registers .rcx - 1 = 0
  all_goals
    simp only [BitVec.ofNat_eq_ofNat] at zero
    simp [PrivateValid, nextPhase, phase, loopContext, rdi, rsp, pc, zero, nextBound, BitVec.add_assoc]

end EDSL.OS.CounterThreads
