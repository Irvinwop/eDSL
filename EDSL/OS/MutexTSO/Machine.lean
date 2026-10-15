/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.MemoryTransport
import EDSL.OS.MachineThreads
import EDSL.OS.MutexReplay.Machine

namespace EDSL.OS.MutexTSO
open X86

/-- Every ordinary instruction in the fixed mutex replay reads only context. -/
theorem plain_contextOnly (instruction : MutexReplay.Plain) :
    ContextOnly instruction.instruction := by
  cases instruction <;> trivial

/-- Exact load using the actual replay context constructor, on arbitrary memory. -/
theorem execute_load_exact (context : Threads.Context) (memory : Memory)
    (value : BitVec 32)
    (read : loadDWord memory (context.registers .rsi) = .ok value) :
    executeInstruction (MachineThreads.contextState context memory) .loadEaxRsi =
      .ok (.next (MachineThreads.contextState
        (MutexReplay.exchangedContext context value) memory)) :=
  X86.execute_load_exact (MachineThreads.contextState context memory) value read

/-- Exact issued store, with the full context and complete immediate memory. -/
theorem execute_store_exact (context : Threads.Context) (memory : Memory)
    (allowed : canStoreDWord memory (context.registers .rsi) = true) :
    executeInstruction (MachineThreads.contextState context memory) .storeEaxRsi =
      .ok (.next (MachineThreads.contextState (MutexReplay.storedContext context)
        (writeDWordUnchecked memory (context.registers .rsi)
          ((context.registers .rax).setWidth 32)))) :=
  X86.execute_store_exact (MachineThreads.contextState context memory) allowed

/-- Exact saved return, with no buffer or publication operation. -/
theorem execute_ret_exact (context : Threads.Context) (memory : Memory) (target : Word)
    (read : readWord memory (context.registers .rsp) = .ok target)
    (valid : canonical target = true) :
    executeInstruction (MachineThreads.contextState context memory) .ret =
      .ok (.returned (MachineThreads.contextState
        (MutexReplay.returnedContext context target) memory)) :=
  X86.execute_ret_exact (MachineThreads.contextState context memory) target read valid

/-- Exact exchange with the actual event and the replay's entire private context. -/
theorem execute_exchange_exact (context : Threads.Context) (memory output : Memory)
    (old : BitVec 32)
    (ran : exchangeDWord memory (context.registers .rdi)
      ((context.registers .rax).setWidth 32) = .ok (output, old)) :
    executeInstruction (MachineThreads.contextState context memory) .exchangeEaxRdi =
      .ok (.atomic
        ⟨context.registers .rdi, old, (context.registers .rax).setWidth 32⟩
        (MachineThreads.contextState (MutexReplay.exchangedContext context old) output)) :=
  X86.execute_exchange_exact (MachineThreads.contextState context memory) output old ran

end EDSL.OS.MutexTSO
