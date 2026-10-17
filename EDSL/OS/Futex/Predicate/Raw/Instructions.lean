import EDSL.OS.Futex.Predicate.Decode

namespace EDSL.OS.Futex.Predicate
open X86

def movContext (context : Threads.Context) (destination : Register) (value : BitVec 32) :
    Threads.Context :=
  { context with
    registers := fun register => if register = destination then value.setWidth 64
      else context.registers register
    rip := context.rip + 5 }

def cmpContext (context : Threads.Context) : Threads.Context :=
  { context with rip := context.rip + 3
                 flags := cmpZeroFlags32 context.flags ((context.registers .rax).setWidth 32) }

def branchContext (context : Threads.Context) (target : Word) : Threads.Context :=
  { context with rip := target }

def resumeContext (request : SyscallRequest) (raw flags rcx r11 : Word) : Threads.Context :=
  { registers := fun register =>
      if register = .rax then raw
      else if register = .rcx then rcx
      else if register = .r11 then r11
      else request.user.registers register
    rip := request.continuation
    flags := flags }

theorem execute_load (context : Threads.Context) (memory : Memory) (value : BitVec 32)
    (readable : loadDWord memory (context.registers .rdi) = .ok value) :
    executeInstruction (MachineThreads.contextState context memory) .loadEaxRdi =
      .ok (.next (MachineThreads.contextState (context.loaded value) memory)) := by
  simp [executeInstruction, executeLoad, MachineThreads.contextState, readable,
    Threads.Context.loaded, State.writeRegister]

theorem execute_cmp (context : Threads.Context) (memory : Memory) :
    executeInstruction (MachineThreads.contextState context memory) .cmpEaxZero =
      .ok (.next (MachineThreads.contextState (cmpContext context) memory)) := rfl

theorem execute_mov (context : Threads.Context) (memory : Memory)
    (destination : Register) (value : BitVec 32) :
    executeInstruction (MachineThreads.contextState context memory) (.mov32 destination value) =
      .ok (.next (MachineThreads.contextState (movContext context destination value) memory)) := rfl

theorem execute_jnz_fallthrough (context : Threads.Context) (memory : Memory) (displacement : Byte)
    (zero : context.flags.getLsbD 6 = true) :
    executeInstruction (MachineThreads.contextState context memory) (.jnz displacement) =
      .ok (.next (MachineThreads.contextState (branchContext context (context.rip + 2)) memory)) := by
  simp only [executeInstruction, executeJnz, MachineThreads.contextState, zero]
  simp [executeShortBranch, branchContext]

theorem execute_jnz_taken (context : Threads.Context) (memory : Memory) (displacement : Byte)
    (zero : context.flags.getLsbD 6 = false)
    (canonical : X86.canonical (context.rip + 2 + displacement.signExtend 64) = true) :
    executeInstruction (MachineThreads.contextState context memory) (.jnz displacement) =
      .ok (.next (MachineThreads.contextState
        (branchContext context (context.rip + 2 + displacement.signExtend 64)) memory)) := by
  have checked : executeShortBranch (MachineThreads.contextState context memory) true displacement =
      .ok (MachineThreads.contextState
        (branchContext context (context.rip + 2 + displacement.signExtend 64)) memory) := by
    simp only [executeShortBranch, ↓reduceIte]
    exact ite_eq_left canonical
  change (do
    let output ← executeShortBranch (MachineThreads.contextState context memory)
      (!context.flags.getLsbD 6) displacement
    pure (StepResult.next output)) = _
  simp only [zero, Bool.not_false, checked, ok_bind]
  rfl

theorem execute_syscall (context : Threads.Context) (memory : Memory) :
    executeInstruction (MachineThreads.contextState context memory) .syscall =
      .ok (.syscall ⟨MachineThreads.contextState context memory, context.rip + 2⟩) := rfl

theorem execute_ret (client : Client) (context : Threads.Context) (memory : Memory)
    (stack : readWord memory (context.registers .rsp) = .ok client.returnTarget)
    (canonical : X86.canonical client.returnTarget = true) :
    executeInstruction (MachineThreads.contextState context memory) .ret =
      .ok (.returned (MachineThreads.contextState (client.returned context) memory)) := by
  simp [executeInstruction, executeRet, MachineThreads.contextState, stack, canonical,
    Client.returned, State.writeRegister]

theorem Stable.loaded {client : Client} {context : Threads.Context}
    (stable : Stable client context) (value : BitVec 32) : Stable client (context.loaded value) := by
  constructor
  · intro register rax rsi rcx r11
    simp only [Threads.Context.loaded, ite_eq_right rax]
    exact stable.register register rax rsi rcx r11
  · simpa [Threads.Context.loaded] using stable.2

theorem Stable.mov_rax {client : Client} {context : Threads.Context}
    (stable : Stable client context) (value : BitVec 32) : Stable client (movContext context .rax value) :=
  stable.loaded value

theorem Stable.mov_rsi {client : Client} {context : Threads.Context}
    (stable : Stable client context) : Stable client (movContext context .rsi 128) := by
  constructor
  · intro register rax rsi rcx r11
    simp only [movContext, ite_eq_right rsi]
    exact stable.register register rax rsi rcx r11
  · exact Or.inr (by simp [movContext])

theorem Running.load_next {client : Client} {context : Threads.Context}
    (current : Running client .load context) (value : BitVec 32) :
    Running client (.compare value) (context.loaded value) := by
  refine ⟨current.stable.loaded value, ?_, ?_⟩
  · simp [Threads.Context.loaded, current.rip, Point.offset]
  · simp [Point.Fields, Threads.Context.loaded]

theorem Running.compare_next {client : Client} {context : Threads.Context} {observed : BitVec 32}
    (current : Running client (.compare observed) context) :
    Running client (.branch observed) (cmpContext context) := by
  refine ⟨current.stable, ?_, current.fields, ?_⟩
  · simp [cmpContext, current.rip, Point.offset, BitVec.add_assoc]
  · have operand : (context.registers .rax).setWidth 32 = observed := by
      rw [current.fields]
      simp
    simpa only [cmpContext, operand] using
      (cmpZeroFlags32_bits context.flags observed).2.2.2.1

theorem Running.branch_zero {client : Client} {context : Threads.Context}
    (current : Running client (.branch 0) context) :
    Running client .number (branchContext context (context.rip + 2)) := by
  refine ⟨current.stable, ?_, ?_⟩
  · simp [branchContext, current.rip, Point.offset, BitVec.add_assoc]
  · simpa [Point.Fields, branchContext] using current.fields.1

theorem Running.branch_nonzero {client : Client} {context : Threads.Context} {observed : BitVec 32}
    (current : Running client (.branch observed) context) (nonzero : observed ≠ 0) :
    Running client (.done observed) (branchContext context (client.entry.rip + 29)) := by
  refine ⟨current.stable, rfl, current.fields.1, nonzero, ?_⟩
  have zero : context.flags.getLsbD 6 = (observed == 0) := current.fields.2
  rw [beq_eq_false_iff_ne.mpr nonzero] at zero
  exact zero

theorem Running.number_next {client : Client} {context : Threads.Context}
    (current : Running client .number context) :
    Running client .operation (movContext context .rax 202) := by
  refine ⟨current.stable.mov_rax 202, ?_, ?_⟩
  · simp [movContext, current.rip, Point.offset, BitVec.add_assoc]
  · simp [Point.Fields, movContext]

theorem Running.operation_next {client : Client} {context : Threads.Context}
    (current : Running client .operation context) :
    Running client .syscall (movContext context .rsi 128) := by
  refine ⟨current.stable.mov_rsi, ?_, ?_, ?_⟩
  · simp [movContext, current.rip, Point.offset, BitVec.add_assoc]
  · exact current.fields
  · simp [movContext]

theorem Running.resumed_next {client : Client} {context : Threads.Context} {raw : Word}
    (current : Running client (.resumed raw) context) :
    Running client .retryCompare (movContext context .rax 1) := by
  refine ⟨current.stable.mov_rax 1, ?_, ?_, ?_⟩
  · simp [movContext, current.rip, Point.offset, BitVec.add_assoc]
  · simp [movContext]
  · exact current.fields.2

theorem Running.retryCompare_next {client : Client} {context : Threads.Context}
    (current : Running client .retryCompare context) :
    Running client .retryBranch (cmpContext context) := by
  refine ⟨current.stable, ?_, current.fields.1, current.fields.2, ?_⟩
  · simp [cmpContext, current.rip, Point.offset, BitVec.add_assoc]
  · have operand : (context.registers .rax).setWidth 32 = 1 := by rw [current.fields.1]; rfl
    simpa only [cmpContext, operand, show ((1 : BitVec 32) == 0) = false by decide] using
      (cmpZeroFlags32_bits context.flags 1).2.2.2.1

theorem Running.retryBranch_next {client : Client} {context : Threads.Context}
    (current : Running client .retryBranch context) :
    Running client .load (branchContext context client.entry.rip) := by
  exact ⟨current.stable, by simp [branchContext, Point.offset], trivial⟩

theorem branch_done_target {client : Client} {context : Threads.Context} {observed : BitVec 32}
    (current : Running client (.branch observed) context) :
    context.rip + 2 + (0x16 : Byte).signExtend 64 = client.entry.rip + 29 := by
  rw [current.rip]
  simp [Point.offset, BitVec.add_assoc]

theorem branch_retry_target {client : Client} {context : Threads.Context}
    (current : Running client .retryBranch context) :
    context.rip + 2 + (0xe3 : Byte).signExtend 64 = client.entry.rip := by
  rw [current.rip]
  simp [Point.offset, BitVec.add_assoc]

theorem family_resume {client : Client} {request : SyscallRequest}
    (family : client.Family request) (raw flags rcx r11 : Word) :
    Running client (.resumed raw) (resumeContext request raw flags rcx r11) := by
  refine ⟨?_, Family.continuation family, rfl, ?_⟩
  · constructor
    · intro register rax rsi changedRcx changedR11
      simp only [resumeContext, ite_eq_right rax, ite_eq_right changedRcx, ite_eq_right changedR11]
      exact family.1.stable.register register rax rsi changedRcx changedR11
    · exact Or.inr family.1.fields.2
  · exact family.1.fields.2

theorem resume_context_exact (request : SyscallRequest) (memory : Memory)
    (raw flags rcx r11 : Word) :
    X86.resumeAt request memory raw flags rcx r11 =
      MachineThreads.contextState (resumeContext request raw flags rcx r11) memory := rfl

end EDSL.OS.Futex.Predicate
