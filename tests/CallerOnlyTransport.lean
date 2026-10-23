/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.CallerOnly
import EDSL.X86.Sequential.Rotate
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Literal instruction bytes exercise production decoding and steps. The two
operand memories differ at unrelated RAM, while registers and flags remain
arbitrary. Rotation uses the independent bit-origin specification; RET checks
the architectural context frame, actual caller dependence and exact faults.
These model-level regression contracts make no corpus or hardware claims.
-/

namespace EDSL.Tests.CallerOnlyTransport
open X86 X86.Sequential

deriving instance DecidableEq for Except

private def memory (code stack : List Byte) (ambient : Byte) : Memory where
  read address :=
    if 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + code.length then
      code[address.toNat - 0x1000]?
    else if 0x2000 ≤ address.toNat ∧ address.toNat < 0x2000 + stack.length then
      stack[address.toNat - 0x2000]?
    else if address = 0x4000 then some ambient
    else none
  executable address := decide (0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + code.length)
  writable address := address.getLsbD 4

private def entry (code stack : List Byte) (ambient : Byte)
    (registers : Register → Word) (flags : Word) : State :=
  ⟨registers, 0x1000, flags, memory code stack ambient⟩

private def caller : List Byte := [0, 0x30, 0, 0, 0, 0, 0, 0]

/-- Decode the literal RET using its authenticated opcode. Registers, flags and
all bytes beyond that opcode remain outside the decoder premise. -/
private theorem ret_decoded {state : State}
    (opcode : fetchByte state.memory state.rip = .ok 0xc3) :
    Sequential.decodeAt state = .ok (.legacy .ret) := by
  apply decodeAt_legacy
  rw [X86.decodeAt, opcode, ok_bind, ite_eq_left rfl]
  rfl

/-- Actual RET preserves every arbitrary GPR except RSP and every flag.
The second step changes the observed RAM while retaining the complete returned
context and exact STACK8 trace. This catches retaining the old output memory. -/
theorem ret_unrelated_ram (registers : Register → Word) (flags : Word) (af : Bool)
    (rsp : registers .rsp = 0x2000) :
    ∃ output,
      Sequential.step af (entry [0xc3] caller 0x11 registers flags) =
        .ok ⟨.returned output, [⟨.stack, registers .rsp, 8⟩]⟩ ∧
      Sequential.step af (entry [0xc3] caller 0x22 registers flags) =
        .ok ⟨.returned { output with memory := memory [0xc3] caller 0x22 },
          [⟨.stack, registers .rsp, 8⟩]⟩ ∧
      output.rip = 0x3000 ∧ output.registers .rsp = 0x2008 ∧ output.flags = flags ∧
      (∀ register, register ≠ .rsp → output.registers register = registers register) ∧
      output.memory.read 0x4000 ≠ (memory [0xc3] caller 0x22).read 0x4000 := by
  let initial := entry [0xc3] caller 0x11 registers flags
  let output := { initial.writeRegister .rsp (initial.registers .rsp + 8) with rip := 0x3000 }
  have decodedLeft : Sequential.decodeAt initial = .ok (.legacy .ret) := by
    apply ret_decoded
    change fetchByte (memory [0xc3] caller 0x11) 0x1000 = .ok 0xc3
    decide +kernel
  have decodedRight : Sequential.decodeAt (entry [0xc3] caller 0x22 registers flags) =
      .ok (.legacy .ret) := by
    apply ret_decoded
    change fetchByte (memory [0xc3] caller 0x22) 0x1000 = .ok 0xc3
    decide +kernel
  have read : readWord initial.memory (initial.registers .rsp) = .ok 0x3000 := by
    change readWord (memory [0xc3] caller 0x11) (registers .rsp) = .ok 0x3000
    rw [rsp]
    decide +kernel
  have legacy := X86.execute_ret_exact initial 0x3000 read (by decide)
  have actual : Sequential.execute initial (.legacy .ret) af =
      .ok ⟨.returned output, [⟨.stack, registers .rsp, 8⟩]⟩ := by
    rw [execute_legacy, legacy] <;> rfl
  have agree : readWord (memory [0xc3] caller 0x22) (initial.registers .rsp) =
      readWord initial.memory (initial.registers .rsp) := by
    change readWord (memory [0xc3] caller 0x22) (registers .rsp) =
      readWord (memory [0xc3] caller 0x11) (registers .rsp)
    rw [rsp]
    decide +kernel
  have only : CallerOnly (.legacy .ret) := Or.inr rfl
  have transported := only.execute_memory_eq initial (memory [0xc3] caller 0x22) af
    (fun _ => agree)
  rw [actual] at transported
  refine ⟨output, (step_eq_execute af decodedLeft).trans actual, ?_, rfl, ?_, rfl, ?_, ?_⟩
  · rw [step_eq_execute af decodedRight]
    exact transported
  · change registers .rsp + 8 = 0x2008
    rw [rsp]
    decide +kernel
  · intro register different
    simp [output, State.writeRegister, different, initial, entry]
  · change (some (0x11 : Byte) : Option Byte) ≠ some 0x22
    decide

/-- The original caller word is readable, but a shifted current RSP makes its
last actual byte inaccessible. The same exact fault survives unrelated RAM
changes using equality of read errors, without assuming a successful return. -/
theorem current_rsp_fault_transports (registers : Register → Word) (flags : Word) (af : Bool)
    (rsp : registers .rsp = 0x2001) :
    Sequential.step af (entry [0xc3] caller 0x11 registers flags) =
      .error (.inaccessibleStack 0x2008) ∧
    Sequential.step af (entry [0xc3] caller 0x22 registers flags) =
      .error (.inaccessibleStack 0x2008) := by
  let initial := entry [0xc3] caller 0x11 registers flags
  have decodedLeft : Sequential.decodeAt initial = .ok (.legacy .ret) := by
    apply ret_decoded
    change fetchByte (memory [0xc3] caller 0x11) 0x1000 = .ok 0xc3
    decide +kernel
  have decodedRight : Sequential.decodeAt (entry [0xc3] caller 0x22 registers flags) =
      .ok (.legacy .ret) := by
    apply ret_decoded
    change fetchByte (memory [0xc3] caller 0x22) 0x1000 = .ok 0xc3
    decide +kernel
  have failedRead : readWord (memory [0xc3] caller 0x11) (registers .rsp) =
      .error (.inaccessibleStack 0x2008) := by
    rw [rsp]
    decide +kernel
  have actual : Sequential.execute initial (.legacy .ret) af =
      .error (.inaccessibleStack 0x2008) := by
    simp only [execute, X86.executeInstruction, executeRet, initial, entry, failedRead, error_bind]
  have agree : readWord (memory [0xc3] caller 0x22) (initial.registers .rsp) =
      readWord initial.memory (initial.registers .rsp) := by
    change readWord (memory [0xc3] caller 0x22) (registers .rsp) =
      readWord (memory [0xc3] caller 0x11) (registers .rsp)
    rw [rsp]
    decide +kernel
  have only : CallerOnly (.legacy .ret) := Or.inr rfl
  have transported := only.execute_memory_eq initial (memory [0xc3] caller 0x22) af
    (fun _ => agree)
  rw [actual] at transported
  exact ⟨(step_eq_execute af decodedLeft).trans actual,
    (step_eq_execute af decodedRight).trans transported⟩

/-- Changing the caller word itself can turn the same decoded RET into a
canonicality rejection. Unrelated RAM independence does not erase this read. -/
theorem changed_caller_can_reject (registers : Register → Word) (flags : Word) (af : Bool)
    (rsp : registers .rsp = 0x2000) :
    ∃ output,
      Sequential.step af (entry [0xc3] caller 0x11 registers flags) =
        .ok ⟨.returned output, [⟨.stack, registers .rsp, 8⟩]⟩ ∧
      Sequential.step af (entry [0xc3] [0, 0, 0, 0, 0, 0x80, 0, 0] 0x22 registers flags) =
        .error (.noncanonicalReturn 0x800000000000) := by
  obtain ⟨output, returned, _⟩ := ret_unrelated_ram registers flags af rsp
  refine ⟨output, returned, ?_⟩
  let stack : List Byte := [0, 0, 0, 0, 0, 0x80, 0, 0]
  have decoded : Sequential.decodeAt (entry [0xc3] stack 0x22 registers flags) =
      .ok (.legacy .ret) := by
    apply ret_decoded
    change fetchByte (memory [0xc3] stack 0x22) 0x1000 = .ok 0xc3
    decide +kernel
  have read : readWord (memory [0xc3] stack 0x22) (registers .rsp) =
      .ok 0x800000000000 := by
    rw [rsp]
    decide +kernel
  rw [step_eq_execute af decoded]
  simp only [execute, X86.executeInstruction, executeRet, entry, read, ok_bind] <;> rfl

/-- Full production Bool and uniform-vector steps retain arbitrary context
across distinct unrelated RAM. The bit-origin relation is independent of the
executor, and undefined OF is the selected Bool for every masked count > 1. -/
theorem rotate_unrelated_ram (registers : Register → Word) (flags : Word) (af : Bool) :
    ∃ output,
      Sequential.step af (entry [0x48, 0xd3, 0xc0] [] 0x11 registers flags) =
        .ok ⟨.next output, []⟩ ∧
      Sequential.stepWith (FlagChoices.uniform af)
          (entry [0x48, 0xd3, 0xc0] [] 0x22 registers flags) =
        .ok ⟨.next { output with memory := memory [0x48, 0xd3, 0xc0] [] 0x22 }, []⟩ ∧
      WordMath.IsRotateLeft64 (registers .rax) (rolCount64 (registers .rcx))
        (output.registers .rax) ∧
      (∀ register, register ≠ .rax → output.registers register = registers register) ∧
      output.flags &&& ~~~(0x801 : Word) = flags &&& ~~~(0x801 : Word) ∧
      (1 < rolCount64 (registers .rcx) → output.flags.getLsbD 11 = af) ∧
      output.rip = 0x1003 ∧
      output.memory.read 0x4000 ≠ (memory [0x48, 0xd3, 0xc0] [] 0x22).read 0x4000 := by
  let initial := entry [0x48, 0xd3, 0xc0] [] 0x11 registers flags
  have decodedLeft : Sequential.decodeAt initial = .ok (.rolCL64 .rax) :=
    decodeAt_rolCL64 (state := initial) (rex := 0x48) (modrm := 0xc0)
      (Or.inl rfl)
      (by
        change fetchByte (memory [0x48, 0xd3, 0xc0] [] 0x11) 0x1000 = .ok 0x48
        decide +kernel)
      (by
        change fetchByte (memory [0x48, 0xd3, 0xc0] [] 0x11) (0x1000 + 1) = .ok 0xd3
        decide +kernel)
      (by
        change fetchByte (memory [0x48, 0xd3, 0xc0] [] 0x11) (0x1000 + 2) = .ok 0xc0
        decide +kernel)
      (by decide) (by decide)
  have decodedRight : Sequential.decodeAt
      (entry [0x48, 0xd3, 0xc0] [] 0x22 registers flags) = .ok (.rolCL64 .rax) :=
    decodeAt_rolCL64 (state := entry [0x48, 0xd3, 0xc0] [] 0x22 registers flags)
      (rex := 0x48) (modrm := 0xc0)
      (Or.inl rfl)
      (by
        change fetchByte (memory [0x48, 0xd3, 0xc0] [] 0x22) 0x1000 = .ok 0x48
        decide +kernel)
      (by
        change fetchByte (memory [0x48, 0xd3, 0xc0] [] 0x22) (0x1000 + 1) = .ok 0xd3
        decide +kernel)
      (by
        change fetchByte (memory [0x48, 0xd3, 0xc0] [] 0x22) (0x1000 + 2) = .ok 0xc0
        decide +kernel)
      (by decide) (by decide)
  obtain ⟨output, actual, rotation, registersFrame, memoryFrame, chosen, flagsFrame, pc⟩ :=
    execute_rolCL64_context initial .rax af
  have only : CallerOnly (.rolCL64 .rax) := trivial
  have vector : executeWith initial (.rolCL64 .rax) (FlagChoices.uniform af) =
      .ok ⟨.next output, []⟩ := by
    rw [executeWith_uniform initial (.rolCL64 .rax) af only.boolChoiceProfile]
    exact actual
  have transported := only.executeWith_uniform_memory_eq initial
    (memory [0x48, 0xd3, 0xc0] [] 0x22) af (by intro impossible; cases impossible)
  rw [vector] at transported
  refine ⟨output, (step_eq_execute af decodedLeft).trans actual, ?_, rotation,
    registersFrame, flagsFrame, ?_, pc, ?_⟩
  · rw [stepWith_eq_executeWith _ decodedRight]
    exact transported
  · intro moreThanOne
    change output.flags = rolFlags64 flags (output.registers .rax)
      (rolCount64 (registers .rcx)) af at chosen
    rw [chosen]
    have nonzero : rolCount64 (registers .rcx) ≠ 0 := by omega
    have notOne : rolCount64 (registers .rcx) ≠ 1 := by omega
    simpa only [ite_eq_right notOne] using
      (rolFlags64_bits flags (output.registers .rax) (rolCount64 (registers .rcx)) af nonzero).2
  · rw [memoryFrame]
    change (some (0x11 : Byte) : Option Byte) ≠ some 0x22
    decide

/-- Taken control flow still rejects the actual noncanonical target in either
memory; transporting a failure cannot manufacture an ordinary continuation. -/
theorem branch_fault_transports (input : State) (replacement : Memory) (af : Bool) :
    Sequential.execute { input with rip := 0x7ffffffffffe } (.jmp 0) af =
      .error (.noncanonicalBranch 0x800000000000) ∧
    Sequential.execute { input with rip := 0x7ffffffffffe, memory := replacement } (.jmp 0) af =
      .error (.noncanonicalBranch 0x800000000000) := by
  have actual : Sequential.execute { input with rip := 0x7ffffffffffe } (.jmp 0) af =
      .error (.noncanonicalBranch 0x800000000000) := by rfl
  have only : CallerOnly (.jmp 0) := trivial
  have transported := only.execute_memory_eq { input with rip := 0x7ffffffffffe }
    replacement af (by intro impossible; cases impossible)
  rw [actual] at transported
  exact ⟨actual, transported⟩

end EDSL.Tests.CallerOnlyTransport

#print axioms EDSL.X86.Sequential.CallerOnly.execute_memory_eq
#print axioms EDSL.X86.Sequential.CallerOnly.executeWith_uniform_memory_eq
#print axioms EDSL.Tests.CallerOnlyTransport.ret_unrelated_ram
#print axioms EDSL.Tests.CallerOnlyTransport.current_rsp_fault_transports
#print axioms EDSL.Tests.CallerOnlyTransport.changed_caller_can_reject
#print axioms EDSL.Tests.CallerOnlyTransport.rotate_unrelated_ram
#print axioms EDSL.Tests.CallerOnlyTransport.branch_fault_transports
#audit_edsl
