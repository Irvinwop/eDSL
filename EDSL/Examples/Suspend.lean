/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Suspend.Invariant

namespace EDSL.Examples.Suspend
open X86 OS

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- Owned raw request/RET bytes. No Linux service contract is assumed. -/
def callerBytes : List Byte := [0x0f, 0x05, 0xc3]

/-- The peer changes shared RAM with an actual implicitly locked XCHG. -/
def exchangeBytes : List Byte := [0x87, 0x07, 0xc3]

/-- Finite executable code, separate read-only return words, and one aligned
writable data word with guards. Neither stack aliases code or writable data. -/
def memory (caller peer : List Byte) : X86.Memory where
  read address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4096 + caller.length then
      caller[address.toNat - 4096]?
    else if 8192 ≤ address.toNat ∧ address.toNat < 8192 + peer.length then
      peer[address.toNat - 8192]?
    else if address.toNat = 32769 then some 0x30
    else if address.toNat = 32801 then some 0x40
    else if address.toNat = 65535 then some 0x5a
    else if address.toNat = 65536 then some 0xfe
    else if address.toNat = 65537 then some 0xdc
    else if address.toNat = 65538 then some 0xba
    else if address.toNat = 65539 then some 0x98
    else if address.toNat = 65540 then some 0xa5
    else if (32768 ≤ address.toNat ∧ address.toNat < 32776) ∨
        (32800 ≤ address.toNat ∧ address.toNat < 32808) then some 0 else none
  executable address := decide
    ((4096 ≤ address.toNat ∧ address.toNat < 4096 + caller.length) ∨
      (8192 ≤ address.toNat ∧ address.toNat < 8192 + peer.length))
  writable address := decide (65536 ≤ address.toNat ∧ address.toNat < 65540)

/-- Distinct high halves expose argument selection and accidental truncation.
The private sentinels also expose collateral register/flag changes. -/
def callerContext : Threads.Context where
  registers
    | .rax => 0xdeadbeef76543210
    | .rcx => 0x1111222233334444
    | .rdx => 0x23456789abcdef01
    | .rbx => 0x6789abcdef0123456
    | .rsp => 32768
    | .rbp => 0x789abcdef01234567
    | .rsi => 0x0123456789abcdef
    | .rdi => 65536
    | .r8 => 0x456789abcdef01234
    | .r9 => 0x56789abcdef012345
    | .r10 => 0x3456789abcdef0123
    | .r11 => 0x5555666677778888
    | .r12 => 0x89abcdef01234567
    | .r13 => 0x9abcdef012345678
    | .r14 => 0xabcdef0123456789
    | .r15 => 0xbcdef0123456789a
  rip := 4096
  flags := 0x8d7

def peerContext (replacement : BitVec 32) : Threads.Context where
  registers register := if register = .rax then replacement.setWidth 64
    else if register = .rdi then 65536
    else if register = .rsp then 32800
    else 0xcafef00d13579bdf
  rip := 8192
  flags := 0x246

def initial (replacement : BitVec 32) : OS.Suspend.State :=
  OS.Suspend.initial ⟨memory callerBytes exchangeBytes,
    [⟨callerContext, false, []⟩, ⟨peerContext replacement, false, []⟩]⟩

/-- Extract only an actually successful computation. The proof checks the
constructor without comparing complete function-valued machine states. -/
def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

def entryRequest : SyscallRequest :=
  ⟨MachineThreads.contextState callerContext (memory callerBytes exchangeBytes), 4098⟩

def entered (replacement : BitVec 32) : OS.Suspend.State × OS.Suspend.Observation :=
  (OS.Suspend.capture (initial replacement) 0 entryRequest, .entered 0 0)

theorem entered_ok (replacement : BitVec 32) :
    OS.Suspend.issue (initial replacement) 0 = .ok (entered replacement) :=
  OS.Suspend.IssueEffect.success
    (.entered (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl))

private def exchangeInput (replacement : BitVec 32) : X86.State :=
  MachineThreads.contextState (peerContext replacement) (memory callerBytes exchangeBytes)

private def exchangeOutput (replacement : BitVec 32) : X86.State :=
  { (exchangeInput replacement).writeRegister .rax 0x98badcfe with
    memory := writeDWordUnchecked (memory callerBytes exchangeBytes) 65536 replacement
    rip := 8194 }

private theorem exchange_instruction (replacement : BitVec 32) :
    executeInstruction (exchangeInput replacement) .exchangeEaxRdi =
      .ok (.atomic ⟨65536, 0x98badcfe, replacement⟩ (exchangeOutput replacement)) := by
  have width : (replacement.setWidth 64).setWidth 32 = replacement := by simp
  have word : exchangeDWord (exchangeInput replacement).memory
      ((exchangeInput replacement).registers .rdi)
      (((exchangeInput replacement).registers .rax).setWidth 32) =
        .ok (writeDWordUnchecked (memory callerBytes exchangeBytes) 65536 replacement,
          0x98badcfe) := by
    change exchangeDWord (memory callerBytes exchangeBytes) 65536
      ((replacement.setWidth 64).setWidth 32) = _
    rw [width]
    exact exchangeDWord_success _ _ _ _ (by rfl) (by rfl) (by rfl)
  have actual : executeExchange (exchangeInput replacement) =
      .ok (⟨65536, 0x98badcfe, replacement⟩, exchangeOutput replacement) := by
    rw [executeExchange, word]
    simp only [ok_bind, pure_ok]
    simp [exchangeOutput, exchangeInput, MachineThreads.contextState, peerContext, width]
  simp only [executeInstruction, actual, ok_bind, pure_ok]

def exchanged (replacement : BitVec 32) : OS.Suspend.State × OS.Suspend.Observation :=
  ({ (entered replacement).1 with
      machine := TSO.install (entered replacement).1.machine 1
        (exchangeOutput replacement).memory (.ofState (exchangeOutput replacement)) false [] },
    .machine (.retired 1 (some ⟨65536, 0x98badcfe, replacement⟩)))

theorem exchanged_ok (replacement : BitVec 32) :
    OS.Suspend.issue (entered replacement).1 1 = .ok (exchanged replacement) := by
  apply OS.Suspend.IssueEffect.success
  apply OS.Suspend.IssueEffect.machine (by rfl)
  have live : (entered replacement).1.machine.workers[1]? =
      some ⟨peerContext replacement, false, []⟩ := rfl
  have decoded : decodeAt (TSO.sharedState (entered replacement).1.machine
      ⟨peerContext replacement, false, []⟩) = .ok .exchangeEaxRdi := by
    have first : fetchByte (memory callerBytes exchangeBytes) 8192 = .ok 0x87 := rfl
    have second : fetchByte (memory callerBytes exchangeBytes) 8193 = .ok 0x07 := rfl
    simp only [BitVec.ofNat_eq_ofNat] at first second
    change decodeAt (exchangeInput replacement) = _
    simp [decodeAt, exchangeInput, MachineThreads.contextState, peerContext, first, second]
  have data : TSO.dataOnly (entered replacement).1.machine.memory
      ((peerContext replacement).registers .rdi) = true := by rfl
  have executed : executeInstruction (TSO.sharedState (entered replacement).1.machine
      ⟨peerContext replacement, false, []⟩) .exchangeEaxRdi =
        .ok (.atomic ⟨65536, 0x98badcfe, replacement⟩ (exchangeOutput replacement)) :=
    exchange_instruction replacement
  simp [TSO.issue, live, decoded, TSO.execute, TSO.pendingStore, TSO.locked, data, executed,
    Except.mapError]

def resumed (replacement : BitVec 32) (raw flags rcx r11 : Word) : OS.Suspend.State :=
  { (exchanged replacement).1 with
    machine := TSO.install (exchanged replacement).1.machine 0
      (exchanged replacement).1.machine.memory
      (.ofState (X86.resumeAt entryRequest (exchanged replacement).1.machine.memory
        raw flags rcx r11)) false []
    pending := fun query => if query = 0 then none else (exchanged replacement).1.pending query }

theorem resumed_ok (replacement : BitVec 32) (raw flags rcx r11 : Word) :
    OS.Suspend.resume (exchanged replacement).1 0 0 raw flags rcx r11 =
      .ok (resumed replacement raw flags rcx r11) :=
  OS.Suspend.resume_success (state := (exchanged replacement).1) (identifier := 0)
    (invocation := 0) (worker := ⟨callerContext, false, []⟩) (saved := ⟨0, 0, entryRequest⟩)
    raw flags rcx r11
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)

def returned (replacement : BitVec 32) (raw flags rcx r11 : Word) :
    OS.Suspend.State × OS.Suspend.Observation :=
  checked (OS.Suspend.issue (resumed replacement raw flags rcx r11) 0) (by rfl)

theorem returned_ok (replacement : BitVec 32) (raw flags rcx r11 : Word) :
    OS.Suspend.issue (resumed replacement raw flags rcx r11) 0 =
      .ok (returned replacement raw flags rcx r11) := checked_ok _ _

/-- The actual peer instruction publishes any replacement word. This uses
the independently proved little-endian write/read law, rather than expanding
the evaluator into a second expected-state computation. -/
theorem exchanged_value (replacement : BitVec 32) :
    loadDWord (exchanged replacement).1.machine.memory 65536 = .ok replacement := by
  change loadDWord (writeDWordUnchecked (memory callerBytes exchangeBytes) 65536
    replacement) 65536 = .ok replacement
  exact load_after_write _ _ _ (by rfl)

/-- Both instructions run through actual shared-byte fetch and execution. -/
theorem peerPrefix_ok (replacement : BitVec 32) :
    OS.Suspend.schedule (initial replacement) [.issue 0, .issue 1] =
      .ok ((exchanged replacement).1,
        [.entered 0 0, .machine (.retired 1 (some ⟨65536, 0x98badcfe, replacement⟩))]) := by
  simp only [OS.Suspend.schedule, OS.Suspend.step, entered_ok, exchanged_ok, ok_bind, pure_ok]
  rfl

def completionActions (raw flags rcx r11 : Word) : List OS.Suspend.Action :=
  [.issue 0, .issue 1, .resume 0 0 raw flags rcx r11, .issue 0]

/-- A checked byte-level execution exists for every peer replacement and every
full-width completion choice. There is no eventual-success premise. -/
theorem completion_ok (replacement : BitVec 32) (raw flags rcx r11 : Word) :
    OS.Suspend.schedule (initial replacement) (completionActions raw flags rcx r11) =
      .ok ((returned replacement raw flags rcx r11).1,
        [.entered 0 0, .machine (.retired 1 (some ⟨65536, 0x98badcfe, replacement⟩)),
          .resumed 0 0 raw, .machine (.retired 0 none)]) := by
  simp only [completionActions, OS.Suspend.schedule, OS.Suspend.step,
    entered_ok, exchanged_ok, resumed_ok, returned_ok, ok_bind, pure_ok]
  rfl

/-- Full current RAM and the peer's complete Worker are framed by the generic
resume theorems, including functions, permissions, context and FIFO. -/
theorem resumed_frame (replacement : BitVec 32) (raw flags rcx r11 : Word) :
    (resumed replacement raw flags rcx r11).machine.memory =
      (exchanged replacement).1.machine.memory ∧
    (resumed replacement raw flags rcx r11).machine.workers[1]? =
      (exchanged replacement).1.machine.workers[1]? :=
  ⟨OS.Suspend.resume_memory (resumed_ok replacement raw flags rcx r11),
    OS.Suspend.resume_peer (by decide) (resumed_ok replacement raw flags rcx r11)⟩

theorem resumed_value (replacement : BitVec 32) (raw flags rcx r11 : Word) :
    loadDWord (resumed replacement raw flags rcx r11).machine.memory 65536 =
      .ok replacement := by
  rw [(resumed_frame replacement raw flags rcx r11).1]
  exact exchanged_value replacement

/-- Apply the generic full-context contract to the actual installed caller. -/
theorem resumed_contract (replacement : BitVec 32) (raw flags rcx r11 : Word) :
    ∃ worker,
      (resumed replacement raw flags rcx r11).machine.workers[0]? = some worker ∧
      worker.returned = false ∧ worker.buffer = [] ∧
      TSO.sharedState (resumed replacement raw flags rcx r11).machine worker =
        X86.resumeAt entryRequest (exchanged replacement).1.machine.memory raw flags rcx r11 ∧
      ReturnsAt entryRequest (exchanged replacement).1.machine.memory raw
        (TSO.sharedState (resumed replacement raw flags rcx r11).machine worker) := by
  obtain ⟨saved, worker, pending, live, unreturned, empty, context, contract⟩ :=
    OS.Suspend.resume_returnsAt (resumed_ok replacement raw flags rcx r11)
  have same : saved = ⟨0, 0, entryRequest⟩ := Option.some.inj (pending.symm.trans (by rfl))
  subst saved
  exact ⟨worker, live, unreturned, empty, context, contract⟩

/-- Resumption is enabled for every completion choice after the actual peer
XCHG. Its current-memory result differs from the historical request snapshot
whenever the replacement differs from the initial word. -/
theorem every_raw_return (replacement : BitVec 32) (raw flags rcx r11 : Word) :
    ∃ after worker,
      OS.Suspend.resume (exchanged replacement).1 0 0 raw flags rcx r11 = .ok after ∧
      after.machine.memory = (exchanged replacement).1.machine.memory ∧
      loadDWord after.machine.memory 65536 = .ok replacement ∧
      after.machine.workers[1]? = (exchanged replacement).1.machine.workers[1]? ∧
      after.machine.workers[0]? = some worker ∧
      TSO.sharedState after.machine worker =
        X86.resumeAt entryRequest (exchanged replacement).1.machine.memory raw flags rcx r11 ∧
      ReturnsAt entryRequest (exchanged replacement).1.machine.memory raw
        (TSO.sharedState after.machine worker) := by
  obtain ⟨worker, live, _, _, context, contract⟩ := resumed_contract replacement raw flags rcx r11
  exact ⟨resumed replacement raw flags rcx r11, worker,
    resumed_ok replacement raw flags rcx r11, (resumed_frame replacement raw flags rcx r11).1,
    resumed_value replacement raw flags rcx r11, (resumed_frame replacement raw flags rcx r11).2,
    live, context, contract⟩

theorem returned_peer (replacement : BitVec 32) (raw flags rcx r11 : Word) :
    (returned replacement raw flags rcx r11).1.machine.workers[1]? =
      (exchanged replacement).1.machine.workers[1]? :=
  (OS.Suspend.issue_peer (by decide) (returned_ok replacement raw flags rcx r11)).trans
    (resumed_frame replacement raw flags rcx r11).2

theorem initial_valid (replacement : BitVec 32) : OS.Suspend.WellFormed (initial replacement) := by
  apply OS.Suspend.WellFormed.initial
  intro worker member store queued
  change worker ∈ [⟨callerContext, false, []⟩, ⟨peerContext replacement, false, []⟩] at member
  simp at member
  rcases member with rfl | rfl <;> cases queued

theorem exchanged_valid (replacement : BitVec 32) :
    OS.Suspend.WellFormed (exchanged replacement).1 :=
  ((initial_valid replacement).issue (entered_ok replacement)).issue (exchanged_ok replacement)

theorem resumed_valid (replacement : BitVec 32) (raw flags rcx r11 : Word) :
    OS.Suspend.WellFormed (resumed replacement raw flags rcx r11) :=
  (exchanged_valid replacement).resume (resumed_ok replacement raw flags rcx r11)

theorem returned_valid (replacement : BitVec 32) (raw flags rcx r11 : Word) :
    OS.Suspend.WellFormed (returned replacement raw flags rcx r11).1 :=
  (resumed_valid replacement raw flags rcx r11).issue (returned_ok replacement raw flags rcx r11)

end EDSL.Examples.Suspend

#audit_edsl
