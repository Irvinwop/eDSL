/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Process.Certificate
import EDSL.Examples.Compiler.WriteExit

namespace EDSL.Process
open X86 OS.AddressSpace
open Examples.Compiler

/-- Finite userspace execution across one completed abstract stream write.
The environment keeps the supplied byte snapshot and stream identity stable.
This relation excludes asynchronous interference and models no kernel code.
Waiting steps belong to the write contract and are excluded from user cost. -/
def ViaWrite (initial : State) (payload : List Byte) (outcome : OS.LinuxWrite.Outcome)
    (final : SyscallRequest) (count : Nat) : Prop :=
  ∃ first firstCount after lastCount,
    Invokes initial first firstCount ∧
    OS.LinuxWrite.supported first payload ∧ first.argument .first = 1 ∧
    BufferAt first.user.memory (first.argument .second) payload ∧
    OS.LinuxWrite.Execution payload .pending (.done outcome) ∧
    Returns first (OS.LinuxWrite.rawResult outcome) after ∧
    Invokes after final lastCount ∧ count = firstCount + lastCount

def checkWriteExit42 (file : List Byte) (image : ELF.Image) : Bool :=
  ELF.checkParsed file image && decide (image.entry = 0x400000) &&
    ELF.checkEntry file image WriteExit.bytes

/-- Output bytes accepted by the modeled stream are a prefix, and the final
raw exit request has status42. Exact output requires a full successful write;
reaching this final request requires write completion. -/
def WriteExitResults (outcome : OS.LinuxWrite.Outcome) (final : SyscallRequest)
    (count : Nat) : Prop :=
  count = 8 ∧ OS.LinuxExit.supported final ∧ OS.LinuxExit.status final = 42 ∧
  OS.LinuxWrite.Permitted WriteExit.payload outcome ∧
  List.IsPrefix (OS.LinuxWrite.emitted WriteExit.payload outcome) WriteExit.payload ∧
  (OS.LinuxWrite.emitted WriteExit.payload outcome).length ≤ 3 ∧
  (outcome = .accepted 3 → OS.LinuxWrite.emitted WriteExit.payload outcome = WriteExit.payload) ∧
  (∀ trace, OS.LinuxExit.Trace final trace →
    (∀ index status, trace index = .exited status → status = 42) ∧
    (OS.LinuxExit.Fair trace → ∃ index, trace index = .exited 42))

theorem viaWrite_results (initial : State) (outcome : OS.LinuxWrite.Outcome)
    (final : SyscallRequest) (count : Nat)
    (code : CodeAt initial.memory initial.rip WriteExit.bytes)
    (execution : ViaWrite initial WriteExit.payload outcome final count) :
    WriteExitResults outcome final count := by
  obtain ⟨first, firstCount, after, lastCount, firstRun, _, _, _, kernel, returned,
    lastRun, cost⟩ := execution
  obtain ⟨same, firstCost⟩ := firstRun.deterministic (WriteExit.reaches_write initial code).1
  subst first
  have exitRun := WriteExit.exits_after_write initial after outcome code returned
  obtain ⟨lastRequest, lastCost⟩ := lastRun.deterministic exitRun.1
  subst final
  have allowed := OS.LinuxWrite.execution_result WriteExit.payload outcome kernel
  refine ⟨by omega, exitRun.2.2.1, exitRun.2.2.2, allowed,
    OS.LinuxWrite.emitted_prefix _ _, OS.LinuxWrite.emitted_length_le _ _, ?_, ?_⟩
  · intro full
    subst outcome
    exact OS.LinuxWrite.full_success WriteExit.payload
  · exact Exit42.kernel_results after

theorem viaWrite_exists (initial : State) (outcome : OS.LinuxWrite.Outcome)
    (code : CodeAt initial.memory initial.rip WriteExit.bytes)
    (fixed : initial.rip = WriteExit.entryAddress)
    (allowed : OS.LinuxWrite.Permitted WriteExit.payload outcome) :
    ∃ final, ViaWrite initial WriteExit.payload outcome final 8 := by
  let after := resume (WriteExit.request initial) (OS.LinuxWrite.rawResult outcome) 0 0 0
  have returned : Returns (WriteExit.request initial) (OS.LinuxWrite.rawResult outcome) after :=
    resume_returns _ _ _ _ _
  have exitRun := WriteExit.exits_after_write initial after outcome code returned
  refine ⟨Exit42.request after, WriteExit.request initial, 5, after, 3,
    (WriteExit.reaches_write initial code).1, (WriteExit.request_supported initial).1,
    (WriteExit.request_supported initial).2.1, ?_, .next (.finish allowed) .refl,
    returned, exitRun.1, rfl⟩
  simpa [WriteExit.request, WriteExit.callState, SyscallRequest.argument] using
    WriteExit.payload_readable initial code fixed

def WriteExitGuarantee (file : List Byte) (image : ELF.Image) (initial : State) : Prop :=
  let user := entry file image empty initial
  ELF.load file empty = .ok ⟨image, ELF.install file image empty⟩ ∧
  Invokes user (WriteExit.request user) 5 ∧ ¬ Diverges user ∧
  (∀ outcome, OS.LinuxWrite.Permitted WriteExit.payload outcome →
    ∃ final, ViaWrite user WriteExit.payload outcome final 8) ∧
  (∀ outcome final count, ViaWrite user WriteExit.payload outcome final count →
    WriteExitResults outcome final count)

theorem writeExit_standalone (file : List Byte) (image : ELF.Image)
    (checked : checkWriteExit42 file image = true) (initial : State) :
    WriteExitGuarantee file image initial := by
  obtain ⟨container, codeCheck⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨parsed, address⟩ := Bool.and_eq_true_iff.mp container
  have parsedImage := ELF.checkParsed_sound file image parsed
  have code := ELF.checked_entry_code file image WriteExit.bytes empty codeCheck
  have invocation := WriteExit.reaches_write (entry file image empty initial) code
  refine ⟨ELF.load_success file empty image parsedImage (empty_is_fresh image),
    invocation.1, invocation.2.1, ?_, ?_⟩
  · intro outcome allowed
    apply viaWrite_exists _ outcome code _ allowed
    change ELF.codeAddress image = WriteExit.entryAddress
    have fixed : image.entry = 0x400000 := of_decide_eq_true address
    simp [ELF.codeAddress, fixed, WriteExit.entryAddress]
  · intro outcome final count execution
    exact viaWrite_results _ outcome final count code execution

end EDSL.Process
