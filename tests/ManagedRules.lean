/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.ManagedRules
import EDSL.OS.TSO64.Return
import EDSL.OS.FetchAddBatch64.Certificate
import tests.FetchAddCalls64
import tests.TSO64SharedCells
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.ManagedRules
open X86 OS.TSO64

/-- MOV RAX,[RDI]; MOV [RDI],RSI; RET. The loaded return word differs from
the buffered store, so a response read from current/pending RAM is incorrect.
The high bits also distinguish a full-width return from truncation. -/
def start : Except Fault OS.TSO64.State :=
  TSO64SharedCells.start 0x00c3378948078b48 0 0xfedcba9876543210 9 23 0 0

def responseBeforePublication : Except Fault
    (Option (Nat × Word) × Option (Nat × Word) ×
      Option (Word × Word × Phase × Nat × Nat) × Except Error Word × Except Error Word ×
      Option (Nat × Word) × Except Error Word) := do
  let initial ← start
  let loaded ← step initial (.issue 0 false) .sharedCell
  let stored ← step loaded.1 (.issue 0 true) .sharedCell
  let returned ← step stored.1 (.issue 0 false) .sharedCell
  let published ← step returned.1 (.drain 0) .sharedCell
  pure (Return.returnValue stored, Return.returnValue returned,
    returned.1.workers[0]?.map (fun worker =>
      (worker.context.registers .rsp, worker.context.flags, worker.phase,
        worker.pending.length, worker.nextStore)),
    loadQWord (OS.TSO64.published returned.1.world) 65536,
    readWord (OS.TSO64.published returned.1.world) 262144,
    Return.returnValue published, loadQWord (OS.TSO64.published published.1.world) 65536)

/-- The actual response retains the earlier loaded qword, while RET preserves
the unpublished store and its counter. Only the later drain changes RAM.
Ordinary store/drain observations are not responses. The original caller slot
and flags are unchanged, and RSP advances by the one popped qword. -/
theorem return_keeps_buffered_store_and_original_caller_frame :
    responseBeforePublication = .ok
      (none, some (0, 0xfedcba9876543210), some (262152, 0x200202, .returned, 1, 1),
        .ok 0xfedcba9876543210, .ok 0x7000, none, .ok 9) := by rfl

/-- A peer response must be selected from that actual successor's context.
The two actual loads see different words across the first publication. -/
def peerResponse : Except Fault
    (Option (Nat × Word) × Except Error Word × Option (Nat × Word) × Except Error Word) := do
  let initial ← start
  let writer ← schedule initial [.issue 0 false, .issue 0 false] .sharedCell
  let drained ← step writer.1 (.drain 0) .sharedCell
  let peer ← schedule drained.1 [.issue 1 false, .issue 1 true] .sharedCell
  let peerReturned ← step peer.1 (.issue 1 false) .sharedCell
  let writerReturned ← step peerReturned.1 (.issue 0 false) .sharedCell
  pure (Return.returnValue peerReturned,
    loadQWord (OS.TSO64.published peerReturned.1.world) 65536,
    Return.returnValue writerReturned,
    loadQWord (OS.TSO64.published writerReturned.1.world) 65536)

/-- Later publication must not replace a saved return value. The peer sees the
new word, and response tids follow the selected actual RET rather than actors.
Reading the other worker's RAX would fail either response comparison. -/
theorem responses_retain_the_selected_thread_and_loaded_value :
    peerResponse = .ok (some (1, 9), .ok 9,
      some (0, 0xfedcba9876543210), .ok 9) := by rfl

end EDSL.Tests.ManagedRules

#print axioms EDSL.X86.VCGen.ManagedRules.local_code
#print axioms EDSL.X86.VCGen.ManagedRules.step_ordinary
#print axioms EDSL.OS.TSO64.Return.returned_origin
#print axioms EDSL.OS.TSO64.Return.returnValue_sound
#print axioms EDSL.OS.TSO64.Return.ReturnOrigin.frame
#audit_edsl
