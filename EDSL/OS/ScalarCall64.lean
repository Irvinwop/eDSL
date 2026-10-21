/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Setup
import EDSL.PureCall.Contract
import EDSL.Audit

/-!
Represented scalar SysV entry and return obligations for managed calls.
These predicates describe present machine state, caller resources and ABI
observations independently of a decoder, method cutpoint or proof strategy.
Return does not require publication of a buffered store. Collection separately
requires an empty own queue, as in the production scheduler API.
Unrepresented CPU feature state and native ABI correspondence remain external.
-/

set_option autoImplicit false

namespace EDSL.OS.ScalarCall64
open X86 TSO64

/-- A complete callable byte image and its entry address, independent of its
instruction family, behavior contract or artifact provenance. -/
structure Image where
  base : Word
  bytes : List Byte
  deriving DecidableEq, Repr

/-- Scalar entry alignment, clear DF and a nonwrapping canonical post-pop RSP.
The original protected caller slot and its value are separate resource facts. -/
structure Entry (worker : Worker) : Prop where
  aligned : ((worker.context.registers .rsp).toNat + 8) % 16 = 0
  direction : worker.context.flags.getLsbD 10 = false
  stackBound : (worker.context.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : canonical (worker.context.registers .rsp + 8) = true

/-- Original caller, represented callee-saved registers and current resources
at return. There is deliberately no pending-queue or shared-RAM snapshot field:
publication and interference are separate behavioral obligations. -/
structure ReturnFrame (before after : TSO64.State) (tid : Nat) (initial final : Worker) : Prop where
  initialLive : before.workers[tid]? = some initial
  live : after.workers[tid]? = some final
  phase : final.phase = .returned
  resources : final.resources = initial.resources
  current : ResourcesValid after.world final.resources
  registers : ∀ register ∈ PureCall.calleeSaved,
    final.context.registers register = initial.context.registers register
  flags : final.context.flags = initial.context.flags
  stack : final.context.registers .rsp = initial.context.registers .rsp + 8
  stackCanonical : canonical (final.context.registers .rsp) = true
  direction : final.context.flags.getLsbD 10 = false
  returnCanonical : canonical final.context.rip = true
  continuation : ∃ address,
    Borrowing.loadWord64 before.world.legacy.shared initial.resources.actor
      initial.resources.caller.identifier initial.resources.callerAddress = .ok address ∧
    final.context.rip = address

/-- Publication is required by collection, independently of the actual RET.
No resource is released by this read-only production observation. -/
theorem ReturnFrame.collect {before after : TSO64.State} {tid : Nat} {initial final : Worker}
    (frame : ReturnFrame before after tid initial final) (empty : final.pending = []) :
    TSO64.collect after tid = .ok (final.context.registers .rax) := by
  simp [TSO64.collect, frame.live, frame.phase, empty]

end EDSL.OS.ScalarCall64

#audit_edsl
