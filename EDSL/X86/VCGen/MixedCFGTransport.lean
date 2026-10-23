/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.MixedCFG
import EDSL.X86.VCGen.AtomicMethods

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

/-!
Current and guarded fetch transport for mixed structural certificates. Static
decoding is relocated through successful executable fetches, with the exact
locked tag's no-wrap bound. Current code, original loan containment, and live
leases remain explicit environmental premises of the public graph bridges.

Dispatch equality retains the production executors, including their errors,
blocking, operand checks, FIFO checks, and actual shared-memory re-decoding.
-/

namespace EDSL.X86.VCGen.MixedCFG
open OS OS.TSO64

private theorem arithmetic_decode_transport {source destination : X86.State}
    {instruction : AddRMW64.Instruction}
    (transport : Sequential.SuccessfulFetchTransport source destination)
    (bound : destination.rip.toNat + instruction.length ≤ 2^64)
    (decoded : AddRMW64.decodeAt source = .ok instruction) :
    AddRMW64.decodeAt destination = .ok instruction := by
  have code := AddRMW64.decodeAt_code decoded
  apply AddRMW64.decodeAt_of_code instruction
  refine ⟨?_, ?_⟩
  · simpa only [AddRMW64.Instruction.bytes_length] using bound
  · intro offset byte present
    have short : offset < instruction.length := by
      simpa only [AddRMW64.Instruction.bytes_length] using
        (List.getElem_of_getElem? present).1
    have length : instruction.length ≤ 5 := by
      cases instruction with
      | xadd old => change 5 ≤ 5; decide
      | addImm8 encoding => change 5 ≤ 5; decide
      | inc encoding => change 4 ≤ 5; decide
    exact transport offset (by omega) byte (code.2 offset byte present)

private theorem decode_transport {family : RMWFamily}
    {source destination : X86.State} {instruction : OS.TSO64.Decoded family}
    (transport : Sequential.SuccessfulFetchTransport source destination)
    (lockedBound : ∀ locked, instruction = .locked locked →
      destination.rip.toNat + (family.embed locked).length ≤ 2^64)
    (decoded : OS.TSO64.decode source family = .ok instruction) :
    OS.TSO64.decode destination family = .ok instruction := by
  cases first : fetchByte source.memory source.rip with
  | error fault =>
    simp [OS.TSO64.decode, first, Except.mapError] at decoded
  | ok byte =>
    have next := transport 0 (by decide) byte
      (by simpa only [BitVec.add_zero] using first)
    simp only [BitVec.add_zero] at next
    by_cases lock : byte = 0xf0#8
    · subst byte
      have actual : ∃ locked : family.Instruction, instruction = .locked locked ∧
          family.decodeAt source = .ok locked := by
        cases output : family.decodeAt source with
        | error fault =>
          simp [OS.TSO64.decode, first, output, Except.mapError] at decoded
        | ok locked =>
          have same : (.locked locked : OS.TSO64.Decoded family) = instruction := by
            simpa [OS.TSO64.decode, first, output, Except.mapError] using decoded
          exact ⟨locked, same.symm, rfl⟩
      obtain ⟨locked, rfl, actual⟩ := actual
      have destinationDecoded : family.decodeAt destination = .ok locked := by
        cases family with
        | xaddOnly =>
          have code := LockedAdd64.decodeAt_code actual
          have destinationCode : CodeAt destination.memory destination.rip locked.bytes := by
            refine ⟨lockedBound locked rfl, ?_⟩
            intro offset byte present
            have bound := (List.getElem_of_getElem? present).1
            exact transport offset (by change offset < 5 at bound; omega) byte
              (code.2 offset byte present)
          exact LockedAdd64.decodeAt_of_code locked destinationCode
        | arithmetic =>
          exact arithmetic_decode_transport transport (lockedBound locked rfl) actual
      simp [OS.TSO64.decode, next, destinationDecoded, Except.mapError]
    · have actual : ∃ ordinary, instruction = .ordinary ordinary ∧
          Sequential.decodeAt source = .ok ordinary := by
        cases output : Sequential.decodeAt source with
        | error fault =>
          simp [OS.TSO64.decode, first, lock, output, Except.mapError] at decoded
        | ok ordinary =>
          have same : (.ordinary ordinary : OS.TSO64.Decoded family) = instruction := by
            simpa [OS.TSO64.decode, first, lock, output, Except.mapError] using decoded
          exact ⟨ordinary, same.symm, rfl⟩
      obtain ⟨ordinary, rfl, actual⟩ := actual
      simp [OS.TSO64.decode, next, lock,
        Sequential.decodeAt_transport transport actual, Except.mapError]

private theorem offset_nat {bytes : List Byte} {memory : Memory} {base : Word}
    (code : CodeAt memory base bytes) {offset : Nat} (inside : offset < bytes.length) :
    (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
  have small : offset < 2^64 := by have := code.1; omega
  have sum : base.toNat + offset < 2^64 := by have := code.1; omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt sum]

variable {family : RMWFamily} {caps : Caps} {bytes : List Byte} {graph : Graph family}

/-- Whole-window validity transports the authenticated current instruction.
The locked no-wrap gate follows from its exact span and current code window. -/
theorem Valid.decoded (valid : Valid family caps bytes graph)
    {memory : Memory} {base : Word} (code : CodeAt memory base bytes)
    (i : graph.Index) (cpu : X86.State) (ram : cpu.memory = memory)
    (pc : cpu.rip = base + BitVec.ofNat 64 (graph.node i).offset) :
    OS.TSO64.decode cpu family = .ok (graph.node i).instruction := by
  apply decode_transport
    (Sequential.code_fetch_transport_of_bound code valid.fetchNoWrap
      (graph.node i).offset (valid.nodes i).1 cpu ram pc) ?_ (valid.nodes i).2.1
  intro locked same
  rw [pc, offset_nat code (valid.nodes i).1]
  have span := valid.instruction_span i
  rw [same] at span
  change (graph.node i).offset + (family.embed locked).length ≤ bytes.length at span
  have bound := code.1
  omega

/-- Guarded fetch retains the entire current code window under the original
code loan; no resource is inferred from the graph certificate. -/
theorem Valid.guarded_decoded (valid : Valid family caps bytes graph)
    {state : OS.TSO64.State} {worker : Worker} {base : Word}
    (code : CodeAt (published state.world) base bytes)
    (fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region)
    (i : graph.Index)
    (pc : worker.context.rip = base + BitVec.ofNat 64 (graph.node i).offset) :
    OS.TSO64.decode (fetchCPU state worker) family = .ok (graph.node i).instruction :=
  valid.decoded (AtomicMethods.guarded_code code fits) i (fetchCPU state worker) rfl pc

/-- The exact authenticated instruction span lies in the original code loan. -/
theorem Valid.codeFits (valid : Valid family caps bytes graph)
    {state : OS.TSO64.State} {worker : Worker} {base : Word}
    (code : CodeAt (published state.world) base bytes)
    (fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region)
    (i : graph.Index)
    (pc : worker.context.rip = base + BitVec.ofNat 64 (graph.node i).offset) :
    OS.TSO64.codeFits worker (instructionLength (graph.node i).instruction) := by
  have natural := offset_nat code (valid.nodes i).1
  have lower := fits.1
  have upper := fits.2
  have span := valid.instruction_span i
  change worker.resources.code.loan.region.base.toNat ≤ base.toNat at lower
  change base.toNat + bytes.length ≤
    worker.resources.code.loan.region.base.toNat + worker.resources.code.loan.region.length at upper
  change worker.resources.code.loan.region.base.toNat ≤ worker.context.rip.toNat ∧
    worker.context.rip.toNat + instructionLength (graph.node i).instruction ≤
      worker.resources.code.loan.region.base.toNat + worker.resources.code.loan.region.length
  rw [pc, natural]
  constructor <;> omega

/-- Exact equality with actual scheduler dispatch, retaining all executor
failures and blocking. Current leases are premises, not static graph facts. -/
theorem Valid.issue_eq_dispatch (valid : Valid family caps bytes graph)
    {state : OS.TSO64.State} {worker : Worker} {tid : Nat} {base : Word}
    (live : state.workers[tid]? = some worker) (running : worker.phase = .running)
    (codeCurrent : LeaseCurrent state.world worker.resources.actor worker.resources.code)
    (callerCurrent : LeaseCurrent state.world worker.resources.actor worker.resources.caller)
    (code : CodeAt (published state.world) base bytes)
    (fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region)
    (i : graph.Index)
    (pc : worker.context.rip = base + BitVec.ofNat 64 (graph.node i).offset)
    (af : Bool) (authority : OS.TSO64.Profile) :
    OS.TSO64.issue state tid af authority family =
      match (graph.node i).instruction with
      | .ordinary instruction => OS.TSO64.ordinary state tid worker instruction af authority
      | .locked instruction => OS.TSO64.lockedFor family state tid worker instruction := by
  have decoded := valid.guarded_decoded code fits i pc
  simp [OS.TSO64.issue, live, running, codeCurrent, callerCurrent, decoded]
  rfl

private def incFourBytes : List Byte := [0xf0, 0x48, 0xff, 0x07]

private def incFourInstruction : AddRMW64.Instruction :=
  .inc ⟨0x48, 0x07, by decide, by decide, by decide⟩

private def incFourMemory : Memory where
  read address :=
    if 4096 ≤ address.toNat then incFourBytes[address.toNat - 4096]? else none
  executable address := decide (4096 ≤ address.toNat ∧ address.toNat < 4100)

private def incFourCPU : X86.State :=
  ⟨fun _ => 0, 4096, 0, incFourMemory⟩

/-- Relocate the mixed decoder to nonzero RIP with exactly four executable
INC bytes and a denied fifth fetch. This is deliberately private: a terminal
INC's fallthrough cannot close a public Valid graph. -/
private theorem inc_four_byte_relocation :
    OS.TSO64.decode incFourCPU .arithmetic = .ok (.locked incFourInstruction) ∧
      fetchByte incFourCPU.memory (incFourCPU.rip + 4) =
        .error (.inaccessibleInstruction (incFourCPU.rip + 4)) := by
  have code : CodeAt incFourCPU.memory 4096 incFourBytes := by
    refine ⟨by decide, ?_⟩
    intro offset byte present
    match offset with
    | 0 | 1 | 2 | 3 =>
      simp [incFourBytes] at present
      subst byte
      rfl
    | offset + 4 => simp [incFourBytes] at present
  let source := Sequential.codeState incFourBytes 0
  have sourceDecoded : OS.TSO64.decode source .arithmetic = .ok (.locked incFourInstruction) := by
    have first : fetchByte source.memory source.rip = .ok 0xf0 := by rfl
    have actual : AddRMW64.decodeAt source = .ok incFourInstruction := by rfl
    simp [OS.TSO64.decode, first, RMWFamily.decodeAt, actual, Except.mapError, ok_bind]
    rfl
  have transport : Sequential.SuccessfulFetchTransport source incFourCPU :=
    Sequential.code_fetch_transport_of_bound code (by decide) 0 (by decide)
      incFourCPU rfl (by decide)
  refine ⟨decode_transport transport ?_ sourceDecoded, ?_⟩
  · intro locked same
    have tag : incFourInstruction = locked := OS.TSO64.Decoded.locked.inj same
    subst locked
    decide
  · rfl

#print axioms Valid.decoded
#print axioms Valid.guarded_decoded
#print axioms Valid.codeFits
#print axioms Valid.issue_eq_dispatch
#print axioms inc_four_byte_relocation

end EDSL.X86.VCGen.MixedCFG

#audit_edsl
