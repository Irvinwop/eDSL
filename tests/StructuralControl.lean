/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.StructuralControl
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.StructuralControl
open X86 Sequential

/-!
Owned synthetic bytes use the production decoder and `stepWith`. Successor
states and atomic events are inferred from that execution, then checked against
literal expected results. Structural continuation proves control only; it adds
no memory frame, executable-text preservation, concurrency or OS safety claim.
-/

private def memory (bytes : List Byte) (target : Word) (allowWrite : Bool) : Memory where
  read address :=
    if 0x4000 ≤ address.toNat ∧ address.toNat < 0x4000 + bytes.length then
      bytes[address.toNat - 0x4000]?
    else if target.toNat ≤ address.toNat ∧ address.toNat < target.toNat + 4 then
      [0x2a, 0, 0, 0][address.toNat - target.toNat]?
    else if 0x9000 ≤ address.toNat ∧ address.toNat < 0x9008 then
      [0, 0x50, 0, 0, 0, 0, 0, 0][address.toNat - 0x9000]?
    else none
  executable address := decide (0x4000 ≤ address.toNat ∧
    address.toNat < 0x4000 + bytes.length)
  writable address := allowWrite && decide (target.toNat ≤ address.toNat ∧
    address.toNat < target.toNat + 4)

private def entry (bytes : List Byte) (target : Word := 0x8000)
    (allowWrite : Bool := true) : State where
  registers register := match register with
    | .rax => 1
    | .rsi => 0x11223344
    | .rdi => target
    | .rsp => 0x9000
    | _ => 0
  rip := 0x4000
  flags := 0xabcdef
  memory := memory bytes target allowWrite

private theorem three_byte_code (a b c : Byte) (target : Word) (allowWrite : Bool) :
    CodeAt (entry [a, b, c] target allowWrite).memory 0x4000 [a, b, c] := by
  refine ⟨by change 16384 + 3 ≤ 2 ^ 64; decide +kernel, ?_⟩
  intro offset byte present
  match offset with
  | 0 => cases present; rfl
  | 1 => cases present; rfl
  | 2 => cases present; rfl
  | _ + 3 => cases present

private theorem five_byte_code (a b c d e : Byte) (target : Word) (allowWrite : Bool) :
    CodeAt (entry [a, b, c, d, e] target allowWrite).memory 0x4000 [a, b, c, d, e] := by
  refine ⟨by change 16384 + 5 ≤ 2 ^ 64; decide +kernel, ?_⟩
  intro offset byte present
  match offset with
  | 0 => cases present; rfl
  | 1 => cases present; rfl
  | 2 => cases present; rfl
  | 3 => cases present; rfl
  | 4 => cases present; rfl
  | _ + 5 => cases present

namespace Store

def bytes : List Byte := [0x89, 0x37, 0xc3]

def graph : CFG.Graph := ⟨[
  ⟨0, .legacy .storeEsiRdi, true, 1⟩,
  ⟨2, .legacy .ret, false, 0⟩], 1⟩

theorem valid : CFG.Structural.Valid bytes graph :=
  CFG.Structural.check_sound (by decide +kernel)

private theorem code : CodeAt (entry bytes).memory 0x4000 bytes :=
  three_byte_code 0x89 0x37 0xc3 0x8000 true

-- Explicit bytes detect wrong source, width, byte order, address or RIP.
theorem writes_and_follows_edge (choices : FlagChoices) :
    ∃ observation after,
      Sequential.decodeAt (entry bytes) = .ok (.legacy .storeEsiRdi) ∧
      stepWith choices (entry bytes) = .ok observation ∧
      observation.result = .next after ∧
      (after.memory.read 0x8000, after.memory.read 0x8001,
        after.memory.read 0x8002, after.memory.read 0x8003, after.rip) =
        (some 0x44, some 0x33, some 0x22, some 0x11, 0x4002) ∧
      ∃ destination : graph.Index, graph.Edge ⟨0, by decide +kernel⟩ destination ∧
        after.rip = 0x4000 + BitVec.ofNat 64 (graph.node destination).offset := by
  refine ⟨_, _, rfl, rfl, rfl, rfl, ?_⟩
  exact valid.continues (initial := entry bytes) (choices := choices)
    code ⟨0, by decide +kernel⟩ rfl rfl (.inl rfl)

private def denied : State := entry bytes 0x8000 false

theorem denied_write (choices : FlagChoices) :
    CodeAt denied.memory 0x4000 bytes ∧
    Sequential.decodeAt denied = .ok (.legacy .storeEsiRdi) ∧
    stepWith choices denied = .error (.writeDenied 0x8000) :=
  ⟨three_byte_code 0x89 0x37 0xc3 0x8000 false, rfl, rfl⟩

theorem denied_cannot_continue (choices : FlagChoices) :
    ¬ ∃ observation after, stepWith choices denied = .ok observation ∧
      CFG.Structural.Continues observation after := by
  rintro ⟨_, _, actual, _⟩
  rw [(denied_write choices).2.2] at actual
  cases actual

end Store

namespace Exchange

def bytes : List Byte := [0x87, 0x07, 0xc3]

def graph : CFG.Graph := ⟨[
  ⟨0, .legacy .exchangeEaxRdi, true, 1⟩,
  ⟨2, .legacy .ret, false, 0⟩], 1⟩

theorem valid : CFG.Structural.Valid bytes graph :=
  CFG.Structural.check_sound (by decide +kernel)

private theorem code : CodeAt (entry bytes).memory 0x4000 bytes :=
  three_byte_code 0x87 0x07 0xc3 0x8000 true

-- The event witness comes from actual `stepWith`, without constructing one.
theorem atomic_and_follows_edge (choices : FlagChoices) :
    ∃ observation event after,
      Sequential.decodeAt (entry bytes) = .ok (.legacy .exchangeEaxRdi) ∧
      stepWith choices (entry bytes) = .ok observation ∧
      observation.result = .atomic event after ∧
      (event.address, event.before, event.after) = (0x8000, 42, 1) ∧
      (loadDWord after.memory 0x8000, after.registers .rax, after.flags,
        after.rip, observation.reads) =
        (.ok 1, 42, 0xabcdef, 0x4002, [⟨.data, 0x8000, 4⟩]) ∧
      ∃ destination : graph.Index, graph.Edge ⟨0, by decide +kernel⟩ destination ∧
        after.rip = 0x4000 + BitVec.ofNat 64 (graph.node destination).offset := by
  refine ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact valid.continues (initial := entry bytes) (choices := choices)
    code ⟨0, by decide +kernel⟩ rfl rfl (.inr ⟨_, rfl⟩)

end Exchange

namespace FetchAdd

def bytes : List Byte := [0xf0, 0x0f, 0xc1, 0x07, 0xc3]

def graph : CFG.Graph := ⟨[
  ⟨0, .legacy .fetchAddEaxRdi, true, 1⟩,
  ⟨4, .legacy .ret, false, 0⟩], 1⟩

theorem valid : CFG.Structural.Valid bytes graph :=
  CFG.Structural.check_sound (by decide +kernel)

private theorem code : CodeAt (entry bytes).memory 0x4000 bytes :=
  five_byte_code 0xf0 0x0f 0xc1 0x07 0xc3 0x8000 true

/-- Actual locked XADD differs from XCHG: it writes 42+1, returns the old
value, records the operand read, and reaches the four-byte fallthrough edge. -/
theorem atomic_and_follows_edge (choices : FlagChoices) :
    ∃ observation event after,
      Sequential.decodeAt (entry bytes) = .ok (.legacy .fetchAddEaxRdi) ∧
      stepWith choices (entry bytes) = .ok observation ∧
      observation.result = .atomic event after ∧
      (event.address, event.before, event.after) = (0x8000, 42, 43) ∧
      (loadDWord after.memory 0x8000, after.registers .rax, after.rip, observation.reads) =
        (.ok 43, 42, 0x4004, [⟨.data, 0x8000, 4⟩]) ∧
      ∃ destination : graph.Index, graph.Edge ⟨0, by decide +kernel⟩ destination ∧
        after.rip = 0x4000 + BitVec.ofNat 64 (graph.node destination).offset := by
  refine ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact valid.continues (initial := entry bytes) (choices := choices)
    code ⟨0, by decide +kernel⟩ rfl rfl (.inr ⟨_, rfl⟩)

end FetchAdd

-- Constructor exclusions are generic over every request/state and read list.
theorem syscall_not_continuing (request : SyscallRequest) (reads : List Read)
    (after : State) : ¬ CFG.Structural.Continues ⟨.syscall request, reads⟩ after := by
  rintro (impossible | ⟨_, impossible⟩) <;> cases impossible

theorem returned_not_continuing (returned : State) (reads : List Read)
    (after : State) : ¬ CFG.Structural.Continues ⟨.returned returned, reads⟩ after := by
  rintro (impossible | ⟨_, impossible⟩) <;> cases impossible

namespace Boundaries

def bytes : List Byte := [0x0f, 0x05, 0xc3]

def graph : CFG.Graph := ⟨[
  ⟨0, .legacy .syscall, true, 1⟩,
  ⟨2, .legacy .ret, false, 0⟩], 1⟩

-- Structural admission also authenticates instructions that end this step's
-- control contract; it cannot turn their outcomes into continuations.
theorem valid : CFG.Structural.Valid bytes graph :=
  CFG.Structural.check_sound (by decide +kernel)

private theorem code : CodeAt (entry bytes).memory 0x4000 bytes :=
  three_byte_code 0x0f 0x05 0xc3 0x8000 true

theorem syscall_stops (choices : FlagChoices) :
    ∃ observation request,
      CodeAt (entry bytes).memory 0x4000 bytes ∧
      Sequential.decodeAt (entry bytes) = .ok (.legacy .syscall) ∧
      stepWith choices (entry bytes) = .ok observation ∧
      observation.result = .syscall request ∧
      request.continuation = 0x4002 ∧
      ∀ after, ¬ CFG.Structural.Continues observation after := by
  refine ⟨_, _, code, rfl, rfl, rfl, rfl, ?_⟩
  intro after
  exact syscall_not_continuing _ _ after

private def atRet : State := { entry bytes with rip := 0x4002 }

theorem ret_stops (choices : FlagChoices) :
    ∃ observation returned,
      CodeAt atRet.memory 0x4000 bytes ∧
      Sequential.decodeAt atRet = .ok (.legacy .ret) ∧
      stepWith choices atRet = .ok observation ∧
      observation.result = .returned returned ∧
      (returned.rip, returned.registers .rsp) = (0x5000, 0x9008) ∧
      ∀ after, ¬ CFG.Structural.Continues observation after := by
  refine ⟨_, _, code, rfl, rfl, rfl, rfl, ?_⟩
  intro after
  exact returned_not_continuing _ _ after

end Boundaries

namespace SelfModifying

-- Deliberately writable text: the store replaces the next RET with NOP.
-- Its remaining three written bytes are mapped ordinary RAM past this window.
private def initial : State :=
  (entry Store.bytes 0x4002).writeRegister .rsi 0x90909090

private theorem code : CodeAt initial.memory 0x4000 Store.bytes :=
  three_byte_code 0x89 0x37 0xc3 0x4002 true

theorem edge_without_code_frame (choices : FlagChoices) :
    ∃ observation after,
      Sequential.decodeAt initial = .ok (.legacy .storeEsiRdi) ∧
      stepWith choices initial = .ok observation ∧
      observation.result = .next after ∧
      (after.memory.read 0x4002, after.memory.read 0x4003,
        after.memory.read 0x4004, after.memory.read 0x4005, after.rip) =
        (some 0x90, some 0x90, some 0x90, some 0x90, 0x4002) ∧
      Sequential.decodeAt after = .ok (.nop .one) ∧
      (∃ destination : Store.graph.Index,
        Store.graph.Edge ⟨0, by decide +kernel⟩ destination ∧
        after.rip = 0x4000 + BitVec.ofNat 64 (Store.graph.node destination).offset) ∧
      ¬ CodeAt after.memory 0x4000 Store.bytes := by
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact Store.valid.continues (initial := initial) (choices := choices)
      code ⟨0, by decide +kernel⟩ rfl rfl (.inl rfl)
  · intro retained
    have oldRet := retained.2 2 0xc3 rfl
    change (Except.ok (0x90 : Byte) : Except Error Byte) = .ok 0xc3 at oldRet
    exact (by decide +kernel : (0x90 : Byte) ≠ 0xc3) (Except.ok.inj oldRet)

end SelfModifying
end EDSL.Tests.StructuralControl

#print axioms EDSL.Tests.StructuralControl.Store.valid
#print axioms EDSL.Tests.StructuralControl.Store.writes_and_follows_edge
#print axioms EDSL.Tests.StructuralControl.Store.denied_write
#print axioms EDSL.Tests.StructuralControl.Store.denied_cannot_continue
#print axioms EDSL.Tests.StructuralControl.Exchange.valid
#print axioms EDSL.Tests.StructuralControl.Exchange.atomic_and_follows_edge
#print axioms EDSL.Tests.StructuralControl.FetchAdd.valid
#print axioms EDSL.Tests.StructuralControl.FetchAdd.atomic_and_follows_edge
#print axioms EDSL.Tests.StructuralControl.syscall_not_continuing
#print axioms EDSL.Tests.StructuralControl.returned_not_continuing
#print axioms EDSL.Tests.StructuralControl.Boundaries.valid
#print axioms EDSL.Tests.StructuralControl.Boundaries.syscall_stops
#print axioms EDSL.Tests.StructuralControl.Boundaries.ret_stops
#print axioms EDSL.Tests.StructuralControl.SelfModifying.edge_without_code_frame
#audit_edsl
