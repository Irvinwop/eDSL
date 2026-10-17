/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallStackPrograms
import EDSL.CallStack.Geometry

set_option warningAsError true

namespace EDSL.CallStack.Compiler
open X86 OS

/-- The instruction immediately after the actual CALL. -/
def continuation : Profile → Node
  | .gccSeparate => .pop
  | _ => .increment

theorem call_target {profile : Profile} {base : Word} {state : State}
    (pc : state.rip = base + BitVec.ofNat 64 (offset profile .call)) :
    CallReturn.callTarget state (displacement profile) = base + BitVec.ofNat 64 (offset profile .helper) := by
  cases profile <;> simp [CallReturn.callTarget, CallReturn.returnAddress, pc,
    offset, displacement, BitVec.add_assoc]

theorem call_continuation {profile : Profile} {base : Word} {state : State}
    (pc : state.rip = base + BitVec.ofNat 64 (offset profile .call)) :
    CallReturn.returnAddress state = base + BitVec.ofNat 64 (offset profile (continuation profile)) := by
  cases profile <;> simp [CallReturn.returnAddress, pc, offset, continuation, BitVec.add_assoc]

theorem continuation_active (profile : Profile) : active profile (continuation profile) = true := by
  cases profile <;> rfl

/-- Exact current bytes supply canonicality for both the helper and the actual
pushed continuation. Neither is an extra admitted future-success premise. -/
theorem call_addresses {profile : Profile} {base : Word} {state : State}
    (code : CodeAt state.memory base (bytes profile))
    (pc : state.rip = base + BitVec.ofNat 64 (offset profile .call)) :
    canonical (CallReturn.callTarget state (displacement profile)) = true ∧
      canonical (CallReturn.returnAddress state) = true := by
  rw [call_target pc, call_continuation pc]
  exact ⟨Sequential.code_canonical_offset code _ (inside profile .helper),
    Sequential.code_canonical_offset code _ (inside profile (continuation profile))⟩

def finish (state : State) (target : Word) : State :=
  { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target }

theorem raw_ret {profile : Profile} {base : Word} {state : State} {target : Word}
    (code : CodeAt state.memory base (bytes profile)) (node : Node)
    (ret : instruction profile node = .sequential (.legacy .ret))
    (present : active profile node = true)
    (pc : state.rip = base + BitVec.ofNat 64 (offset profile node))
    (loaded : readWord state.memory (state.registers .rsp) = .ok target)
    (canon : canonical target = true) (af : Bool) :
    CallReturn.rawStep af state = .ok ⟨.returned (finish state target),
      [⟨.stack, state.registers .rsp, 8⟩]⟩ := by
  rw [CallReturn.rawStep_eq_execute af (decode code node present pc), ret]
  exact CallReturn.execute_ret_success_iff.mpr ⟨target, loaded, canon, rfl, rfl⟩

theorem internal_ret {profile : Profile} {base originalSlot : Word} {state : State} {target : Word}
    (code : CodeAt state.memory base (bytes profile))
    (pc : state.rip = base + BitVec.ofNat 64 (offset profile .innerRet))
    (loaded : readWord state.memory (state.registers .rsp) = .ok target)
    (canon : canonical target = true) (internal : state.registers .rsp ≠ originalSlot) (af : Bool) :
    CallReturn.boundaryStep originalSlot af state = .ok ⟨.next (finish state target),
      [⟨.stack, state.registers .rsp, 8⟩]⟩ :=
  CallReturn.boundaryStep_internal_ret internal (raw_ret code .innerRet rfl rfl pc loaded canon af)

theorem terminal_ret {profile : Profile} {base originalSlot : Word} {state : State} {target : Word}
    (code : CodeAt state.memory base (bytes profile))
    (pc : state.rip = base + BitVec.ofNat 64 (offset profile .ret))
    (loaded : readWord state.memory (state.registers .rsp) = .ok target)
    (canon : canonical target = true) (original : state.registers .rsp = originalSlot) (af : Bool) :
    CallReturn.boundaryStep originalSlot af state = .ok ⟨.returned (finish state target),
      [⟨.stack, state.registers .rsp, 8⟩]⟩ :=
  CallReturn.boundaryStep_returned_iff.mpr ⟨original, raw_ret code .ret rfl rfl pc loaded canon af⟩

end EDSL.CallStack.Compiler
