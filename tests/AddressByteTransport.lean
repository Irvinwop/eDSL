/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.X86.Sequential.Code
import EDSL.X86.Sequential.Machine

import tests.Support.ExceptDecidable

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.AddressByteTransport
open scoped EDSL.Tests.Support
open X86 X86.Sequential

/-- Exact finite code suffices at an arbitrary current executable address;
there is no requirement for a mapped byte after this three-byte instruction. -/
theorem relocated_lea32 (memory : Memory) (base : Word)
    (registers : Register → Word) (flags : Word)
    (code : CodeAt memory base [0x8d,0x46,0xff]) :
    Sequential.decodeAt ⟨registers,base,flags,memory⟩ =
      .ok (.lea32 .rax (.baseDisp8 .rsi 0xff) false) := by
  exact decodeAt_transport
    (code_fetch_transport_of_bound code (by decide) 0 (by decide)
      ⟨registers,base,flags,memory⟩ rfl (by simp)) (by decide +kernel)

theorem relocated_test8 (memory : Memory) (base : Word)
    (registers : Register → Word) (flags : Word)
    (code : CodeAt memory base [0x40,0xf6,0xc6,1]) :
    Sequential.decodeAt ⟨registers,base,flags,memory⟩ = .ok (.testImm8 .rsi 1 true) := by
  exact decodeAt_transport
    (code_fetch_transport_of_bound code (by decide) 0 (by decide)
      ⟨registers,base,flags,memory⟩ rfl (by simp)) (by decide +kernel)

/-- The shared 8D opcode still transports the legacy decoder's displacement. -/
theorem relocated_legacy_lea (memory : Memory) (base : Word)
    (registers : Register → Word) (flags : Word)
    (code : CodeAt memory base [0x8d,0x40,0xff]) :
    Sequential.decodeAt ⟨registers,base,flags,memory⟩ =
      .ok (.legacy (.leaEaxRaxDisp8 0xff)) := by
  exact decodeAt_transport
    (code_fetch_transport_of_bound code (by decide) 0 (by decide)
      ⟨registers,base,flags,memory⟩ rfl (by simp)) (by decide +kernel)

private def windowState (bytes : List Byte) (base : Word) : State where
  registers := fun _ => 0
  rip := base
  flags := 0
  memory := {
    read := fun address => bytes[(address - base).toNat]?
    executable := fun address => decide ((address - base).toNat < bytes.length) }

/-- Both complete windows end at the last canonical byte. Their decoder does
not fetch the next address in the hole. Real-index SIB rows isolate absent
base5 rejection from the independent missing-index restriction. -/
theorem exact_boundary_and_absent_base :
    Sequential.decodeAt (windowState [0x8d,0x46,0xff] 0x7ffffffffffd) =
      .ok (.lea32 .rax (.baseDisp8 .rsi 0xff) false) ∧
    Sequential.decodeAt (windowState [0x40,0xf6,0xc6,1] 0x7ffffffffffc) =
      .ok (.testImm8 .rsi 1 true) ∧
    Sequential.decodeAt (windowState [0x8d,0x04,0x0d] 0) = .error .unsupportedEncoding ∧
    Sequential.decodeAt (windowState [0x41,0x8d,0x04,0x0d] 0) = .error .unsupportedEncoding :=
  by
    refine ⟨?_,?_,?_,?_⟩ <;> decide +kernel

/-- Raw RIP arithmetic can wrap. Authenticated code windows independently
reject that extent, so a successful decoder alone is insufficient admission. -/
theorem wrapping_is_not_an_authenticated_window (memory : Memory) :
    Sequential.decodeAt (windowState [0xf6,0xc0,1] 0xffffffffffffffff) =
      .ok (.testImm8 .rax 1 false) ∧
    ¬ CodeAt memory 0xffffffffffffffff [0xf6,0xc0,1] := by
  refine ⟨?_, ?_⟩
  · decide +kernel
  · intro code
    exact (by decide : ¬ ((0xffffffffffffffff : Word).toNat +
    ([0xf6,0xc0,1] : List Byte).length ≤ 2^64)) code.1

end EDSL.Tests.AddressByteTransport
