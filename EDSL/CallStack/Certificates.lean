/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Coverage
import EDSL.X86.CallReturn.DecodeTransport

set_option warningAsError true

namespace EDSL.CallStack.Certificates
open X86 OS

/-- Transport a successful static decode of arbitrary exact code to the
current coupled machine state, retaining the full instruction-length bound.
The transport currently supports windows of at most 64 bytes. All code,
offsets, instructions and decoding evidence are caller arguments. -/
theorem fetchWithin_of_code {frame : StackFrame.Descriptor} {state : State}
    {offset : Nat} {instruction : CallReturn.Instruction}
    (code : CodeAt state.memory frame.call.code frame.call.bytes)
    (extent : frame.call.bytes.length ≤ 64)
    (inside : offset < frame.call.bytes.length)
    (pc : state.rip = frame.call.code + BitVec.ofNat 64 offset)
    (decoded : CallReturn.decodeAt (Sequential.codeState frame.call.bytes offset) =
      .ok instruction)
    (bound : offset + instruction.length ≤ frame.call.bytes.length) :
    FetchWithin frame state :=
  ⟨offset, instruction, pc,
    CallReturn.decodeAt_code code extent inside state rfl pc decoded, bound⟩

end EDSL.CallStack.Certificates
