/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.AtomicMethods

set_option warningAsError true

namespace EDSL.Tests.AtomicMethods
open X86 X86.VCGen.AtomicMethods

/- Independent encoding mutations: each defect changes the claimed function's
behavior, atomic width, or complete extent. These check the fail-closed static
certificate boundary, without asserting an assigned fixture result or mocking
the current decoder. Universal dynamic behavior is proved in AtomicMethods. -/

-- Copying RDI into RAX cannot implement entry RSI flow, even if LOCK/RET match.
example : check [0x48,0x89,0xf8,0xf0,0x48,0x0f,0xc1,0x07,0xc3]
    .rsi LockedAdd64.frozen [] = false := by decide +kernel

-- A 32-bit copy loses high argument bits and is not the full-width body.
example : check [0x89,0xf0,0xf0,0x48,0x0f,0xc1,0x07,0xc3]
    .rsi LockedAdd64.frozen [] = false := by decide +kernel

-- Dropping LOCK must not be accepted as an indivisible RMW.
example : check [0x48,0x89,0xf0,0x48,0x0f,0xc1,0x07,0xc3]
    .rsi LockedAdd64.frozen [] = false := by decide +kernel

-- A non-W REX does not promise qword arithmetic.
example : check [0x48,0x89,0xf0,0xf0,0x40,0x0f,0xc1,0x07,0xc3]
    .rsi LockedAdd64.frozen [] = false := by decide +kernel

-- The register source of the RMW must be the destination of the copy.
example : check [0x48,0x89,0xf0,0xf0,0x48,0x0f,0xc1,0x0f,0xc3]
    .rsi LockedAdd64.frozen [] = false := by decide +kernel

-- A matching sequence inside a larger window cannot silently ignore a suffix.
example : check [0x48,0x89,0xf0,0xf0,0x48,0x0f,0xc1,0x07,0xc3,0x90]
    .rsi LockedAdd64.frozen [] = false := by decide +kernel

-- A missing ENDBR64 cannot satisfy the admitted padding map.
example : check [0x48,0x89,0xf0,0xf0,0x48,0x0f,0xc1,0x07,0xc3]
    .rsi LockedAdd64.frozen [.endbr64] = false := by decide +kernel

-- Falling through NOP is not a return, regardless of correct RMW bytes.
example : check [0x48,0x89,0xf0,0xf0,0x48,0x0f,0xc1,0x07,0x90]
    .rsi LockedAdd64.frozen [] = false := by decide +kernel

-- Argument mismatches remain rejected even when the same frozen instruction
-- bytes are supplied. This distinguishes the caller's input register contract.
example : check [0x48,0x89,0xf0,0xf0,0x48,0x0f,0xc1,0x07,0xc3]
    .rdx LockedAdd64.frozen [] = false := by decide +kernel

end EDSL.Tests.AtomicMethods

#audit_edsl
