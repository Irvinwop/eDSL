/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.CallReturn.DecodeTransport
import EDSL.X86.CallReturn.Execution

/-!
Additive direct E8 CALL, register PUSH/POP and REX.W mod=01 LEA, with an
explicit original-stack-slot return boundary. Ordinary RAM; four-level
canonical addresses; AC/CET disabled; no asynchronous/control-state or physical
fault-delivery refinement. The abstract CALL error order is target canonicality,
then complete checked stack store. Execution permission is checked at fetch.

Raw RET reads current RAM. The driver has no trusted ghost call stack or target
range heuristic. No ownership, balanced-stack, ABI, compiler, concurrent-profile
or whole-OS claim follows from importing this module. Existing decoders, CFGs,
graders and ordinary store-intent theorems remain separate.
-/
