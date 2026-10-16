/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Write32.Contract

set_option warningAsError true

namespace EDSL.StoreReturn32
open X86

/-- Independent low32 store, complete RAM/permission and ABI frame, caller
return, and full-width returned pointer. The void write32 contract by itself
does not require this RAX value. -/
structure Post (input : Grading.Write32.Input) (initial final : State) : Prop
    extends Grading.Write32.Post input initial final where
  pointer : final.registers .rax = input.address

end EDSL.StoreReturn32
