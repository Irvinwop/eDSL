/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Profiled
import EDSL.ELF.CallerResources.Stack
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.ProfiledNamedELF
open X86 X86.Sequential OS.AddressSpace
open GeneratedCFG.Profiled

-- The assembler/linker output and importer must agree with this independently
-- stated instruction contract, including text beyond the first return.
theorem exactText : observedBytes =
    [0xb8, 42, 0, 0, 0, 0xc3] ++
      (List.replicate 30 [0x66, 0x90]).flatten ++ [0x90, 0xc3] := by decide +kernel

example : ELF.FunctionCandidate.Binding observedInput observedELF
    [112, 114, 111, 102, 105, 108, 101, 100] 68 := binding
example : CFG.Valid observedBytes observedGraph ⟨68, 40, by decide⟩ := valid
example : observedInput.check observedELF observedName = false := by decide +kernel
example : CFG.checkWith ⟨68, 32, by decide⟩ observedBytes observedGraph = false := by decide +kernel

def initial : State where
  registers register := if register = .rsp then 0x8000 else 0
  rip := observedInput.function.window.base
  flags := 0x202
  memory := toMemory (ELF.install observedELF observedInput.table.image
    (ELF.CallerResources.Stack.prior 0x8000 0x2000))

def observed : Option (Word × Word × Word × Nat) := do
  let result ← (Sequential.run (fun _ => false) 2 initial).toOption
  return (result.state.registers .rax, result.state.rip,
    result.state.registers .rsp, result.instructions)

/-- A concrete modeled loaded call satisfies an independent return contract.
This establishes neither native execution nor a universal resource contract. -/
theorem returns42 : observed = some (42, 0x2000, 0x8008, 2) := by decide +kernel

end EDSL.Tests.ProfiledNamedELF

#print axioms EDSL.Tests.ProfiledNamedELF.exactText
#print axioms EDSL.Tests.ProfiledNamedELF.returns42
#audit_edsl
