/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.StoreReturnValue64.Resources

set_option warningAsError true

namespace EDSL.CountedStore64
open EDSL X86 X86.Sequential OS

/-- Mathematical callable arguments, including the complete 64-bit count.
This contract does not select instructions or require a particular loop. -/
structure Input extends StoreLoad64.Input where
  count : Word

/-- Present machine facts only. RSI supplies the initial value, RDX the full
count, and RDI the target address. No decoder, future step or rank
certificate is part of admission. -/
structure Pre (bytes : List Byte) (input : Input) (initial : State) : Prop where
  memory : StoreLoad64.Pre bytes input.toInput initial
  count : initial.registers .rdx = input.count

/-- Zero iterations preserve the old target; positive counts publish the
modular value. This is a result specification, not source/volatile preservation. -/
def expectedValue (input : Input) : Word :=
  if input.count = 0 then input.oldValue else input.argument + input.count

def Useful (input : Input) : Prop := input.oldValue ≠ expectedValue input

/-- Independent value, complete target/permission/ABI frames and actual caller
return. Exact costs and intermediate store counts are separate obligations. -/
structure Post (input : Input) (initial final : State) : Prop where
  result : final.registers .rax = input.argument + input.count
  value : loadQWord final.memory input.address = .ok (expectedValue input)
  outside : ∀ query, 8 ≤ (query - input.address).toNat →
    final.memory.read query = initial.memory.read query
  writable : final.memory.writable = initial.memory.writable
  executable : final.memory.executable = initial.memory.executable
  returnAddress : final.rip = input.returnAddress
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register ∈ StoreLoad64.calleeSaved,
    final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

/-- The current owned allocation and original live loans use the same existing
world representation; the count is immutable call data. -/
structure Resources where
  memory : StoreLoad64.Resources
  count : Word

def resourceInput (resource : Resources) : Input :=
  ⟨StoreLoad64.resourceInput resource.memory, resource.count⟩

structure ResourcePre (bytes : List Byte) (resource : Resources) (initial : State) : Prop where
  memory : StoreLoad64.ResourcePre bytes resource.memory initial
  count : initial.registers .rdx = resource.count

theorem ResourcePre.machine {bytes resource initial}
    (pre : ResourcePre bytes resource initial) : Pre bytes (resourceInput resource) initial :=
  ⟨pre.memory.machine, pre.count⟩

/-- Ordinary contained writes and real current loan/target reads retain their
actual widths. Existing registration rules exclude atomic/syscall authority. -/
def RawPolicy (bytes : List Byte) (input : Input) (initial : State) : Prop :=
  Grading.StoreReturnValue64.RawPolicy bytes input.toInput initial

def ResourcePolicy (resource : Resources) (initial : State) : Prop :=
  Grading.StoreReturnValue64.ResourcePolicy resource.memory initial

/-- The return obligation retains the same lifted execution, current RAM and
owner/epoch/loan/outside frames, plus another arbitrary checked64 store. -/
def ResourceReturn (resource : Resources) (initial : State) (result : Result) : Prop :=
  Grading.StoreReturnValue64.ResourceReturn resource.memory initial result

end EDSL.CountedStore64
