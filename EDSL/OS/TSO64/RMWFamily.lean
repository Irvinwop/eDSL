/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Resources.Core
import EDSL.OS.AddRMWMachine64

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.OS.TSO64
open X86

/-- Instruction admission is independent of the ordinary-memory authority
profile. The default retains the original XADD decoder and its error boundary. -/
inductive RMWFamily where
  | xaddOnly
  | arithmetic
  deriving DecidableEq, Repr

namespace RMWFamily

def Instruction : RMWFamily → Type
  | .xaddOnly => LockedAdd64.Instruction
  | .arithmetic => AddRMW64.Instruction

instance (family : RMWFamily) : DecidableEq family.Instruction := by
  cases family with
  | xaddOnly => exact inferInstanceAs (DecidableEq LockedAdd64.Instruction)
  | arithmetic => exact inferInstanceAs (DecidableEq AddRMW64.Instruction)

/-- Uniform prestate base, length, delta and optional old-value destination. -/
def embed : (family : RMWFamily) → family.Instruction → AddRMW64.Instruction
  | .xaddOnly, instruction => .xadd instruction
  | .arithmetic, instruction => instruction

/-- Select the original decoder directly for the default family. Successful
tagged decoding agrees with AddRMW64; decoder failures need not agree. -/
def decodeAt : (family : RMWFamily) → X86.State → Except X86.Error family.Instruction
  | .xaddOnly, initial => LockedAdd64.decodeAt initial
  | .arithmetic, initial => AddRMW64.decodeAt initial

def stepCPU (family : RMWFamily) : X86.State → Except X86.Error AddRMW64.Observation :=
  match family with
  | .xaddOnly => LockedAdd64.step
  | .arithmetic => AddRMW64.step

/-- The default effect reduces to the entire legacy source/writeback contract.
The arithmetic family instead records the actual instruction's optional
destination; neither family changes OS authority or the checked primitive. -/
def MachineEffect (family : RMWFamily) (before : World) (actor : Nat)
    (identifier : Atomics64.HandleId64) (initial : X86.State) :
    family.Instruction → (World × Atomics64.FetchAddEvent) → AddRMW64.Observation → Prop :=
  match family with
  | .xaddOnly => Atomics64.FetchAddMachineEffect before actor identifier initial
  | .arithmetic => Atomics64.AddRMWMachineEffect before actor identifier initial

theorem decodeAt_embed {family : RMWFamily} {initial : X86.State}
    {instruction : family.Instruction}
    (decoded : family.decodeAt initial = .ok instruction) :
    AddRMW64.decodeAt initial = .ok (family.embed instruction) := by
  cases family with
  | xaddOnly => exact (AddRMW64.decodeAt_xadd_iff initial instruction).mpr decoded
  | arithmetic => exact decoded

/-- Only successful current decoding is needed; operand execution can fail. -/
theorem stepCPU_eq_arithmetic {family : RMWFamily} {initial : X86.State}
    {instruction : family.Instruction}
    (decoded : family.decodeAt initial = .ok instruction) :
    family.stepCPU initial = AddRMW64.step initial := by
  cases family with
  | xaddOnly => exact (AddRMW64.step_xadd decoded).symm
  | arithmetic => rfl

theorem machineEffect_iff_arithmetic {family : RMWFamily} {before : World}
    {actor : Nat} {identifier : Atomics64.HandleId64} {initial : X86.State}
    {instruction : family.Instruction} {result : World × Atomics64.FetchAddEvent}
    {machine : AddRMW64.Observation} :
    family.MachineEffect before actor identifier initial instruction result machine ↔
      Atomics64.AddRMWMachineEffect before actor identifier initial
        (family.embed instruction) result machine := by
  cases family with
  | xaddOnly => exact Atomics64.AddRMWMachineEffect.xadd_iff.symm
  | arithmetic => exact Iff.rfl

theorem MachineEffect.arithmetic {family : RMWFamily} {before : World}
    {actor : Nat} {identifier : Atomics64.HandleId64} {initial : X86.State}
    {instruction : family.Instruction} {result : World × Atomics64.FetchAddEvent}
    {machine : AddRMW64.Observation}
    (effect : family.MachineEffect before actor identifier initial instruction result machine) :
    Atomics64.AddRMWMachineEffect before actor identifier initial
      (family.embed instruction) result machine :=
  (machineEffect_iff_arithmetic (family := family)).mp effect

end RMWFamily
end EDSL.OS.TSO64
