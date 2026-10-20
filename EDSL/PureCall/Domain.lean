/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallResources.Domain
import EDSL.PureCall.Resources

namespace EDSL.PureCall.Domain
open X86 OS

/-- Realize a present argument, preserving the declared low32 information.
Unbound registers receive zero; the mathematical domain remains independent. -/
def argumentValue : Option Argument → Word
  | none => 0
  | some (.word64 value) => value
  | some (.low32 value) => value.setWidth 64

theorem argumentValue_holds (argument : Argument) :
    argument.Holds (argumentValue (some argument)) := by
  cases argument with
  | word64 value => rfl
  | low32 value =>
    change (value.setWidth 64).setWidth 32 = value
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
    exact BitVec.setWidth_eq value

/-- Construct the six declared integer argument registers. The existing
domain constructor separately installs the original caller stack pointer. -/
def registers (spec : Spec) (value : spec.Input) : Register → Word
  | .rdi => argumentValue (spec.arguments value 0)
  | .rsi => argumentValue (spec.arguments value 1)
  | .rdx => argumentValue (spec.arguments value 2)
  | .rcx => argumentValue (spec.arguments value 3)
  | .r8 => argumentValue (spec.arguments value 4)
  | .r9 => argumentValue (spec.arguments value 5)
  | _ => 0

def initial (environment : CallResources.Domain.Initial) (spec : Spec)
    (value : spec.Input) : State :=
  CallResources.Domain.machine environment (registers spec value) 0x202

theorem initial_arguments (environment : CallResources.Domain.Initial)
    (spec : Spec) (value : spec.Input) :
    Bound spec value (initial environment spec value) := by
  intro ⟨index, bound⟩ argument supplied
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 := by
    omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change argument.Holds (argumentValue (spec.arguments value _))
    have normalized := argumentValue_holds argument
    rw [← supplied] at normalized
    exact normalized

def resource (environment : CallResources.Domain.Initial) (spec : Spec)
    (value : spec.Input) : Resources spec :=
  ⟨CallResources.Domain.shared environment, CallResources.Domain.call environment, value⟩

theorem resource_pre {environment : CallResources.Domain.Initial}
    (facts : CallResources.Domain.Facts environment) (spec : Spec)
    (value : spec.Input) {bytes : List Byte} (source : environment.bytes = bytes)
    (domain : spec.domain value) :
    ResourcePre spec bytes (resource environment spec value)
      (initial environment spec value) := by
  exact ⟨CallResources.Domain.current facts _ _, source, rfl, rfl, domain,
    initial_arguments environment spec value⟩

end EDSL.PureCall.Domain
