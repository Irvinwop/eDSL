/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.ExecutionChoices

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.X86.Sequential

/-- Closed selection of the production sequential executors. This is core
infrastructure, not a registry entry or a submission-supplied transition. -/
inductive ExecutionModel where
  | bool
  | flags
  deriving DecidableEq, Repr

/-- One retired instruction's choice domain for the selected executor. -/
def ExecutionModel.Choice : ExecutionModel → Type
  | .bool => Bool
  | .flags => FlagChoices

/-- Both models decode the actual current executable memory. The Bool model
uses the original single-bit executor; the flags model allows independent
undefined flag choices through the complete production executor. -/
def ExecutionModel.transition (model : ExecutionModel) :
    model.Choice → State → Except Error Observation :=
  match model with
  | .bool => step
  | .flags => stepWith

end EDSL.X86.Sequential
