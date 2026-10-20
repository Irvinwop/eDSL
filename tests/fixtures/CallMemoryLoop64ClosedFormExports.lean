/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.ClosedForm

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.ClosedForm.Exported

/-- Closed names for the client exporter. Neither alias enters the fixed
trusted installation; the submitted proof data reconstructs the client. -/
theorem gcc : EDSL.CallMemoryLoop64.Claim (program .gcc) := claim .gcc

theorem clang : EDSL.CallMemoryLoop64.Claim (program .clang) := claim .clang

end EDSL.CallMemoryLoop64.ClosedForm.Exported
