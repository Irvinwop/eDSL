/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.WriteMoves
import EDSL.Audit

set_option warningAsError true

#print axioms EDSL.WriteMovesSupported.claim
#print axioms EDSL.WriteMovesSupported.modeled_accounting
#audit_edsl
