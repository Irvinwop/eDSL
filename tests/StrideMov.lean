/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.StrideMov
import EDSL.Audit

-- Audit the compiled client proof separately from its elaboration environment.
-- The packet tests independently replay it in the grader's fixed snapshot.
#audit_edsl
