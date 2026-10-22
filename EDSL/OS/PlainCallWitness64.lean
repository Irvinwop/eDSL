/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.PlainCallWitness64.Overlap
import EDSL.OS.PlainCallWitness64.Publication
import EDSL.OS.PlainCallWitness64.Mixed
import EDSL.OS.PlainCallWitness64.ReadFrom

/-!
Constructive execution witnesses for the independent managed plain64 contract.
Two original access blocks establish overlap before either RET. A separate
writer-complete, drain, reader schedule establishes delayed publication; actual
history and persistent writer identities determine the reader's source and RF
row. Scheduling evidence and closed outputs are derived from present admission.
The imported contracts retain the model's explicit environmental assumptions.
-/
