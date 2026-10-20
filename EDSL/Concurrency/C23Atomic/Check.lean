/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Concurrency.C23Atomic.Check.Propose

/-!
Sound finite admission for the supplied atomic-event fragment. Tables and a
happens-before certificate are untrusted data; `check_sound` derives `Legal`
from a successful computation. This checks graph consistency, not program or
machine origins. Failure can mean an invalid graph or insufficient certificate.
-/
