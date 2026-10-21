/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Queue.Publication
import EDSL.OS.TSO64.Queue.Sequence
import EDSL.OS.TSO64.Queue.SelectionOrder

/-!
Checked tagged FIFO policy and occurrence accounting for integration with the
existing TSO64 instruction engine. This module provides no second executor and
does not yet extend that engine's managed plain-load/store admission or history.
-/
