/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Export.Core
import EDSL.Grading.ByteQuotation
import Lean.Elab.Command

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

-- The producer API must be usable without importing a default controller or
-- its broad model snapshot. Check actual imported modules, not source text.
open Lean in
run_cmd do
  let allowed : Array Name := #[`EDSL.Grading.Export.Core,
    `EDSL.Grading.Export.Preparation, `EDSL.Grading.Runtime.Packet,
    `EDSL.Grading.Runtime.DAG, `EDSL.Grading.Runtime.Codec,
    `EDSL.Grading.Runtime.Types, `EDSL.Grading.Runtime.Audit,
    `EDSL.Grading.ByteQuotation, `EDSL.X86.State]
  for name in (← getEnv).header.moduleNames do
    if (`tests).isPrefixOf name || (`Tools).isPrefixOf name ||
        ((`EDSL).isPrefixOf name && !allowed.contains name) then
      throwError "snapshot-independent export imported {name}"
  logInfo m!"Snapshot-independent exporter imports {(← getEnv).header.moduleNames.filter (fun n => (`EDSL).isPrefixOf n) |>.size} project modules"
