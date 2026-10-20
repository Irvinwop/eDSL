/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64
import tests.TSO64Interleaving
import tests.TSO64Forwarding
import tests.TSO64CurrentRAM
import tests.TSO64Denials
import EDSL.Audit

#audit_edsl
#print axioms EDSL.OS.TSO64.StoreGate.enabled
#print axioms EDSL.OS.TSO64.step_origin
#print axioms EDSL.OS.TSO64.locked_coupled
#print axioms EDSL.OS.TSO64.step_wellFormed
#print axioms EDSL.OS.TSO64.schedule_wellFormed
#print axioms EDSL.OS.TSO64.step_peer
#print axioms EDSL.OS.TSO64.step_resources
#print axioms EDSL.OS.TSO64.step_stable
#print axioms EDSL.OS.TSO64.step_code
#print axioms EDSL.OS.TSO64.step_loan_contents
#print axioms EDSL.OS.TSO64.schedule_loan_contents
#print axioms EDSL.OS.TSO64.local_original_caller
#print axioms EDSL.OS.TSO64.OrdinaryEffect.accesses
#print axioms EDSL.OS.TSO64.fetchCPU_fetch
#print axioms EDSL.OS.TSO64.drain_fifo
#print axioms EDSL.OS.TSO64.drain_mixed
#print axioms EDSL.OS.TSO64.blocked_unchanged
#print axioms EDSL.OS.TSO64.publish_worker
#print axioms EDSL.OS.TSO64.attach_valid
#print axioms EDSL.OS.TSO64.collect_ready

/-- Record the actual compiler environment's transitive import closure for
the ignored receipt's source/object seals. This emits no proof assertion. -/
elab "#tso64_dependencies" : command => do
  for imported in (← Lean.getEnv).header.modules do
    Lean.logInfo m!"TSO64_IMPORT {imported.module}"

#tso64_dependencies
