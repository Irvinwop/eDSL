/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Domain
import EDSL.CallStack.Coverage
import tests.fixtures.CallStack.CPUFixture
import EDSL.Audit

set_option warningAsError true

#print axioms EDSL.CallStack.Domain.allocated
#print axioms EDSL.CallStack.Domain.loan_cells_preserved
#print axioms EDSL.CallStack.Domain.private_writable
#print axioms EDSL.CallStack.Domain.contract
#print axioms EDSL.CallStack.Domain.resource_pre
#print axioms EDSL.CallStack.Domain.raw_pre
#print axioms EDSL.CallStack.Domain.nonvacuous
#print axioms EDSL.CallStack.Domain.unsupported_admitted
#print axioms EDSL.CallStack.FetchWithin.decoded
#print axioms EDSL.CallStack.FetchWithin.length_le
#print axioms EDSL.CallStack.FetchWithin.entry
#print axioms EDSL.CallStack.FetchWithin.atOffset_iff
#print axioms EDSL.CallStack.CoveredExecution.execution
#print axioms EDSL.CallStack.CoveredExecution.machine
#print axioms EDSL.CallStack.CoveredExecution.privateHistory
#print axioms EDSL.CallStack.CoveredExecution.current
#print axioms EDSL.CallStack.CoveredExecution.preserves
#print axioms EDSL.CallStack.CoveredExecution.memory_frame
#print axioms EDSL.CallStack.CoveredExecution.fetchWithin
#print axioms EDSL.CallStack.CoveredExecution.prefix
#print axioms EDSL.CallStack.CoveredExecution.of_execution
#print axioms EDSL.CallStack.CoveredExecution.read_origin
#print axioms EDSL.CallStack.CoveredExecution.terminal_origin
#print axioms EDSL.Tests.StackFrameCPU.complete
#audit_edsl
