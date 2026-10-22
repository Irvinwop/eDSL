/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.PlainCall64
import EDSL.Corpus.PlainExecution
import EDSL.Corpus.PlainMixedWitnesses
import EDSL.Audit

/-!
Transitive trust audit and fresh-replay entrypoint for the complete plain64
execution witnesses. The imported certificate inhabitants must retain the
independent overlap, full64 data, actual publication and read-from gates.
This also includes the schedule-independent whole-loaded-image frame.
-/

set_option autoImplicit false

#print axioms EDSL.Corpus.PlainMixedWitnesses.gcc
#print axioms EDSL.Corpus.PlainMixedWitnesses.clang
#print axioms EDSL.Grading.ConcurrentTask.Plain64.ClosedPost.readsFrom_two_workers
#print axioms EDSL.Corpus.Plain.LoadedBatch.retainedImage_after
#audit_edsl
