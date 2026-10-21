/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ConcurrentTask.Plain64.Claim
import EDSL.OS.PlainCallCompletion64
import EDSL.OS.PlainCallClosed64

/-!
The reusable full registered plain64 contract for every statically checked
catalog. Present-only independent admission supplies resources and inputs;
checked candidate bytes supply shape. All prefix safety, completed behavior,
closed histories, enabledness, chosen completion, real drain closure and the
restricted own-issue bound are derived, without a future-success or graph oracle.

This universal modeled contract still requires useful exact-file resource and
execution inhabitants for a compiler-corpus certificate. Physical/source/OS,
lifecycle and fairness boundaries remain explicit in its component contracts.
-/

set_option autoImplicit false

namespace EDSL.OS.PlainCallClaim64
open X86 TSO64 Grading.ConcurrentTask.Plain64

/-- One reusable proof serves all full64 input words, actual current resources,
valid incoming queues, counters, worker populations and mixed registered sites. -/
theorem claim {catalog : Catalog} (static : PlainCallAdmission64.StaticShapes catalog) :
    Claim catalog where
  prefixes := fun _before _inputs pre _actions _actual success =>
    PlainCallSafety64.safe_prefix static pre success
  completed := fun _before _inputs pre _actions _actual success returned =>
    PlainCallBehavior64.post static pre success returned
  whole := fun _before _inputs pre _actions _actual success finished =>
    PlainCallClosed64.post static pre success finished 0
  enabled := fun _before _inputs pre _actions _actual success =>
    PlainCallProgress64.enabled static pre success
  completion := fun _before _inputs pre _prior _actual success choices =>
    PlainCallCompletion64.completion static pre success choices
  closure := by
    intro before inputs pre actions actual success returned
    obtain ⟨closed, drained, certificate, finished, appended, post, _responses⟩ :=
      PlainCallCompletion64.closure static pre success returned
    refine ⟨closed, drained, certificate, finished, appended, post, ?_⟩
    intro initialEmpty
    exact PlainCallClosed64.post static ⟨pre, initialEmpty⟩ appended finished 0
  bounded := ⟨64, by decide, fun _before _inputs pre _actions _actual success =>
    PlainCallProgress64.bounded static pre success⟩

end EDSL.OS.PlainCallClaim64

#audit_edsl
