/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.PublishedOrder
import tests.PlainCallBatch

/-!
Published-position views on an admitted six-action execution. The peer's store
is issued at action 0 and published at action 2; the reader's later ordinary
drain is outside the managed-cell writer map. Offset 37 retains every action,
so that publication's stamp is 39 and its position view is 40. The literal
trajectory distinguishes publication from issue and filtered event indices.

These observations concern published metadata. They do not establish a
pending-own view, release transfer, C23 legality, or native correspondence.
-/

set_option autoImplicit false

namespace EDSL.Tests.PublishedPositionViews
open OS.TSO64

private def target : OS.Atomics64.CellId64 :=
  PlainCallBatch.peerReference.handle.cell

/-- The view is absent through the store and load; the managed drain changes
it once. Both RETs and the final ordinary drain retain the same full stamp. -/
theorem actual_prefix_views :
    (List.range 7).map (fun count =>
      PublishedOrder.view
        (PublishedHistory.after 37 (PlainCallBatch.result.2.take count) PublishedHistory.empty)
        target) = [0, 0, 0, 40, 40, 40, 40] := by
  decide +kernel

/-- Instantiation of the general theorem on the actual successful run,
including prefix indices beyond its length. No chosen view trajectory is a
premise of the theorem. -/
theorem every_prefix_order {first last : Nat} (ordered : first ≤ last) :
    PublishedOrder.view
        (PublishedHistory.after 37 (PlainCallBatch.result.2.take first) PublishedHistory.empty)
        target ≤
      PublishedOrder.view
        (PublishedHistory.after 37 (PlainCallBatch.result.2.take last) PublishedHistory.empty)
        target :=
  PublishedOrder.prefix_view (PublishedOrder.prior_empty 37) ordered target

end EDSL.Tests.PublishedPositionViews

#print axioms EDSL.Tests.PublishedPositionViews.actual_prefix_views
#print axioms EDSL.Tests.PublishedPositionViews.every_prefix_order
#audit_edsl
