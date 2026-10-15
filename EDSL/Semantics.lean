/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/

namespace EDSL

/-- A model of possible observations. Observation types may include traces,
termination, faults, and divergence. No executable model is supplied here. -/
structure Semantics (Program Input Observation : Type) where
  behaves : Program → Input → Observation → Prop

/-- Every target behavior is allowed by the source on admitted inputs.
This alone proves neither target execution existence nor termination. -/
def Refines
    (source : Semantics S I O) (target : Semantics T I O)
    (sourceProgram : S) (targetProgram : T) (admitted : I → Prop) : Prop :=
  ∀ input, admitted input → ∀ observation,
    target.behaves targetProgram input observation →
    source.behaves sourceProgram input observation

/-- A safety property over all behaviors on admitted inputs. -/
def Satisfies
    (model : Semantics P I O) (program : P)
    (admitted : I → Prop) (specification : I → O → Prop) : Prop :=
  ∀ input, admitted input → ∀ observation,
    model.behaves program input observation → specification input observation

/-- Nonemptiness is a separate obligation, not an implicit refinement premise. -/
def HasBehavior (model : Semantics P I O) (program : P) (admitted : I → Prop) : Prop :=
  ∀ input, admitted input → ∃ observation, model.behaves program input observation

theorem Refines.trans
    {source : Semantics S I O} {middle : Semantics M I O} {target : Semantics T I O}
    {s : S} {m : M} {t : T} {admitted : I → Prop}
    (first : Refines source middle s m admitted)
    (second : Refines middle target m t admitted) :
    Refines source target s t admitted := by
  intro input permitted observation behavior
  exact first input permitted observation (second input permitted observation behavior)

theorem Satisfies.of_refines
    {source : Semantics S I O} {target : Semantics T I O}
    {s : S} {t : T} {admitted : I → Prop} {specification : I → O → Prop}
    (correct : Satisfies source s admitted specification)
    (refinement : Refines source target s t admitted) :
    Satisfies target t admitted specification := by
  intro input permitted observation behavior
  exact correct input permitted observation (refinement input permitted observation behavior)

end EDSL
