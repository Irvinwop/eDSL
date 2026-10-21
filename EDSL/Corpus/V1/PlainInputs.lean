/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.PlainInput
import EDSL.Corpus.V1.PlainWindows
import EDSL.OS.PlainCallAdmission64

/-!
Register the two unchanged plain-call symbol extents in each frozen final ELF
with the independent load/store input catalog. File/name/extent checks and
static decoder shapes are reused, including GCC's actual ENDBR64/CET-off gate.
There are four function artifacts across two files. No behavioral/resource
inhabitant or corpus credit is established by these input bindings alone.
-/

set_option autoImplicit false

namespace EDSL.Corpus.V1.PlainInputs
open X86 Grading.ConcurrentTask.Plain64

abbrev Compiler := PlainWindows.Compiler

def windowKind : Kind → PlainWindows.Kind
  | .loadAcquire => .loadAcquire
  | .storeRelease => .storeRelease

def named (compiler : Compiler) (kind : Kind) : Plain.NamedImage (PlainWindows.file compiler) where
  kind := kind
  input := PlainWindows.input compiler (windowKind kind)
  checked := by
    cases kind <;> exact PlainWindows.checked compiler _

def site (compiler : Compiler) (kind : Kind) : Site := (named compiler kind).site

def images (compiler : Compiler) : List (Plain.NamedImage (PlainWindows.file compiler)) :=
  [named compiler .loadAcquire, named compiler .storeRelease]

def catalog (compiler : Compiler) : Catalog :=
  [site compiler .loadAcquire, site compiler .storeRelease]

theorem images_catalog (compiler : Compiler) :
    (images compiler).map Plain.NamedImage.site = catalog compiler := rfl

/-- The same checked static shape serves arbitrary full64 values and resources.
No new per-compiler execution proof or changed compiler option is required. -/
def staticShapes (compiler : Compiler) : OS.PlainCallAdmission64.StaticShapes (catalog compiler) where
  padding _ := PlainWindows.padding compiler
  checked := by
    intro selected member
    have alternatives : selected = site compiler .loadAcquire ∨
        selected = site compiler .storeRelease := by
      simpa only [catalog, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using member
    rcases alternatives with rfl | rfl
    · exact PlainWindows.shape_checked compiler .loadAcquire
    · exact PlainWindows.shape_checked compiler .storeRelease

end EDSL.Corpus.V1.PlainInputs

#audit_edsl
