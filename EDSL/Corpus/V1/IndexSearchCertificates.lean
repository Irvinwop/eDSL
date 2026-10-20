/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.BufferCertificate
import EDSL.Corpus.V1.IndexSearchBodies
import EDSL.Corpus.V1.IndexSearchResources

set_option autoImplicit false
set_option warningAsError true

/-! Compose useful current calls with the exact authenticated search files.
The fixed task determines the independent mathematics and resource contract. -/

namespace EDSL.Corpus.V1.IndexSearchCertificates
open X86 OS.AddressSpace

abbrev Compiler := IndexSearchWindows.Compiler
abbrev Operation := IndexSearchWindows.Operation

/-- The complete installed image, actual function entry and useful input share
one current resource world, including the original private caller loan. -/
def loaded (compiler : Compiler) (operation : Operation) :
    Buffer.LoadedCall (IndexSearchResources.taskID operation)
      (IndexSearchWindows.file compiler) (IndexSearchWindows.name operation)
      (IndexSearchWindows.input compiler operation) where
  prior := empty
  loaded := IndexSearchResources.installed compiler operation
  admitted := IndexSearchResources.admitted compiler operation
  resource := (IndexSearchResources.witness compiler operation).resource
  initial := (IndexSearchResources.witness compiler operation).initial
  useful := (IndexSearchResources.witness compiler operation).useful
  pre := (IndexSearchResources.witness compiler operation).pre
  entry := (IndexSearchResources.witness compiler operation).entry
  text := (IndexSearchResources.witness compiler operation).text
  retainedImage := (IndexSearchResources.witness compiler operation).retained

/-- Combine the universal fixed task with a useful call at the exact selected
file entry, retaining the entire installed image and current authority. -/
def certificate (compiler : Compiler) (operation : Operation) :
    Buffer.Certificate (IndexSearchResources.taskID operation)
      (IndexSearchWindows.file compiler) (IndexSearchWindows.name operation) :=
  Buffer.Certificate.ofLoadedCall (IndexSearchWindows.input compiler operation)
    (IndexSearchWindows.checked compiler operation)
    (IndexSearchBodies.semantics compiler operation) (loaded compiler operation)

#print axioms loaded
#print axioms certificate
end EDSL.Corpus.V1.IndexSearchCertificates
#audit_edsl
