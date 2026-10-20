/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.BufferCertificate
import EDSL.Corpus.V1.ByteComparisonBodies
import EDSL.Corpus.V1.ByteComparisonResources

set_option autoImplicit false
set_option warningAsError true

/-! Compose a useful current two-buffer call with the exact complete frozen
function. The fixed task supplies its independent unsigned lexicographic
contract; the compiler-specific proof supplies execution and read authority. -/

namespace EDSL.Corpus.V1.ByteComparisonCertificates
open X86 OS.AddressSpace

abbrev Compiler := ByteComparisonWindows.Compiler

/-- The authenticated complete ELF, original caller and both current input
loans inhabit the same resource world at the actual function entry. -/
def loaded (compiler : Compiler) :
    Buffer.LoadedCall ByteComparisonResources.taskID
      (ByteComparisonWindows.file compiler) ByteComparisonWindows.name
      (ByteComparisonWindows.input compiler) where
  prior := empty
  loaded := ByteComparisonResources.installed compiler
  admitted := ByteComparisonResources.admitted compiler
  resource := (ByteComparisonResources.witness compiler).resource
  initial := (ByteComparisonResources.witness compiler).initial
  useful := (ByteComparisonResources.witness compiler).useful
  pre := (ByteComparisonResources.witness compiler).pre
  entry := (ByteComparisonResources.witness compiler).entry
  text := (ByteComparisonResources.witness compiler).text
  retainedImage := (ByteComparisonResources.witness compiler).retained

/-- Combine the universal fixed task with a useful call and complete file
binding. No candidate-selected specification or desired-result premise enters. -/
def certificate (compiler : Compiler) :
    Buffer.Certificate ByteComparisonResources.taskID
      (ByteComparisonWindows.file compiler) ByteComparisonWindows.name :=
  Buffer.Certificate.ofLoadedCall (ByteComparisonWindows.input compiler)
    (ByteComparisonWindows.checked compiler)
    (ByteComparisonBodies.semantics compiler) (loaded compiler)

#print axioms loaded
#print axioms certificate
end EDSL.Corpus.V1.ByteComparisonCertificates
#audit_edsl
