/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.BufferCertificate
import EDSL.Corpus.V1.ByteEqualityBodies
import EDSL.Corpus.V1.ByteEqualityResources

set_option autoImplicit false
set_option warningAsError true

/-! The fixed Boolean task, complete named ELF and useful current resources
compose with the independent universal body proof. -/

namespace EDSL.Corpus.V1.ByteEqualityCertificates
open X86 OS.AddressSpace

abbrev Compiler := ByteEqualityWindows.Compiler

def loaded (compiler : Compiler) :
    Buffer.LoadedCall .equalBytes (ByteEqualityWindows.file compiler) ByteEqualityWindows.name
      (ByteEqualityWindows.input compiler) (ByteEqualityWindows.maxBytes compiler) where
  prior := empty
  loaded := ByteEqualityResources.installed compiler
  admitted := ByteEqualityResources.admitted compiler
  resource := ByteEqualityResources.resources compiler
  initial := ByteEqualityResources.machine compiler (fun _ => 0) 0x202
  useful := ByteEqualityResources.useful compiler
  pre := ByteEqualityResources.pre compiler (fun _ => 0) 0x202
  entry := rfl
  text := ByteEqualityResources.text compiler
  retainedImage := fun _ _ present => ByteEqualityResources.installed_frame compiler present

/-- The complete Clang extent retains its explicit bound; no prefix or source
language assertion replaces either compiler's checked final bytes. -/
def certificate (compiler : Compiler) :
    Buffer.Certificate .equalBytes (ByteEqualityWindows.file compiler) ByteEqualityWindows.name
      (ByteEqualityWindows.maxBytes compiler) :=
  Buffer.Certificate.ofLoadedCallWith (ByteEqualityWindows.maxBytes compiler)
    (ByteEqualityWindows.input compiler) (ByteEqualityWindows.checked compiler)
    (ByteEqualityBodies.semantics compiler) (loaded compiler)

#print axioms loaded
#print axioms certificate
end EDSL.Corpus.V1.ByteEqualityCertificates
#audit_edsl
