/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.BufferCertificate
import EDSL.Corpus.V1.ByteScanBodies
import EDSL.Corpus.V1.ByteScanResources

set_option autoImplicit false
set_option warningAsError true

/-! Exact frozen-file certificates for the independent bounded-NUL task.
Universal generated body proofs and useful current loaded resources are
separate evidence, composed through the fixed buffer certificate API. -/

namespace EDSL.Corpus.V1.ByteScanCertificates
open X86 OS.AddressSpace

abbrev Compiler := ByteScanWindows.Compiler

/-- The complete installed ELF, current input/caller/code loans and useful
snapshot all belong to the same actual selected function entry. -/
def loaded (compiler : Compiler) : Buffer.LoadedCall .firstBoundedNulLength
    (ByteScanWindows.file compiler) ByteScanWindows.name (ByteScanWindows.input compiler) where
  prior := empty
  loaded := ByteScanResources.installed compiler
  admitted := ByteScanResources.admitted compiler
  resource := ByteScanResources.resources compiler
  initial := ByteScanResources.machine compiler (fun _ => 0) 0x202
  useful := ByteScanResources.useful
  pre := ByteScanResources.pre compiler (fun _ => 0) 0x202
  entry := rfl
  text := ByteScanResources.text compiler
  retainedImage := fun _ _ present => ByteScanResources.installed_frame compiler present

/-- The trusted task fixes the mathematics and permitted resource behavior;
no candidate-selected specification or future-run admission is added. -/
def certificate (compiler : Compiler) : Buffer.Certificate .firstBoundedNulLength
    (ByteScanWindows.file compiler) ByteScanWindows.name :=
  Buffer.Certificate.ofLoadedCall (ByteScanWindows.input compiler)
    (ByteScanWindows.checked compiler) (ByteScanBodies.semantics compiler) (loaded compiler)

#print axioms loaded
#print axioms certificate

end EDSL.Corpus.V1.ByteScanCertificates
#audit_edsl
