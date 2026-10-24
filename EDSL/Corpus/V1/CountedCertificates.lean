/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.CountedCertificates.Inputs
import EDSL.Corpus.V1.CountedCertificates.Overlap

/-!
Exact complete-file counted-call certificates for the frozen GCC and Clang
counter workers. The generic contract lives in `EDSL.Corpus.CountedCertificate`;
`Inputs` supplies loaded resource admission and `Overlap` constructs completed
interleavings. Import this facade to use `CountedCertificates.gcc` and `.clang`.
-/
