/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
-- Reusable sequential verification API. No frozen corpus or example imports.
-- EDSL.All explicitly imports the complete historical proof catalogue.
import EDSL.Semantics
import EDSL.X86.VCGen
import EDSL.X86.VCGen.PureCall
import EDSL.X86.VCGen.BufferCall
import EDSL.PureCall.ELFCertificate
import EDSL.ELF.CallerResources.Stack
import EDSL.PureCall.Frame
import EDSL.PureCall.Candidate
import EDSL.X86.Sequential.Low8
import EDSL.X86.Sequential.ByteComparePadding
import EDSL.Grading.ByteEquality
import EDSL.ELF.FunctionCandidateSource
