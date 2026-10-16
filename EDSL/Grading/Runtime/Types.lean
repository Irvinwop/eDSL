/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Lean.Environment
import Lean.Data.Json

/-! Runtime admission and checking data. These are controller definitions, not task
correctness claims. The caller supplies a pinned, trusted checked environment. -/
namespace EDSLGrader.Runtime

open Lean

structure Limits where
  maxInputBytes : Nat := 4194304
  maxJsonDepth : Nat := 192
  maxExprDepth : Nat := 128
  maxNodes : Nat := 200000
  maxNameParts : Nat := 64
  maxStringBytes : Nat := 4096
  maxDecimalChars : Nat := 128
  maxDeclarations : Nat := 256
  maxAuditSteps : Nat := 100000
  kernelHeartbeats : USize := 10000000
  kernelRecDepth : USize := 512

inductive FailureKind where
  | malformed | unsupported | rejected | audit | resource | internal
  deriving BEq, Repr, Inhabited

structure Failure where
  kind : FailureKind
  message : String
  deriving Repr, Inhabited

instance : ToString Failure where
  toString f := s!"{repr f.kind}: {f.message}"

structure Checked where
  /-- Checked auxiliary environment. The final scratch certification is discarded. -/
  env : Kernel.Environment
  value : Expr
  /-- Number of auxiliary declaration entries, not number of generated constants. -/
  declarations : Nat
  constants : Nat
  decoderSteps : Nat
  auditSteps : Nat
  kernelChecks : Nat

def certificationPrefix : Name := `EDSLGrader.Internal

def fail (kind : FailureKind) (message : String) : Except Failure α :=
  .error { kind, message }

end EDSLGrader.Runtime
