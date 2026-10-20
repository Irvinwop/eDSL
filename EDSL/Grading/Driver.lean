/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL
import EDSL.Grading.Artifact
import EDSL.Grading.CallStack.Artifact
import EDSL.Grading.CallMemory64.Artifact
import EDSL.Grading.CallMemoryLoop64.Artifact
import EDSL.Grading.AtomicLogical64.Artifact
import EDSL.Grading.AtomicSet64.Artifact
import EDSL.Grading.Known
import EDSL.Grading.Runtime.Checker
import Lean

/-! Trusted CLI controller. This module does not advertise a formal theorem
about its IO implementation. Mathematical claims live in EDSL.Grading. -/
namespace EDSLGrader
open Lean EDSL EDSL.Grading EDSLGrader.Runtime

def taskID : String → Option TaskID
  | "pair32" => some .pair32
  | "stride32" => some .stride32
  | "write32" => some .write32
  | "storeReturn32" => some .storeReturn32
  | "storeReturnValue64" => some .storeReturnValue64
  | "countedStore64" => some .countedStore64
  | "maximum64" => some .maximum64
  | "minimum64" => some .minimum64
  | "signedMaximum64" => some .signedMaximum64
  | "arrayMaximum64" => some .arrayMaximum64
  | "arraySum64" => some .arraySum64
  | "intersection64" => some .intersection64
  | "union64" => some .union64
  | "symmetricDifference64" => some .symmetricDifference64
  | "addModulo64" => some .addModulo64
  | "clampSigned32" => some .clampSigned32
  | "absSigned32" => some .absSigned32
  | "byteSwap64" => some .byteSwap64
  | "populationCount64" => some .populationCount64
  | "average64" => some .average64
  | "parity64" => some .parity64
  | "rotateLeft64" => some .rotateLeft64
  | _ => none

def taskExpr : TaskID → Expr
  | .pair32 => mkConst ``TaskID.pair32
  | .stride32 => mkConst ``TaskID.stride32
  | .write32 => mkConst ``TaskID.write32
  | .storeReturn32 => mkConst ``TaskID.storeReturn32
  | .storeReturnValue64 => mkConst ``TaskID.storeReturnValue64
  | .countedStore64 => mkConst ``TaskID.countedStore64
  | .maximum64 => mkConst ``TaskID.maximum64
  | .minimum64 => mkConst ``TaskID.minimum64
  | .signedMaximum64 => mkConst ``TaskID.signedMaximum64
  | .arrayMaximum64 => mkConst ``TaskID.arrayMaximum64
  | .arraySum64 => mkConst ``TaskID.arraySum64
  | .intersection64 => mkConst ``TaskID.intersection64
  | .union64 => mkConst ``TaskID.union64
  | .symmetricDifference64 => mkConst ``TaskID.symmetricDifference64
  | .addModulo64 => mkConst ``TaskID.addModulo64
  | .clampSigned32 => mkConst ``TaskID.clampSigned32
  | .absSigned32 => mkConst ``TaskID.absSigned32
  | .byteSwap64 => mkConst ``TaskID.byteSwap64
  | .populationCount64 => mkConst ``TaskID.populationCount64
  | .average64 => mkConst ``TaskID.average64
  | .parity64 => mkConst ``TaskID.parity64
  | .rotateLeft64 => mkConst ``TaskID.rotateLeft64

/-- Balanced quotation is a controller optimization, not a trusted conversion
axiom. Its exact value is checked by the kernel in the expected statement. -/
private def balancedBytes : Nat → List X86.Byte → Expr
  | 0, bytes => toExpr bytes
  | fuel + 1, bytes =>
    if bytes.length ≤ 16 then toExpr bytes
    else
      let half := bytes.length / 2
      mkApp3 (mkConst ``List.append [Level.zero]) (toTypeExpr X86.Byte)
        (balancedBytes fuel (bytes.take half)) (balancedBytes fuel (bytes.drop half))

def byteExpr (bytes : List X86.Byte) : Expr := balancedBytes 16 bytes

def artifactExpr : Artifact → Expr
  | .raw bytes => mkApp (mkConst ``Artifact.raw) (byteExpr bytes)
  | .elf bytes span => mkApp2 (mkConst ``Artifact.elf) (byteExpr bytes) (toExpr span)

def expectedClaim (id : TaskID) (bytes : List X86.Byte) : Expr :=
  mkApp2 (mkConst ``Grading.Claim) (taskExpr id) (byteExpr bytes)

/-- Each call gets a fresh trusted snapshot. No candidate module name or search
path is an input. The installation's executable, project .olean files and pinned
Lean sysroot must be provisioned as trusted, immutable build products. -/
def trustedEnvironment : IO Environment := do
  let executable ← IO.appPath
  let some bin := executable.parent | throw (IO.userError "missing executable directory")
  let some build := bin.parent | throw (IO.userError "missing installation directory")
  let sysroot ← findSysroot
  searchPathRef.set [build / "lib" / "lean", sysroot / "lib" / "lean"]
  importModules #[{ module := `EDSL },
    { module := `EDSL.Grading.Known }, { module := `EDSL.Grading.Artifact },
    { module := `EDSL.Grading.CallStack.Artifact },
    { module := `EDSL.Grading.CallMemory64.Artifact },
    { module := `EDSL.Grading.CallMemoryLoop64.Artifact },
    { module := `EDSL.Grading.AtomicLogical64.Artifact },
    { module := `EDSL.Grading.AtomicSet64.Artifact }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)

/-- Read at most limit+1 bytes, including when a file grows while being read.
The extra byte distinguishes an over-limit stream from exact-limit EOF. -/
def readBounded (path : System.FilePath) (limit : Nat) : IO (Except Failure ByteArray) :=
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    let mut done := false
    for _ in List.range (limit / 4096 + 2) do
      if !done then
        let remaining := limit + 1 - bytes.size
        let chunk ← handle.read (USize.ofNat (min 4096 remaining))
        bytes := bytes ++ chunk
        if bytes.size > limit then return fail .resource "file bytes"
        if chunk.isEmpty then done := true
    if !done then return fail .resource "file bytes"
    return .ok bytes

def readPacket (path : System.FilePath) (limits : Limits) : IO (Except Failure String) := do
  let bytes ← readBounded path limits.maxInputBytes
  return do
    let bytes ← bytes
    let some text := String.fromUTF8? bytes | fail .malformed "proof UTF-8"
    return text

def makeArtifact (bytes : ByteArray) (span : Option Nat) : Artifact :=
  let file := bytes.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)
  match span with
  | none => .raw file
  | some n => .elf file n

structure Acceptance where
  codeBytes : Nat
  declarations : Nat
  constants : Nat
  decoderSteps : Nat
  auditSteps : Nat
  kernelChecks : Nat

/-- Runtime selection is independently recomputed by the kernel in the final
artifact wrapper. Neither host selection nor a displayed file hash is a proof. -/
def grade (env : Kernel.Environment) (limits : Limits) (id : TaskID)
    (artifact : Artifact) (packet : String) : Except Failure Acceptance := do
  let selected ← artifact.select |>.mapError fun _ =>
    ⟨.unsupported, "artifact admission failed"⟩
  let checked ← checkPacket env limits (expectedClaim id selected.code) packet
  let code := byteExpr selected.code
  let someCode := mkApp2 (mkConst ``Option.some [Level.zero])
    (toTypeExpr (List X86.Byte)) code
  let selection := mkApp2 (mkConst ``Eq.refl [Level.one])
    (toTypeExpr (Option (List X86.Byte))) someCode
  let value := mkAppN (mkConst ``Artifact.certify)
    #[taskExpr id, artifactExpr artifact, code, selection, checked.value]
  let expected := mkApp2 (mkConst ``Artifact.Claim) (taskExpr id) (artifactExpr artifact)
  -- Full files can require more reduction depth than the packet's syntax.
  -- The wrapper uses the same cumulative thread ceiling; it does not reset
  -- the counter or provide another heartbeat allowance.
  let wrapperLimits := { limits with kernelRecDepth := 32768 }
  let wrapped ← checkExpr checked.env wrapperLimits expected value
    `EDSLGrader.Internal.artifact
  return {
    codeBytes := selected.code.length
    declarations := checked.declarations
    constants := max checked.constants wrapped.constants
    decoderSteps := checked.decoderSteps
    auditSteps := checked.auditSteps + wrapped.auditSteps
    kernelChecks := checked.kernelChecks + wrapped.kernelChecks }

def failureStatus : FailureKind → UInt32
  | .malformed => 4
  | .unsupported => 3
  | .rejected | .audit => 5
  | .resource => 6
  | .internal => 1

end EDSLGrader
