/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Driver
import EDSL.Grading.RegisteredArtifact

set_option autoImplicit false
set_option warningAsError true

/-! Additive trusted controller for registered execution/task pairs. As with the
original driver, mathematical claims are kernel checked; no formal theorem is
advertised about this IO implementation or native platform correspondence. -/
namespace EDSLGrader
open Lean EDSL EDSL.Grading EDSLGrader.Runtime

/-- Existing task spellings retain their original parser. The new spelling
selects a trusted identifier, never a candidate-supplied execution model. -/
def registryID : String → Option RegistryID
  | "multiplyModulo64" => some .multiplyModulo64
  | name => (taskID name).map RegistryID.legacy

def registryExpr : RegistryID → Expr
  | .legacy id => mkApp (mkConst ``RegistryID.legacy) (taskExpr id)
  | .multiplyModulo64 => mkConst ``RegistryID.multiplyModulo64

def expectedRegisteredClaim (id : RegistryID) (bytes : List X86.Byte) : Expr :=
  mkApp2 (mkConst ``RegisteredClaim) (registryExpr id) (byteExpr bytes)

/-- Fresh trusted installation snapshot with the unchanged fixed module list
plus the additive registered-artifact wrapper. Candidate module names, search
paths, options, plugins and execution models are not inputs. The executable,
project oleans and pinned Lean sysroot must be immutable trusted products. -/
def trustedRegistryEnvironment : IO Environment := do
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
    { module := `EDSL.Grading.AtomicSet64.Artifact },
    { module := `EDSL.Grading.RegisteredArtifact }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false)

/-- Legacy identifiers call the original grader directly, preserving packet
acceptance and the original expected claim/artifact wrapper. The new task uses
its fixed registered contract and the same packet limits, axiom audit and
cumulative wrapper ceiling as the original controller. -/
def gradeRegistered (env : Kernel.Environment) (limits : Limits) (id : RegistryID)
    (artifact : Artifact) (packet : String) : Except Failure Acceptance :=
  match id with
  | .legacy original => grade env limits original artifact packet
  | .multiplyModulo64 => do
    let selected ← artifact.select |>.mapError fun _ =>
      ⟨.unsupported, "artifact admission failed"⟩
    let checked ← checkPacket env limits
      (expectedRegisteredClaim .multiplyModulo64 selected.code) packet
    let code := byteExpr selected.code
    let someCode := mkApp2 (mkConst ``Option.some [Level.zero])
      (toTypeExpr (List X86.Byte)) code
    let selection := mkApp2 (mkConst ``Eq.refl [Level.one])
      (toTypeExpr (Option (List X86.Byte))) someCode
    let value := mkAppN (mkConst ``RegisteredArtifact.certify)
      #[registryExpr .multiplyModulo64, artifactExpr artifact, code, selection, checked.value]
    let expected := mkApp2 (mkConst ``RegisteredArtifact.Claim)
      (registryExpr .multiplyModulo64) (artifactExpr artifact)
    -- Identical to the original artifact wrapper: deeper full-file reduction,
    -- without resetting counters or adding another heartbeat allowance.
    let wrapperLimits := { limits with kernelRecDepth := 32768 }
    let wrapped ← checkExpr checked.env wrapperLimits expected value
      `EDSLGrader.Internal.registeredArtifact
    return {
      codeBytes := selected.code.length
      declarations := checked.declarations
      constants := max checked.constants wrapped.constants
      decoderSteps := checked.decoderSteps
      auditSteps := checked.auditSteps + wrapped.auditSteps
      kernelChecks := checked.kernelChecks + wrapped.kernelChecks }

end EDSLGrader
