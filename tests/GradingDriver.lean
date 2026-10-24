/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.ByteQuotation
import EDSL.Grading.Runtime.Checker
import Lean

open Lean EDSLGrader EDSLGrader.Runtime

-- Compare the controller's balanced quotation with Lean's independent standard
-- literal quotation, at both sides of each chunk/split boundary. A dropped,
-- swapped, duplicated or wrapped byte must break actual kernel conversion.
run_cmd do
  let env := (← getEnv).toKernelEnv
  let listType := toTypeExpr (List EDSL.X86.Byte)
  for length in [0, 1, 15, 16, 17, 31, 32, 33, 64, 65, 255, 256, 257] do
    let bytes := (List.range length).map fun i => BitVec.ofNat 8 (i * 73 + 251)
    let literal := toExpr bytes
    let actual := byteExpr bytes
    let expected := mkApp3 (mkConst ``Eq [1]) listType actual literal
    let proof := mkApp2 (mkConst ``Eq.refl [1]) listType literal
    match checkExpr env { kernelRecDepth := 4096 } expected proof
        `EDSLGrader.Internal.quotationTest with
    | .error failure => throwError "balanced quotation failed at length {length}: {failure}"
    | .ok _ => pure ()
  logInfo "Balanced file quotation agrees with independent literal quotation at all tested boundaries"
