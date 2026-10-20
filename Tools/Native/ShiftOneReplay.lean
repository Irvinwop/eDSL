/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.native.ShiftOneReplay

/-- IO entry point separate from the importable production projection. -/
def main : List String → IO Unit := EDSL.Tests.ShiftOneReplay.main
