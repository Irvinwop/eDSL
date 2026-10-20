/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.native.UnaryReplay

/-- IO entry point kept separate from the importable validator/proof module. -/
def main : List String → IO Unit := EDSL.Tests.UnaryReplay.main
