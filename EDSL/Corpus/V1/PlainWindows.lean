/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.FrozenFunction
import EDSL.X86.VCGen.PlainMethods.Model

set_option autoImplicit false
set_option warningAsError true

/-!
Complete unchanged `c_atomic_load_acquire64` / `c_atomic_store_release64`
named extents in both frozen final ELF files. This data adapter binds names,
files and code shapes only. It supplies no behavior, ABI, resource, ordering,
native-execution, compiler-preservation or corpus-credit claim. GCC's original
ENDBR64 is retained under the existing CET-off decoding profile.
-/

namespace EDSL.Corpus.V1.PlainWindows
open X86 ELF.FunctionSymbol

abbrev Compiler := ArithmeticWindows.Compiler

inductive Kind where
  | loadAcquire
  | storeRelease
  deriving DecidableEq, Repr

/-- Reuse each complete frozen file without copying its literal bytes. -/
def file : Compiler → List Byte := ArithmeticWindows.file

/-- Exact ELF byte names, excluding the terminating NUL. -/
def name : Kind → List Byte
  | .loadAcquire => [99,95,97,116,111,109,105,99,95,108,111,97,100,95,97,99,113,117,105,114,101,54,52]
  | .storeRelease => [99,95,97,116,111,109,105,99,95,115,116,111,114,101,95,114,101,108,101,97,115,101,54,52]

/-- Entire symbol extents, including RET and GCC ENDBR64; intersymbol padding
is outside these extents. -/
def bytes : Compiler → Kind → List Byte
  | .defaultGCC, .loadAcquire => [0xf3,0x0f,0x1e,0xfa,0x48,0x8b,0x07,0xc3]
  | .defaultGCC, .storeRelease => [0xf3,0x0f,0x1e,0xfa,0x48,0x89,0x37,0xc3]
  | .defaultClang, .loadAcquire => [0x48,0x8b,0x07,0xc3]
  | .defaultClang, .storeRelease => [0x48,0x89,0x37,0xc3]

/-- Actual static symbol-table indices, distinct from corpus definition IDs
35/36. Row selection remains untrusted until the full named check succeeds. -/
def symbolIndex (c : Compiler) (k : Kind) :
    Fin (FrozenFunction.symbols c).rows.length :=
  match c, k with
  | .defaultGCC, .loadAcquire => ⟨115, by decide +kernel⟩
  | .defaultGCC, .storeRelease => ⟨140, by decide +kernel⟩
  | .defaultClang, .loadAcquire => ⟨92, by decide +kernel⟩
  | .defaultClang, .storeRelease => ⟨116, by decide +kernel⟩

def function (c : Compiler) (k : Kind) : Function :=
  FrozenFunction.function c (symbolIndex c k)

def input (c : Compiler) (k : Kind) : FunctionInput :=
  FrozenFunction.input c (symbolIndex c k) (bytes c k)

theorem body (c : Compiler) (k : Kind) : (input c k).bytes = bytes c k := rfl

/-- Authenticate the unique names, actual symbol rows, entire declared extents,
addresses, file offsets and executable image bytes against the shared files.
Shared metadata/layout and bounded file-tail proofs are reused. -/
theorem checked (c : Compiler) (k : Kind) :
    (input c k).check (file c) (name k) = true := by
  cases c with
  | defaultGCC =>
    change check GCC.file GCC.table GCC.metadata (name k) (function .defaultGCC k)
      (bytes .defaultGCC k) = true
    unfold check
    rw [GCC.metadataAccepted]
    unfold ELF.FunctionWindow.check
    have bounded : (function .defaultGCC k).window.offset ≤ 41016 := by
      cases k <;> decide +kernel
    rw [GCC.layoutAccepted, GCC.fileDropChunks _ bounded]
    simp only [GCC.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, GCC.fileByteChunks]
    cases k <;> decide +kernel
  | defaultClang =>
    change check Clang.file Clang.table Clang.metadata (name k) (function .defaultClang k)
      (bytes .defaultClang k) = true
    unfold check
    rw [Clang.metadataAccepted]
    unfold ELF.FunctionWindow.check
    have bounded : (function .defaultClang k).window.offset ≤ 44240 := by
      cases k <;> decide +kernel
    rw [Clang.layoutAccepted, Clang.fileDropAt _ bounded]
    simp only [Clang.fileLength, ELF.checkCode, X86.fetchByte, OS.AddressSpace.toMemory,
      ELF.install, ELF.segmentCell, FrozenFunction.clangFileByte]
    cases k <;> decide +kernel

/-- Operand selection only: load into RAX from [RDI], or store RSI into [RDI].
This definition depends on neither values nor a method/admission proof. -/
def operation : Kind → X86.VCGen.PlainMethods.Operation
  | .loadAcquire => .load (.base .rdi)
  | .storeRelease => .store (.base .rdi) .rsi

def padding : Compiler → List X86.VCGen.PlainMethods.Padding
  | .defaultGCC => [.endbr64]
  | .defaultClang => []

/-- Production decoding with exact operands and final RET/extent coverage.
The acquire/release names do not establish a synchronization contract. -/
theorem shape_checked (c : Compiler) (k : Kind) :
    X86.VCGen.PlainMethods.check (bytes c k) (operation k) (padding c) = true := by
  cases c <;> cases k <;> decide +kernel

#print axioms body
#print axioms checked
#print axioms shape_checked
end EDSL.Corpus.V1.PlainWindows
#audit_edsl
