/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Certificate
import EDSL.OS.CallResources.Domain
import EDSL.X86.VCGen.CompilerComparisons

namespace EDSL.Corpus.Comparison
open X86 OS

abbrev Compiler := X86.VCGen.CompilerComparisons.Compiler
abbrev Operation := X86.VCGen.CompilerComparisons.Operation

/-- Registry-owned names for the independent unsigned-order tasks. -/
def name : Operation → List Byte
  | .minimum => [99,95,109,105,110,95,117,54,52]
  | .maximum => [99,95,109,97,120,95,117,54,52]

def taskID (operation : Operation) : Grading.TaskID :=
  X86.VCGen.CompilerComparisons.taskID operation

def registers (left right : Word) : Register → Word
  | .rdi => left
  | .rsi => right
  | _ => 0xfedcba9876543210

def initial (environment : CallResources.Domain.Initial) (left right : Word) : X86.State :=
  CallResources.Domain.machine environment (registers left right) 0x202

def resource (environment : CallResources.Domain.Initial) (left right : Word) : Comparison64.Resources :=
  ⟨CallResources.Domain.shared environment, CallResources.Domain.call environment, left, right⟩

/-- The resource domain is inhabited independently of decoding and the desired
minimum/maximum. Its sole byte condition is the environment's exact code span. -/
theorem resource_pre {environment : CallResources.Domain.Initial}
    (facts : CallResources.Domain.Facts environment) {bytes : List Byte}
    (source : environment.bytes = bytes) (left right : Word) :
    Comparison64.ResourcePre bytes (resource environment left right)
      (initial environment left right) := by
  refine ⟨CallResources.Domain.current facts _ _, source, rfl, ?_, ?_, ?_⟩
  all_goals rfl

/-- This constructor uses current loans in a declared new initial model. It
cannot transport a preexisting/native world or manufacture native authority.
The supplied mapping is exactly the symbol checker's fresh loaded space. -/
def loadedCall (operation : Operation) {file : List Byte} (input : FunctionInput)
    (prior : AddressSpace.Space) (loaded : ELF.Loaded)
    (admitted : input.admit file (name operation) prior = .ok loaded)
    (environment : CallResources.Domain.Initial)
    (facts : CallResources.Domain.Facts environment)
    (source : environment.bytes = input.bytes)
    (code : environment.code = input.function.window.base)
    (mapped : environment.space = loaded.space)
    (left right : Word) (useful : left ≠ right) :
    LoadedCall (taskID operation) file (name operation) input := by
  have pre := resource_pre facts source left right
  have atEntry : (initial environment left right).rip = input.function.window.base := code
  have inMemory : (initial environment left right).memory = AddressSpace.toMemory loaded.space :=
    congrArg AddressSpace.toMemory mapped
  have text : ELF.FunctionWindow.TextUnchanged (AddressSpace.toMemory loaded.space)
      (initial environment left right).memory input.function.window input.bytes.length := by
    rw [inMemory]
    intro _ _
    exact ⟨rfl, rfl⟩
  cases operation <;>
    exact ⟨prior, loaded, admitted, resource environment left right,
      initial environment left right, useful, pre, atEntry, text⟩

/-- One family adapter composes all four ordinary compiler windows. A checked
symbol/file and a useful actual-address resource witness remain mandatory.
There is no source/IR preservation or native Linux/CPU refinement conclusion. -/
def certificate (compiler : Compiler) (operation : Operation) {file : List Byte}
    (input : FunctionInput) (checked : input.check file (name operation) = true)
    (body : input.bytes = X86.VCGen.CompilerComparisons.bytes compiler operation)
    (prior : AddressSpace.Space) (loaded : ELF.Loaded)
    (admitted : input.admit file (name operation) prior = .ok loaded)
    (environment : CallResources.Domain.Initial)
    (facts : CallResources.Domain.Facts environment)
    (source : environment.bytes = input.bytes)
    (code : environment.code = input.function.window.base)
    (mapped : environment.space = loaded.space) :
    Certificate (taskID operation) file (name operation) where
  input := input
  checked := checked
  claim := by
    rw [body]
    exact X86.VCGen.CompilerComparisons.claim compiler operation
  inhabited := ⟨loadedCall operation input prior loaded admitted environment facts source code mapped
    0xffffffffffffffff 0x100000000 (by decide)⟩

end EDSL.Corpus.Comparison
