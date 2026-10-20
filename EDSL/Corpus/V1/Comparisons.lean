/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.Comparison
import EDSL.Corpus.ELFResources
import EDSL.Corpus.V1.GCC
import EDSL.Corpus.V1.Clang

namespace EDSL.Corpus.V1.Comparisons
open X86 OS OS.AddressSpace

abbrev Compiler := Comparison.Compiler
abbrev Operation := Comparison.Operation

def file : Compiler → List Byte
  | .defaultGCC => GCC.file
  | .defaultClang => Clang.file

/-- Metadata and windows are untrusted data until `checked` is applied. All
functions of one compiler share its one complete literal file and tables. -/
def input (compiler : Compiler) (operation : Operation) : FunctionInput :=
  match compiler, operation with
  | .defaultGCC, .minimum => ⟨GCC.table, GCC.metadata, GCC.minFunction, GCC.minBytes⟩
  | .defaultGCC, .maximum => ⟨GCC.table, GCC.metadata, GCC.maxFunction, GCC.maxBytes⟩
  | .defaultClang, .minimum => ⟨Clang.table, Clang.metadata, Clang.minFunction, Clang.minBytes⟩
  | .defaultClang, .maximum => ⟨Clang.table, Clang.metadata, Clang.maxFunction, Clang.maxBytes⟩

theorem checked (compiler : Compiler) (operation : Operation) :
    (input compiler operation).check (file compiler) (Comparison.name operation) = true := by
  cases compiler <;> cases operation
  · exact GCC.minAccepted
  · exact GCC.maxAccepted
  · exact Clang.minAccepted
  · exact Clang.maxAccepted

theorem body (compiler : Compiler) (operation : Operation) :
    (input compiler operation).bytes = X86.VCGen.CompilerComparisons.bytes compiler operation := by
  cases compiler <;> cases operation <;> rfl

/-- This independent caller slot inhabits a newly declared modeled resource
world. It is not native Linux startup or authentication of ownership. -/
def caller : ELFResources.Caller where
  prior.cells address :=
    if (⟨0x700008, 8⟩ : Region).Contains address then
      some ⟨(0x654321 : Word).extractLsb' ((address.toNat - 0x700008) * 8) 8, readOnly⟩
    else none
  codeOwner := 101
  callerOwner := 202
  worker := 303
  stack := 0x700008
  returnAddress := 0x654321

theorem caller_facts : caller.Facts := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  rfl

theorem fresh (compiler : Compiler) (operation : Operation) :
    ELF.fresh (input compiler operation).table.image caller.prior = true := by
  cases compiler <;> cases operation <;> decide +kernel

theorem separate (compiler : Compiler) (operation : Operation) :
    Ownership.Disjoint ⟨(input compiler operation).function.window.base,
      (input compiler operation).bytes.length⟩ caller.region := by
  cases compiler <;> cases operation <;> decide +kernel

def environment (compiler : Compiler) (operation : Operation) : CallResources.Domain.Initial :=
  ELFResources.initial (file compiler) (input compiler operation) caller

theorem environment_facts (compiler : Compiler) (operation : Operation) :
    CallResources.Domain.Facts (environment compiler operation) :=
  ELFResources.initial_facts (checked compiler operation) (fresh compiler operation)
    caller_facts (separate compiler operation)

/-- Four exact final-file, unique-symbol, registered mathematical certificates,
composed through shared VCG and OS-resource APIs. The useful actual-address
witnesses use unequal full64 inputs. The fixed machine environment requires
long mode, CET/IBT and shadow stacks disabled, stable modeled RAM, and the
registered caller/code authority; source, physical CPU and native OS startup
refinement are outside this theorem. -/
def certificate (compiler : Compiler) (operation : Operation) :
    Certificate (Comparison.taskID operation) (file compiler) (Comparison.name operation) :=
  Comparison.certificate compiler operation (input compiler operation)
    (checked compiler operation) (body compiler operation) caller.prior
    (ELFResources.loaded (file compiler) (input compiler operation) caller)
    (ELFResources.admitted (checked compiler operation) (fresh compiler operation))
    (environment compiler operation) (environment_facts compiler operation) rfl rfl rfl

/-- File/name binding and current-resource nonvacuity are joint obligations of
the typed certificate. Every admitted call obtains the registered all-AF result
and prefix policy via `Certificate.resource`. -/
theorem useful_execution (compiler : Compiler) (operation : Operation) :
    ∃ call : LoadedCall (Comparison.taskID operation) (file compiler) (Comparison.name operation)
        (certificate compiler operation).input,
      CodeAt call.initial.memory call.initial.rip (certificate compiler operation).input.bytes ∧
      X86.Sequential.AllExecutions call.initial (fun result =>
        (Grading.registered (Comparison.taskID operation)).post
          ((Grading.registered (Comparison.taskID operation)).input call.resource)
          call.initial result.state ∧
        (Grading.registered (Comparison.taskID operation)).resourceReturn
          (certificate compiler operation).input.bytes call.resource call.initial result) :=
  (certificate compiler operation).useful_execution

end EDSL.Corpus.V1.Comparisons
