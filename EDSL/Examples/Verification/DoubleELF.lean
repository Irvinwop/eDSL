/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Examples.Verification.Double
import EDSL.PureCall.ELFCertificate

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Examples.Verification.DoubleELF
open X86 X86.Sequential OS PureCall
open Examples.Verification.Double

/-! A complete synthetic ELF64LE file, independently encoded below, binds the
existing doubling proof to a unique non-entry symbol. The ELF entry contains
MOV EAX,42; RET, whereas `double` contains LEA RAX,[RDI+RDI]; RET.

The encoder knows only ELF64LE byte positions. Metadata witnesses are separate
declarations, authenticated by the production checker. This is a modeled
sequential callable certificate, with stable ordinary RAM, supplied ownership
and no asynchronous interference. It establishes no native execution, startup,
whole-OS, source/compiler preservation or registered grading claim. -/

private def le (width value : Nat) : List Byte :=
  (List.range width).map fun index => BitVec.ofNat 8 (value / 256 ^ index)

private def sectionRow
    (name kind flags address offset size link info alignment entrySize : Nat) : List Byte :=
  le 4 name ++ le 4 kind ++ le 8 flags ++ le 8 address ++ le 8 offset ++
  le 8 size ++ le 4 link ++ le 4 info ++ le 8 alignment ++ le 8 entrySize

private def symbolRow (name info other sh value size : Nat) : List Byte :=
  le 4 name ++ le 1 info ++ le 1 other ++ le 2 sh ++ le 8 value ++ le 8 size

def name : List Byte := [0x64, 0x6f, 0x75, 0x62, 0x6c, 0x65] -- double

def strings : List Byte :=
  [0, 0x64, 0x6f, 0x75, 0x62, 0x6c, 0x65, 0,
      0x68, 0x65, 0x6c, 0x70, 0x65, 0x72, 0]

def sectionNames : List Byte :=
  [0, 0x2e, 0x74, 0x65, 0x78, 0x74, 0,
      0x2e, 0x73, 0x79, 0x6d, 0x74, 0x61, 0x62, 0,
      0x2e, 0x73, 0x74, 0x72, 0x74, 0x61, 0x62, 0,
      0x2e, 0x73, 0x68, 0x73, 0x74, 0x72, 0x74, 0x61, 0x62, 0]

/-- Header at zero, one RX LOAD, helper at 0x80, selected function at 0x88,
STRTAB at 0x90, SYMTAB at 0xa0, SHSTRTAB at 0xf0 and five section rows at
0x180. Neither production field lists nor witnesses generate these bytes. -/
def file : List Byte :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
  le 2 2 ++ le 2 62 ++ le 4 1 ++ le 8 0x400080 ++ le 8 64 ++ le 8 0x180 ++
  le 4 0 ++ le 2 64 ++ le 2 56 ++ le 2 1 ++ le 2 64 ++ le 2 5 ++ le 2 4 ++
  le 4 1 ++ le 4 5 ++ le 8 0x80 ++ le 8 0x400080 ++ le 8 0x400080 ++
  le 8 13 ++ le 8 13 ++ le 8 4096 ++ List.replicate 8 0 ++
  [0xb8, 0x2a, 0, 0, 0, 0xc3, 0, 0, 0x48, 0x8d, 0x04, 0x3f, 0xc3] ++
  List.replicate 3 0 ++ strings ++ [0] ++
  symbolRow 0 0 0 0 0 0 ++
  symbolRow 1 0x12 0 1 0x400088 5 ++
  symbolRow 8 0x12 0 1 0x400080 6 ++
  List.replicate 8 0 ++ sectionNames ++ List.replicate 111 0 ++
  sectionRow 0 0 0 0 0 0 0 0 0 0 ++
  sectionRow 1 1 6 0x400080 0x80 13 0 0 16 0 ++
  sectionRow 7 2 0 0 0xa0 72 3 1 8 24 ++
  sectionRow 15 3 0 0 0x90 15 0 0 1 0 ++
  sectionRow 23 3 0 0 0xf0 33 0 0 1 0

def table : ELF.FunctionWindow.Table :=
  ⟨⟨0, 0x400080, 64, 0x180, 5, 4⟩,
    [⟨1, 0x400080, ⟨0x80, 0x400080, 13, 13, 5, 4096⟩⟩]⟩

def text : ELF.FunctionSymbol.Section := ⟨1, 1, 6, 0x400080, 0x80, 13, 0, 0, 16, 0⟩
def symtab : ELF.FunctionSymbol.Section := ⟨7, 2, 0, 0, 0xa0, 72, 3, 1, 8, 24⟩
def strtab : ELF.FunctionSymbol.Section := ⟨15, 3, 0, 0, 0x90, 15, 0, 0, 1, 0⟩
def shstrtab : ELF.FunctionSymbol.Section := ⟨23, 3, 0, 0, 0xf0, 33, 0, 0, 1, 0⟩
def target : ELF.FunctionSymbol.Symbol := ⟨1, 0x12, 0, 1, 0x400088, 5⟩
def helper : ELF.FunctionSymbol.Symbol := ⟨8, 0x12, 0, 1, 0x400080, 6⟩

def metadata : ELF.FunctionSymbol.Metadata :=
  ⟨[default, text, symtab, strtab, shstrtab], ⟨4, shstrtab, sectionNames⟩,
    [⟨2, symtab, [default, target, helper], ⟨3, strtab, strings⟩⟩]⟩

def selected : ELF.FunctionSymbol.Function :=
  ⟨⟨2, 1, target⟩, text, ⟨0x400088, 0x88⟩⟩

def input : ELF.FunctionInput := ⟨table, metadata, selected, bytes⟩

/-- Authenticating the complete independent file, exact name and full extent
selects the existing Double bytes, not the different ELF entry routine. -/
theorem checked : input.check file name = true := by decide +kernel

/-- Present caller mappings are supplied before installation. Besides the
real return slot, retain unrelated writable/inaccessible cells and an executable
copy at a different address. Equal code there does not select the ELF symbol. -/
def prior : AddressSpace.Space where
  cells address :=
    if (⟨0x700008, 8⟩ : AddressSpace.Region).Contains address then
      some ⟨(0x654321 : Word).extractLsb' ((address.toNat - 0x700008) * 8) 8,
        AddressSpace.readOnly⟩
    else if (⟨0x500120, 5⟩ : AddressSpace.Region).Contains address then
      ([0x48, 0x8d, 0x04, 0x3f, 0xc3][address.toNat - 0x500120]?).map
        fun byte => ⟨byte, AddressSpace.readExecute⟩
    else if address = 0x900000 then some ⟨0xa5, AddressSpace.readWrite⟩
    else if address = 0x900001 then some ⟨0x5a, AddressSpace.inaccessible⟩
    else none

def caller : ELF.CallerResources.Caller := ⟨prior, 17, 29, 41, 0x700008, 0x654321⟩

theorem callerFacts : caller.Facts := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  rfl

/-- Prove page freshness by disjoint address bounds, without enumerating a
page or increasing the default proof budgets. -/
theorem fresh : ELF.fresh input.table.image caller.prior = true := by
  change (AddressSpace.allUnmapped prior
    (⟨0x400000, 4096⟩ : AddressSpace.Region) && true) = true
  rw [Bool.and_true]
  apply List.all_eq_true.mpr
  intro address member
  obtain ⟨offset, inRange, rfl⟩ := List.mem_map.mp member
  have bound : offset < 4096 := List.mem_range.mp inRange
  have numeric : (0x400000#64 + BitVec.ofNat 64 offset).toNat = 0x400000 + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have stackOutside : ¬(⟨0x700008#64, 8⟩ : AddressSpace.Region).Contains
      (0x400000#64 + BitVec.ofNat 64 offset) := by
    simp only [AddressSpace.Region.Contains, numeric, BitVec.toNat_ofNat]
    omega
  have copyOutside : ¬(⟨0x500120#64, 5⟩ : AddressSpace.Region).Contains
      (0x400000#64 + BitVec.ofNat 64 offset) := by
    simp only [AddressSpace.Region.Contains, numeric, BitVec.toNat_ofNat]
    omega
  have other : 0x400000#64 + BitVec.ofNat 64 offset ≠ 0x900000#64 ∧
      0x400000#64 + BitVec.ofNat 64 offset ≠ 0x900001#64 := by
    constructor <;> intro same <;> have := congrArg BitVec.toNat same <;>
      simp only [numeric, BitVec.toNat_ofNat] at this <;> omega
  change (prior.cells (0x400000#64 + BitVec.ofNat 64 offset)).isNone = true
  dsimp only [prior]
  simp only [BitVec.ofNat_eq_ofNat]
  rw [ite_eq_right stackOutside, ite_eq_right copyOutside,
    ite_eq_right other.1, ite_eq_right other.2]
  rfl

theorem separate : Ownership.Disjoint
    ⟨input.function.window.base, input.bytes.length⟩ caller.region := by decide +kernel

def loaded : ELF.Loaded := ELF.CallerResources.loaded file input caller
def environment : CallResources.Domain.Initial := ELF.CallerResources.initial file input caller

theorem admitted : input.admit file name caller.prior = .ok loaded :=
  ELF.CallerResources.admitted checked fresh

theorem present : CallResources.Domain.Facts environment :=
  ELF.CallerResources.initial_facts checked fresh callerFacts separate

/-- The useful constructor witness is 7. Other values and arbitrary remaining
registers/flags below are admitted independently of that chosen witness. -/
def certificate : ELFCertificate spec file name :=
  ELFCertificate.ofCaller spec input checked Double.semantics caller fresh callerFacts
    separate (7 : Word) trivial (by change (7 : Word) ≠ 0; decide +kernel)

def resource (value : Word) : Resources spec := Domain.resource environment spec value

def machine (value : Word) (registers : Register → Word) (flags : Word) : State :=
  CallResources.Domain.machine environment
    (fun register => if register = .rdi then value else registers register) flags

theorem pre (value : Word) (registers : Register → Word) (flags : Word) :
    ResourcePre spec bytes (resource value) (machine value registers flags) := by
  refine ⟨CallResources.Domain.current present _ _, rfl, rfl, ?_, trivial, ?_⟩
  · simp [machine, CallResources.Domain.machine, resource, Domain.resource,
      environment, ELF.CallerResources.initial, CallResources.Domain.call]
  · intro index argument binding
    simp only [spec] at binding
    split at binding
    · have zero : index = 0 := Fin.ext (by assumption)
      subst index
      cases binding
      simp [Argument.Holds, machine, CallResources.Domain.machine, argumentRegister,
        resource, Domain.resource]
    · contradiction

def call (value : Word) (registers : Register → Word) (flags : Word) :
    ELFLoadedCall spec file name certificate.input :=
  ⟨caller.prior, loaded, admitted, resource value, machine value registers flags,
    pre value registers flags, rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem binding :
    ELF.FunctionSymbol.CheckedMetadata file table.header metadata ∧
    selected.Contract metadata name bytes.length ∧
    ELF.FunctionWindow.Layout file table ∧
    ELF.FunctionWindow.Selection file table.image selected.window bytes := certificate.binding

theorem nonvacuous : Grading.ReadOnlyNonvacuous (readOnlyTask spec) bytes :=
  certificate.nonvacuous

/-- The certificate's useful witness retains exact selected-address current
code, total execution and original authority at every actual prefix. -/
theorem useful_execution :
    ∃ call : ELFLoadedCall spec file name certificate.input,
      spec.useful call.resource.value ∧
      CodeAt call.initial.memory call.initial.rip bytes ∧
      AllExecutions call.initial (fun result =>
        Post spec (resourceInput call.resource) call.initial result.state ∧
        CallResources.Current call.resource.call call.resource.shared result.state) ∧
      Grading.ReadOnlyPolicy call.initial
        (CallResources.Current call.resource.call call.resource.shared)
        (fun _ => CallResources.ReadAllowed call.resource.call call.resource.shared) :=
  certificate.useful_execution

/-- Universal generic certificate behavior, including value zero, arbitrary
unbound registers, flags and every AF stream. Return retains the complete
original world, memory permissions, caller loan, ABI and mathematical result. -/
theorem resources_survive (value : Word) (registers : Register → Word) (flags : Word) :
    AllExecutions (machine value registers flags) (fun result =>
      Post spec (resourceInput (resource value)) (machine value registers flags) result.state ∧
      CallResources.Current (resource value).call (resource value).shared result.state) ∧
    Grading.ReadOnlyPolicy (machine value registers flags)
      (CallResources.Current (resource value).call (resource value).shared)
      (fun _ => CallResources.ReadAllowed (resource value).call (resource value).shared) :=
  certificate.resource (call value registers flags)

/-- Reuse Double's proved two-instruction execution. The generic certificate
authenticates the same actual run's full resource postcondition. Numerical
expectations are supplied independently of instruction evaluation. -/
theorem numeric_result (value expected : Word)
    (mathematics : expected.toNat = (2 * value.toNat) % 2^64)
    (registers : Register → Word) (flags : Word) (choices : Choices) :
    ∃ result, Sequential.run choices 2 (machine value registers flags) = .ok result ∧
      result.state.registers .rax = expected ∧
      Post spec (resourceInput (resource value)) (machine value registers flags) result.state ∧
      CallResources.Current (resource value).call (resource value).shared result.state := by
  obtain ⟨result, actual, _⟩ := Double.executes _ _ (pre value registers flags).machine choices
  have full := (resources_survive value registers flags).1.project
    ⟨choices, Sequential.run_sound actual⟩
  exact ⟨result, actual, BitVec.eq_of_toNat_eq (full.1.result.trans mathematics.symm), full⟩

end EDSL.Examples.Verification.DoubleELF
