/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.Comparisons
import EDSL.Corpus.V1.Arithmetic
import EDSL.Corpus.V1.Clamps
import EDSL.Corpus.V1.FetchAddCertificates
import EDSL.Corpus.V1.ByteScanCertificates
import EDSL.Corpus.V1.IndexSearchCertificates
import EDSL.Corpus.V1.ByteComparisonCertificates
import EDSL.Corpus.V1.UnaryCertificates
import EDSL.Corpus.V1.PopcountCertificates
import EDSL.Corpus.V1.AverageCertificates
import EDSL.Corpus.V1.ParityCertificates
import EDSL.Corpus.V1.RotationCertificates
import Lean

namespace EDSL.Corpus.Reporting

/-- All eight entries have the registered task, exact complete literal file and
registered symbol in their types. This only composes the existing proof family;
it adds no per-function proof or IO/native premise to the claimed result. -/
theorem acceptedCertificates :
    Nonempty (Certificate (Comparison.taskID .minimum)
      (V1.Comparisons.file .defaultGCC) (Comparison.name .minimum)) ∧
    Nonempty (Certificate (Comparison.taskID .maximum)
      (V1.Comparisons.file .defaultGCC) (Comparison.name .maximum)) ∧
    Nonempty (Certificate .addModulo64
      (V1.ArithmeticWindows.file .defaultGCC) V1.ArithmeticWindows.name) ∧
    Nonempty (Certificate .clampSigned32
      (V1.Clamps.file .defaultGCC) V1.Clamps.name) ∧
    Nonempty (Certificate (Comparison.taskID .minimum)
      (V1.Comparisons.file .defaultClang) (Comparison.name .minimum)) ∧
    Nonempty (Certificate (Comparison.taskID .maximum)
      (V1.Comparisons.file .defaultClang) (Comparison.name .maximum)) ∧
    Nonempty (Certificate .addModulo64
      (V1.ArithmeticWindows.file .defaultClang) V1.ArithmeticWindows.name) ∧
    Nonempty (Certificate .clampSigned32
      (V1.Clamps.file .defaultClang) V1.Clamps.name) :=
  ⟨⟨V1.Comparisons.certificate .defaultGCC .minimum⟩,
    ⟨V1.Comparisons.certificate .defaultGCC .maximum⟩,
    ⟨V1.Arithmetic.certificate .defaultGCC⟩,
    ⟨V1.Clamps.certificate .defaultGCC⟩,
    ⟨V1.Comparisons.certificate .defaultClang .minimum⟩,
    ⟨V1.Comparisons.certificate .defaultClang .maximum⟩,
    ⟨V1.Arithmetic.certificate .defaultClang⟩,
    ⟨V1.Clamps.certificate .defaultClang⟩⟩

/-- The fixed concurrent contract is separate from the eight scalar tasks.
Each inhabitant binds the complete frozen file and exact registered name to
the universal managed claim and an actual loaded overlapping useful batch. -/
theorem acceptedConcurrentCertificates :
    Nonempty (Concurrent.FetchAddCertificate
      (V1.FetchAddWindows.file .defaultGCC) V1.FetchAddWindows.name) ∧
    Nonempty (Concurrent.FetchAddCertificate
      (V1.FetchAddWindows.file .defaultClang) V1.FetchAddWindows.name) :=
  ⟨⟨V1.FetchAddCertificates.certificate .defaultGCC⟩,
    ⟨V1.FetchAddCertificates.certificate .defaultClang⟩⟩

/-- Both complete files have the same fixed independent bounded-NUL task,
universal generated semantics and useful current loaded resources. -/
theorem acceptedBufferCertificates :
    Nonempty (Buffer.Certificate .firstBoundedNulLength
      (V1.ByteScanWindows.file .defaultGCC) V1.ByteScanWindows.name) ∧
    Nonempty (Buffer.Certificate .firstBoundedNulLength
      (V1.ByteScanWindows.file .defaultClang) V1.ByteScanWindows.name) :=
  ⟨⟨V1.ByteScanCertificates.certificate .defaultGCC⟩,
    ⟨V1.ByteScanCertificates.certificate .defaultClang⟩⟩

/-- The four exact functions have their fixed independent byte/u32 first-match
tasks, universal generated semantics and useful current loaded resources. -/
theorem acceptedIndexSearchCertificates :
    Nonempty (Buffer.Certificate .memchrIndex
      (V1.IndexSearchWindows.file .defaultGCC) (V1.IndexSearchWindows.name .byte)) ∧
    Nonempty (Buffer.Certificate .linearSearchU32
      (V1.IndexSearchWindows.file .defaultGCC) (V1.IndexSearchWindows.name .u32)) ∧
    Nonempty (Buffer.Certificate .memchrIndex
      (V1.IndexSearchWindows.file .defaultClang) (V1.IndexSearchWindows.name .byte)) ∧
    Nonempty (Buffer.Certificate .linearSearchU32
      (V1.IndexSearchWindows.file .defaultClang) (V1.IndexSearchWindows.name .u32)) :=
  ⟨⟨V1.IndexSearchCertificates.certificate .defaultGCC .byte⟩,
    ⟨V1.IndexSearchCertificates.certificate .defaultGCC .u32⟩,
    ⟨V1.IndexSearchCertificates.certificate .defaultClang .byte⟩,
    ⟨V1.IndexSearchCertificates.certificate .defaultClang .u32⟩⟩

/-- Both complete files have the fixed unsigned-byte lexicographic task with
signed low32 C-int return, universal semantics and useful current input loans. -/
theorem acceptedByteComparisonCertificates :
    Nonempty (Buffer.Certificate .lexicographicBytes
      (V1.ByteComparisonWindows.file .defaultGCC) V1.ByteComparisonWindows.name) ∧
    Nonempty (Buffer.Certificate .lexicographicBytes
      (V1.ByteComparisonWindows.file .defaultClang) V1.ByteComparisonWindows.name) :=
  ⟨⟨V1.ByteComparisonCertificates.certificate .defaultGCC⟩,
    ⟨V1.ByteComparisonCertificates.certificate .defaultClang⟩⟩

/-- Both unchanged compiler outputs satisfy the fixed signed absolute-value
and full64 byte-reversal tasks, with useful current loaded caller resources. -/
theorem acceptedUnaryCertificates :
    Nonempty (Certificate .absSigned32
      (V1.UnaryWindows.file .defaultGCC) (V1.UnaryWindows.name .absSigned32)) ∧
    Nonempty (Certificate .byteSwap64
      (V1.UnaryWindows.file .defaultGCC) (V1.UnaryWindows.name .byteSwap64)) ∧
    Nonempty (Certificate .absSigned32
      (V1.UnaryWindows.file .defaultClang) (V1.UnaryWindows.name .absSigned32)) ∧
    Nonempty (Certificate .byteSwap64
      (V1.UnaryWindows.file .defaultClang) (V1.UnaryWindows.name .byteSwap64)) :=
  ⟨⟨V1.UnaryCertificates.certificate .defaultGCC .absSigned32⟩,
    ⟨V1.UnaryCertificates.certificate .defaultGCC .byteSwap64⟩,
    ⟨V1.UnaryCertificates.certificate .defaultClang .absSigned32⟩,
    ⟨V1.UnaryCertificates.certificate .defaultClang .byteSwap64⟩⟩

/-- Both unchanged named loop extents satisfy the independent full64 input
cardinality/unsigned-low32 result contract, with useful current resources. -/
theorem acceptedPopcountCertificates :
    Nonempty (Certificate .populationCount64
      (V1.PopcountWindows.file .defaultGCC) V1.PopcountWindows.name) ∧
    Nonempty (Certificate .populationCount64
      (V1.PopcountWindows.file .defaultClang) V1.PopcountWindows.name) :=
  ⟨⟨V1.PopcountCertificates.certificate .defaultGCC⟩,
    ⟨V1.PopcountCertificates.certificate .defaultClang⟩⟩

/-- Both exact named outputs satisfy the registered full64 floor-average
contract, including unbounded input sums that overflow a machine word. -/
theorem acceptedAverageCertificates :
    Nonempty (Certificate .average64
      (V1.AverageWindows.file .defaultGCC) V1.AverageWindows.name) ∧
    Nonempty (Certificate .average64
      (V1.AverageWindows.file .defaultClang) V1.AverageWindows.name) :=
  ⟨⟨V1.AverageCertificates.certificate .defaultGCC⟩,
    ⟨V1.AverageCertificates.certificate .defaultClang⟩⟩

/-- Both complete row-12 artifacts satisfy the independent full64 set-bit
cardinality modulo two contract, with unsigned low32 results and original
caller resources. Each certificate retains its own compiler's semantic proof. -/
theorem acceptedParityCertificates :
    Nonempty (Certificate .parity64
      (V1.ParityWindows.file .defaultGCC) V1.ParityWindows.name) ∧
    Nonempty (Certificate .parity64
      (V1.ParityWindows.file .defaultClang) V1.ParityWindows.name) :=
  ⟨⟨V1.ParityCertificates.gcc_certificate⟩,
    ⟨V1.ParityCertificates.clang_certificate⟩⟩

/-- The registered rotation task binds the full input word and unsigned low32
count to independent bit origins, at both unchanged named final-file extents. -/
theorem acceptedRotationCertificates :
    Nonempty (Certificate .rotateLeft64
      (V1.RotationWindows.file .defaultGCC) V1.RotationWindows.name) ∧
    Nonempty (Certificate .rotateLeft64
      (V1.RotationWindows.file .defaultClang) V1.RotationWindows.name) :=
  ⟨⟨V1.RotationCertificates.gcc_certificate⟩,
    ⟨V1.RotationCertificates.clang_certificate⟩⟩

-- Keep successful CLI stdout machine-readable, while rejecting an unapproved
-- transitive certificate dependency before main can run. The verification gate
-- additionally audits the full imported EDSL namespace and fresh-replays it.
run_cmd do
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  for family in #[``EDSL.Corpus.Reporting.acceptedCertificates,
      ``EDSL.Corpus.Reporting.acceptedConcurrentCertificates,
      ``EDSL.Corpus.Reporting.acceptedBufferCertificates,
      ``EDSL.Corpus.Reporting.acceptedIndexSearchCertificates,
      ``EDSL.Corpus.Reporting.acceptedByteComparisonCertificates,
      ``EDSL.Corpus.Reporting.acceptedUnaryCertificates,
      ``EDSL.Corpus.Reporting.acceptedPopcountCertificates,
      ``EDSL.Corpus.Reporting.acceptedAverageCertificates,
      ``EDSL.Corpus.Reporting.acceptedParityCertificates,
      ``EDSL.Corpus.Reporting.acceptedRotationCertificates] do
    for dependency in ← Lean.collectAxioms family do
      unless allowed.contains dependency do
        throwError "Corpus certificate family {family} depends on unapproved axiom {dependency}"

end EDSL.Corpus.Reporting

/- Runtime IO observes supplied files. Its output does not prove native OS
startup, physical hardware correspondence, source preservation or future file
immutability. Proof authority remains the typed, audited imported family. -/
namespace CorpusV1Reporting
open EDSL EDSL.X86 Lean

private structure Request where
  gcc : System.FilePath := "corpus/v1/gcc/final.elf"
  clang : System.FilePath := "corpus/v1/clang/final.elf"

private def pathValue (value : String) : Bool :=
  !value.isEmpty && !value.startsWith "--"

private def parseArguments : List String → Option Request
  | [] => some {}
  | ["--gcc", gcc] => if pathValue gcc then some { gcc := gcc } else none
  | ["--clang", clang] => if pathValue clang then some { clang := clang } else none
  | ["--gcc", gcc, "--clang", clang] =>
    if pathValue gcc && pathValue clang then some { gcc := gcc, clang := clang } else none
  | ["--clang", clang, "--gcc", gcc] =>
    if pathValue gcc && pathValue clang then some { gcc := gcc, clang := clang } else none
  | _ => none

private def compilerLabel : Corpus.V1.Comparisons.Compiler → String
  | .defaultGCC => "gcc"
  | .defaultClang => "clang"

/-- At most literal-length plus two bytes are read. A changed code byte,
metadata byte, trailing byte or length rejects identically; no hash or selected
window is used in place of complete-file equality. A short read fails closed. -/
private def matchFile (compiler : Corpus.V1.Comparisons.Compiler) (path : System.FilePath) :
    IO (Except String Nat) := do
  let literal := Corpus.V1.Comparisons.file compiler
  let length := literal.length
  IO.FS.withFile path .read fun handle => do
    let raw ← handle.read (USize.ofNat (length + 1))
    if raw.size != length then
      return .error s!"{compilerLabel compiler}: complete-file length mismatch"
    let trailing ← handle.read 1
    if !trailing.isEmpty then
      return .error s!"{compilerLabel compiler}: trailing bytes after complete literal file"
    let observed := raw.data.toList.map fun byte => BitVec.ofNat 8 byte.toNat
    if observed == literal then return .ok raw.size
    return .error s!"{compilerLabel compiler}: complete-file byte mismatch"

private def operationLabel : Corpus.V1.Comparisons.Operation → String
  | .minimum => "unsigned_minimum64"
  | .maximum => "unsigned_maximum64"

private def proofReference (compiler : Corpus.V1.Comparisons.Compiler)
    (operation : Corpus.V1.Comparisons.Operation) : String :=
  "EDSL.Corpus.V1.Comparisons.certificate " ++
    (match compiler with | .defaultGCC => "defaultGCC" | .defaultClang => "defaultClang") ++ " " ++
    (match operation with | .minimum => "minimum" | .maximum => "maximum")

private def artifactJson (compiler : Corpus.V1.Comparisons.Compiler)
    (operation : Corpus.V1.Comparisons.Operation) : Json :=
  let input := Corpus.V1.Comparisons.input compiler operation
  let symbol := String.ofList ((Corpus.Comparison.name operation).map fun byte => Char.ofNat byte.toNat)
  Json.mkObj [
    ("symbol", toJson symbol),
    ("operation", toJson (operationLabel operation)),
    ("file_offset", toJson input.function.window.offset),
    ("address", toJson input.function.window.address),
    ("size", toJson input.bytes.length),
    ("proof", toJson (proofReference compiler operation))]

private def additionJson (compiler : Corpus.V1.Comparisons.Compiler) : Json :=
  let input := Corpus.V1.ArithmeticWindows.input compiler
  let symbol := String.ofList (Corpus.V1.ArithmeticWindows.name.map fun byte => Char.ofNat byte.toNat)
  let proof := "EDSL.Corpus.V1.Arithmetic.certificate " ++
    (match compiler with | .defaultGCC => "defaultGCC" | .defaultClang => "defaultClang")
  Json.mkObj [
    ("symbol", toJson symbol),
    ("operation", toJson ("unsigned_addition_modulo64" : String)),
    ("file_offset", toJson input.function.window.offset),
    ("address", toJson input.function.window.address),
    ("size", toJson input.bytes.length),
    ("proof", toJson proof)]

private def clampJson (compiler : Corpus.V1.Comparisons.Compiler) : Json :=
  let input := Corpus.V1.Clamps.input compiler
  let symbol := String.ofList (Corpus.V1.Clamps.name.map fun byte => Char.ofNat byte.toNat)
  let proof := "EDSL.Corpus.V1.Clamps.certificate " ++
    (match compiler with | .defaultGCC => "defaultGCC" | .defaultClang => "defaultClang")
  Json.mkObj [
    ("symbol", toJson symbol),
    ("operation", toJson ("signed_clamp32" : String)),
    ("file_offset", toJson input.function.window.offset),
    ("address", toJson input.function.window.address),
    ("size", toJson input.bytes.length),
    ("proof", toJson proof)]

private def concurrentJson (compiler : Corpus.V1.Comparisons.Compiler) : Json :=
  let input := (Corpus.V1.FetchAddCertificates.certificate compiler).input
  let symbol := String.ofList (Corpus.V1.FetchAddWindows.name.map fun byte => Char.ofNat byte.toNat)
  let proof := "EDSL.Corpus.V1.FetchAddCertificates.certificate " ++
    (match compiler with | .defaultGCC => "defaultGCC" | .defaultClang => "defaultClang")
  Json.mkObj [
    ("symbol", toJson symbol),
    ("operation", toJson ("full64_fetch_add_concurrent" : String)),
    ("model", toJson Grading.ConcurrentTask.FetchAdd64.model),
    ("file_offset", toJson input.function.window.offset),
    ("address", toJson input.function.window.address),
    ("size", toJson input.bytes.length),
    ("proof", toJson proof)]

private def bufferJson (compiler : Corpus.V1.Comparisons.Compiler) : Json :=
  let input := (Corpus.V1.ByteScanCertificates.certificate compiler).input
  let symbol := String.ofList (Corpus.V1.ByteScanWindows.name.map fun byte => Char.ofNat byte.toNat)
  let proof := "EDSL.Corpus.V1.ByteScanCertificates.certificate " ++
    (match compiler with | .defaultGCC => "defaultGCC" | .defaultClang => "defaultClang")
  Json.mkObj [
    ("symbol", toJson symbol),
    ("operation", toJson ("first_bounded_nul_length" : String)),
    ("model", toJson Grading.BufferTask.model),
    ("file_offset", toJson input.function.window.offset),
    ("address", toJson input.function.window.address),
    ("size", toJson input.bytes.length),
    ("proof", toJson proof)]

private def indexSearchJson (compiler : Corpus.V1.Comparisons.Compiler)
    (operation : Corpus.V1.IndexSearchWindows.Operation) : Json :=
  let input := (Corpus.V1.IndexSearchCertificates.certificate compiler operation).input
  let symbol := String.ofList
    ((Corpus.V1.IndexSearchWindows.name operation).map fun byte => Char.ofNat byte.toNat)
  let operationLabel := match operation with
    | .byte => "first_matching_byte_index"
    | .u32 => "first_matching_u32_index"
  let proof := "EDSL.Corpus.V1.IndexSearchCertificates.certificate " ++
    (match compiler with | .defaultGCC => "defaultGCC" | .defaultClang => "defaultClang") ++
    " " ++ (match operation with | .byte => "byte" | .u32 => "u32")
  Json.mkObj [
    ("symbol", toJson symbol),
    ("operation", toJson operationLabel),
    ("model", toJson Grading.BufferTask.model),
    ("file_offset", toJson input.function.window.offset),
    ("address", toJson input.function.window.address),
    ("size", toJson input.bytes.length),
    ("proof", toJson proof)]

private def byteComparisonJson (compiler : Corpus.V1.Comparisons.Compiler) : Json :=
  let input := Corpus.V1.ByteComparisonWindows.input compiler
  let symbol := String.ofList
    (Corpus.V1.ByteComparisonWindows.name.map fun byte => Char.ofNat byte.toNat)
  let proof := "EDSL.Corpus.V1.ByteComparisonCertificates.certificate " ++
    (match compiler with | .defaultGCC => "defaultGCC" | .defaultClang => "defaultClang")
  Json.mkObj [
    ("symbol", toJson symbol),
    ("operation", toJson ("unsigned_lexicographic_bytes" : String)),
    ("model", toJson Grading.BufferTask.model),
    ("file_offset", toJson input.function.window.offset),
    ("address", toJson input.function.window.address),
    ("size", toJson input.bytes.length),
    ("proof", toJson proof)]

private def unaryJson (compiler : Corpus.V1.UnaryCode.Compiler)
    (operation : Corpus.V1.UnaryCode.Operation) : Json :=
  let input := (Corpus.V1.UnaryCertificates.certificate compiler operation).input
  let symbol := String.ofList
    ((Corpus.V1.UnaryWindows.name operation).map fun byte => Char.ofNat byte.toNat)
  let operationLabel := match operation with
    | .absSigned32 => "signed_absolute32"
    | .byteSwap64 => "byte_reverse64"
  let proof := "EDSL.Corpus.V1.UnaryCertificates.certificate " ++
    (match compiler with | .defaultGCC => "defaultGCC" | .defaultClang => "defaultClang") ++
    " " ++ (match operation with | .absSigned32 => "absSigned32" | .byteSwap64 => "byteSwap64")
  Json.mkObj [
    ("symbol", toJson symbol),
    ("operation", toJson operationLabel),
    ("file_offset", toJson input.function.window.offset),
    ("address", toJson input.function.window.address),
    ("size", toJson input.bytes.length),
    ("proof", toJson proof)]

private def popcountJson (compiler : Corpus.V1.PopcountCode.Compiler) : Json :=
  let input := (Corpus.V1.PopcountCertificates.certificate compiler).input
  let proof := "EDSL.Corpus.V1.PopcountCertificates.certificate " ++
    (match compiler with | .defaultGCC => "defaultGCC" | .defaultClang => "defaultClang")
  Json.mkObj [
    ("symbol", toJson ("c_popcount_loop" : String)),
    ("operation", toJson ("population_count64" : String)),
    ("file_offset", toJson input.function.window.offset),
    ("address", toJson input.function.window.address),
    ("size", toJson input.bytes.length),
    ("proof", toJson proof)]

private def averageJson (compiler : Corpus.V1.AverageCode.Compiler) : Json :=
  let input := (Corpus.V1.AverageCertificates.certificate compiler).input
  let proof := "EDSL.Corpus.V1.AverageCertificates.certificate " ++
    (match compiler with | .defaultGCC => "defaultGCC" | .defaultClang => "defaultClang")
  Json.mkObj [
    ("symbol", toJson ("c_average_u64" : String)),
    ("operation", toJson ("unsigned_floor_average64" : String)),
    ("file_offset", toJson input.function.window.offset),
    ("address", toJson input.function.window.address),
    ("size", toJson input.bytes.length),
    ("proof", toJson proof)]

private def parityJson (compiler : Corpus.V1.ParityCode.Compiler) : Json :=
  let input := (Corpus.V1.ParityCertificates.certificate compiler).input
  let symbol := String.ofList
    (Corpus.V1.ParityWindows.name.map fun byte => Char.ofNat byte.toNat)
  let proof := "EDSL.Corpus.V1.ParityCertificates.certificate " ++
    (match compiler with | .defaultGCC => "defaultGCC" | .defaultClang => "defaultClang")
  Json.mkObj [
    ("symbol", toJson symbol),
    ("operation", toJson ("parity64" : String)),
    ("file_offset", toJson input.function.window.offset),
    ("address", toJson input.function.window.address),
    ("size", toJson input.bytes.length),
    ("proof", toJson proof)]

private def rotationJson (compiler : Corpus.V1.RotationCode.Compiler) : Json :=
  let input := (Corpus.V1.RotationCertificates.certificate compiler).input
  let symbol := String.ofList
    (Corpus.V1.RotationWindows.name.map fun byte => Char.ofNat byte.toNat)
  let proof := "EDSL.Corpus.V1.RotationCertificates.certificate " ++
    (match compiler with | .defaultGCC => "defaultGCC" | .defaultClang => "defaultClang")
  Json.mkObj [
    ("symbol", toJson symbol),
    ("operation", toJson ("rotate_left64" : String)),
    ("file_offset", toJson input.function.window.offset),
    ("address", toJson input.function.window.address),
    ("size", toJson input.bytes.length),
    ("proof", toJson proof)]

private def certificateRows (compiler : Corpus.V1.Comparisons.Compiler) : Array Json :=
  #[artifactJson compiler .minimum, artifactJson compiler .maximum,
    additionJson compiler, clampJson compiler, concurrentJson compiler, bufferJson compiler,
    indexSearchJson compiler .byte, indexSearchJson compiler .u32,
    byteComparisonJson compiler, unaryJson compiler .absSigned32,
    unaryJson compiler .byteSwap64, popcountJson compiler, averageJson compiler,
    parityJson compiler, rotationJson compiler]

private def fileJson (compiler : Corpus.V1.Comparisons.Compiler) (path : System.FilePath)
    (bytes : Nat) : Json := Json.mkObj [
  ("compiler", toJson (compilerLabel compiler)),
  ("path", toJson path.toString),
  ("bytes", toJson bytes),
  ("match", toJson ("complete_byte_equality" : String)),
  ("certificates", Json.arr (certificateRows compiler))]

private def recordedProfile : Bool :=
  let profile := EDSL.X86.VCGen.CompilerComparisons.targetProfile
  profile.longMode && !profile.ibtEnabled && !profile.shadowStackEnabled && profile.multiByteNop

private def report (request : Request) (gccBytes clangBytes : Nat) : Json :=
  let profile := EDSL.X86.VCGen.CompilerComparisons.targetProfile
  let artifacts := (certificateRows .defaultGCC ++ certificateRows .defaultClang).toList
  let symbols := artifacts.filterMap fun artifact =>
    (artifact.getObjValAs? String "symbol").toOption
  let concurrentSymbols := artifacts.filterMap fun artifact =>
    if (artifact.getObjValAs? String "operation").toOption == some "full64_fetch_add_concurrent" then
      (artifact.getObjValAs? String "symbol").toOption
    else none
  Json.mkObj [
    ("schema", toJson ("edsl.compiler-corpus.certificates.v1" : String)),
    ("status", toJson ("certified_under_recorded_model_assumptions" : String)),
    ("score", Json.mkObj [
      ("functions_certified_end_to_end", toJson symbols.eraseDups.length),
      ("functions_total", toJson (40 : Nat)),
      ("compiler_artifacts_certified_end_to_end", toJson artifacts.length),
      ("compiler_artifacts_total", toJson (80 : Nat)),
      ("concurrency_contracts_proved", toJson concurrentSymbols.eraseDups.length)]),
    ("stages", Json.mkObj [
      ("complete_file_identity", toJson ("both supplied files equal every accepted literal byte" : String)),
      ("elf_symbol_binding", toJson ("kernel-checked complete-file metadata, unique named extents and LOAD layout" : String)),
      ("cfg", toJson ("scalar shared checked graphs; concurrent checked code-family proof; diagnostic CFG admission is a separate metric" : String)),
      ("symbolic_vc", toJson ("scalar shared sound VC-generation proofs; concurrent independent managed contract from the checked instruction family" : String)),
      ("registered_semantics", toJson ("unsigned minimum/maximum, addition modulo 2^64 and signed low32 interval clamp with lower <= upper and arbitrary argument upper halves, for every admitted resource call and every AF stream" : String)),
      ("unary_semantics", toJson ("signed low32 absolute value is nonnegative with the same mathematical square, excludes INT32_MIN and permits arbitrary argument upper halves; full64 reversal of all eight base-256 digits; every admitted resource call and every AF stream" : String)),
      ("population_count_semantics", toJson ("full64 input bit-position cardinality returned as unsigned low32; all inputs including zero and all-ones admitted; every AF stream terminates by strict remaining-cardinality rank, with complete RAM and original caller resources retained at every prefix and return; ABI and result established at return" : String)),
      ("parity_semantics", toJson ("independent full64 input bit-position cardinality modulo 2 returned as unsigned low32; all full64 words including zero and all-ones admitted; upper32 RAX unconstrained; useful endpoint witness 0x8000000000000001 does not restrict the domain; every AF stream terminates by strict unsigned remainder rank; complete RAM and permissions, original caller and current code authority retained at every prefix and return; ABI and result established at return; no physical/OS/compiler refinement or minimum-cost claim" : String)),
      ("rotation_semantics", toJson ("independent full64 bit-origin left rotation by unsigned low32 RSI modulo 64; all full64 RDI values and all low32 counts admitted, with arbitrary upper32 RSI; every independent undefined-flag choice stream terminates; zero count retains all flags, one count defines OF, larger counts permit either OF; complete RAM and permissions, original caller and current code authority retained at every prefix and return; ABI and result established at return" : String)),
      ("rotation_progress", toJson ("exact retired model instructions including RET and GCC ENDBR64: rotation GCC 5, Clang 4; universal decoded-execution observations; no physical timing or minimum-cost claim" : String)),
      ("average_semantics", toJson ("full64 RDI/RSI inputs; unsigned floor of the unbounded natural input sum divided by two; all full64 pairs including overflowing input sums admitted; every AF stream terminates; complete RAM and original caller resources retained at every prefix and return; ABI and result established at return" : String)),
      ("average_progress", toJson ("exact retired model instructions including RET and GCC ENDBR64: average GCC 7, Clang 6; universal decoded-execution observations; no physical timing or minimum-cost claim" : String)),
      ("unary_progress", toJson ("exact retired model instructions including RET and GCC ENDBR64: absolute value GCC 5, Clang 4; byte reversal GCC 4, Clang 3; no physical timing or minimum-cost claim" : String)),
      ("buffer_semantics", toJson ("first bounded NUL length for arbitrary admitted byte snapshots with n < 2^64; all AF streams terminate by dynamic rank; original caller, full RAM and every-prefix read authority retained; n=0 requires no data loan or pointer validity" : String)),
      ("index_search_semantics", toJson ("earliest matching byte or little-endian u32 index, or full64 SIZE_MAX when absent, for arbitrary admitted snapshots with n < 2^64; low8/low32 search key permits arbitrary upper bits; all AF streams terminate by dynamic rank; original caller, full RAM, ABI and every-prefix current read authority retained; n=0 requires no data loan or pointer validity" : String)),
      ("byte_comparison_semantics", toJson ("signed low32 C-int return sign agrees with independent unsigned-byte List.Lex on arbitrary equal-length complete snapshots with n < 2^64; full64 RDI/RSI/RDX bind both pointers and count; actual DATA1 reads stay within the two exact input spans; compatible overlapping, identical, unaligned, code and caller aliases admitted; n=0 ignores both pointers and input-loan selectors, needs no DATA loan and performs no DATA read" : String)),
      ("byte_comparison_resources", toJson ("complete RAM and permissions, ABI frames and nonarithmetic flags, current code, original caller and both nonempty input loans retained at every prefix and return" : String)),
      ("byte_comparison_progress", toJson ("all AF streams terminate by dynamic rank; 9*(n+2) is a proved output upper bound on retired model instructions, with no physical cost or minimum-cost claim" : String)),
      ("concurrent_semantics", toJson ("managed CLOSED-COHORT current-only ABI admission with arbitrary full64 initial values and deltas; every successful finite returned schedule has independent legal modulo-counter histories and exact selected RMW/call occurrence coverage" : String)),
      ("concurrent_progress", toJson ("every successful finite prefix preserves safety and current authority; every running context has an enabled actual issue for every AF value; global completion exists and a positive own-issue bound is proved as output" : String)),
      ("concurrent_resources", toJson ("represented return continuation, callee-save registers, stack, DF and collect; original resources and byte frames outside the selected cell; full installed ELF retained under current authority" : String)),
      ("concurrent_useful_domain", toJson ("kernel-checked actual loaded overlapping completed execution with two useful nonzero-delta calls to the selected cell, both RMWs before the first call returns" : String)),
      ("caller_resources", toJson ("modeled current authority, actual return hook, every-prefix policy and ABI contract" : String)),
      ("useful_domain", toJson ("kernel-checked nonempty useful calls at each selected file address" : String)),
      ("certificate_axioms", toJson ("transitively audited at elaboration: propext, Quot.sound, Classical.choice only" : String)),
      ("native_execution", toJson ("not used as proof evidence" : String))]),
    ("profile", Json.mkObj [
      ("long_mode", toJson profile.longMode),
      ("cet_ibt_enabled", toJson profile.ibtEnabled),
      ("shadow_stack_enabled", toJson profile.shadowStackEnabled),
      ("multi_byte_nop", toJson profile.multiByteNop),
      ("status", toJson ("recorded model assumptions; native configuration is not checked" : String))]),
    ("files", Json.arr #[fileJson .defaultGCC request.gcc gccBytes,
      fileJson .defaultClang request.clang clangBytes]),
    ("limits", toJson ([
      "Stable modeled RAM, retained checked executable text and the registered caller/resource assumptions are required.",
      "The useful witness declares a new modeled ownership world; it does not authenticate preexisting native authority.",
      "No source/IR preservation, physical CPU refinement, CET-enabled execution or native Linux startup is proved.",
      "Dynamic linker, relocation, TLS and external calls receive no certificate here; asynchronous interference and concurrency outside the fixed managed closed cohort/profile are unsupported.",
      "Scalar certificates retain their registered caller/resource assumptions and exclude concurrent interference.",
      "The concurrent result establishes only the modeled managed profile: no published physical x86-TSO refinement, Linux/GNU memory-order contract, scheduling fairness or hardware-minimum progress bound is proved.",
      "Byte comparison uses the current borrowed sequential callable profile with stable ordinary RAM, absent asynchronous interference and CET off; no source/LLVM preservation, native Linux behavior or concurrent-buffer claim is proved.",
      "The report concerns bytes observed in this read, not future filesystem or process mappings.",
      "Fresh kernel replay is a separate verification-gate step; this IO command is not a physical OS proof."
    ] : List String))]

def run (arguments : List String) : IO UInt32 := do
  let some request := parseArguments arguments | do
    (← IO.getStderr).putStrLn "usage: lean --run corpus/Certify.lean [--gcc FILE] [--clang FILE]"
    return 2
  try
    if !recordedProfile then
      (← IO.getStderr).putStrLn "CORPUS-CERTIFICATES-REJECTED: unsupported recorded target profile"
      return 1
    match ← matchFile .defaultGCC request.gcc with
    | .error reason =>
      (← IO.getStderr).putStrLn s!"CORPUS-CERTIFICATES-REJECTED: {reason}; no certificate report"
      return 1
    | .ok gccBytes =>
      match ← matchFile .defaultClang request.clang with
      | .error reason =>
        (← IO.getStderr).putStrLn s!"CORPUS-CERTIFICATES-REJECTED: {reason}; no certificate report"
        return 1
      | .ok clangBytes =>
        (← IO.getStdout).putStrLn ((report request gccBytes clangBytes).compress)
        return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"CORPUS-CERTIFICATES-IO-FAILED: {error}; no certificate report"
    return 3

end CorpusV1Reporting

def main (arguments : List String) : IO UInt32 := CorpusV1Reporting.run arguments
