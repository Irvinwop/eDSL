/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.AtomicSet64.Driver
import EDSL.Grading.Export
import EDSL.Audit

/-! Controller integration checks use independently supplied literal machine
bytes and fresh serialized client proofs. The client module is dynamically
loaded only by the exporter; it is absent from the grader's fixed snapshot.
All successful grading uses the unchanged runtime defaults. -/
namespace EDSL.Tests.AtomicSet64GradingPackets
open Lean EDSLGrader EDSLGrader.Runtime

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (context : String) (result : Except Failure α) : IO α :=
  match result with
  | .ok value => pure value
  | .error failure => throw (IO.userError s!"{context}: {failure}")

/-- Independent submissions use independent threads, as separate CLI processes
do. A complete grade (packet plus wrapper) stays on one thread and retains its
one cumulative ceiling. No counter is reset during a submission. -/
private def submission (action : Unit → Except Failure α) : IO (Except Failure α) := do
  let task ← IO.asTask (IO.lazyPure action) Task.Priority.dedicated
  match task.get with
  | .ok result => return result
  | .error error => throw error

private def reject (context : String) (kind : FailureKind)
    (result : Except Failure α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"{context}: unexpectedly accepted")
  | .error failure => require (failure.kind == kind)
      s!"{context}: wrong failure category: {failure}"

/-- Independent ELF64LE ET_EXEC with one RX, file-backed entry window.
The code starts at file offset 128 and virtual address 0x400080. -/
private def elfFile (code : List X86.Byte) : List X86.Byte :=
  let header := Grading.Hex.literal (
    "7f454c46020101000000000000000000" ++
    "02003e00010000008000400000000000" ++
    "40000000000000000000000000000000" ++
    "00000000400038000100000000000000" ++
    "01000000050000008000000000000000" ++
    "80004000000000000000000000000000" ++
    "00000000000000000000000000000000" ++
    "00100000000000000000000000000000")
  (header.set 96 (BitVec.ofNat 8 code.length)).set 104 (BitVec.ofNat 8 code.length) ++ code

private def checkCodePacket (trusted client : Kernel.Environment)
    (desired wrongTask : Logical64.Operation) (code : List X86.Byte) (name : Name) :
    IO Export.Packet := do
  let packet ← unwrap s!"export {name}" (Export.exportTheorem trusted client name)
  let accepted ← unwrap s!"grade {name}"
    (← submission fun _ => EDSLGrader.AtomicSet64.grade trusted {} desired (.raw code) packet.text)
  require (accepted.kernelChecks > 2)
    "client proof did not reconstruct a fresh helper closure and artifact wrapper"
  reject s!"{name}: different desired operation" .rejected
    (← submission fun _ => EDSLGrader.AtomicSet64.grade trusted {} wrongTask (.raw code) packet.text)
  -- Returning before the extra byte is allowed by execution; nevertheless the
  -- old theorem must not bind a different complete selected byte list.
  reject s!"{name}: appended selected byte" .rejected
    (← submission fun _ => EDSLGrader.AtomicSet64.grade trusted {} desired (.raw (code ++ [0x90])) packet.text)
  IO.println s!"PASS {name}: default-budget acceptance; crossed desired task and selected bytes rejected"
  return packet

/-- A wrapper theorem is a different proposition from the packet's required
code Claim. Reconstructing it as checked data must not bypass that boundary. -/
private def rejectWrapperPacket (trusted : Kernel.Environment) (code : List X86.Byte)
    (packet : Export.Packet) : IO Unit := do
  let operation := mkConst ``Logical64.Operation.union
  let bytes := toExpr code
  let literal := mkApp (mkConst ``Grading.Artifact.raw) bytes
  let selection := mkApp2 (mkConst ``Eq.refl [Level.one])
    (toTypeExpr (Option (List X86.Byte))) (toExpr (some code))
  let wrapperType := mkApp2 (mkConst ``Grading.AtomicSet64.Artifact.Claim) operation literal
  let wrapperValue := mkAppN (mkConst ``Grading.AtomicSet64.Artifact.certify)
    #[operation, literal, bytes, selection, packet.value]
  let wrapperName := `AtomicSet64PacketFixture.literalWrapper
  let wrapper := Declaration.thmDecl {
    name := wrapperName, levelParams := [], type := wrapperType, value := wrapperValue }
  let data ← unwrap "encode wrapper packet"
    (encodePacket (packet.declarations ++ [wrapper]) (mkConst wrapperName))
  reject "artifact theorem substituted for code theorem" .rejected
    (← submission fun _ => EDSLGrader.AtomicSet64.grade trusted {} .union (.raw code) data)
  -- The final literal-artifact statement itself must also distinguish changed
  -- code. This expected type uses standard quotation, independently of the
  -- controller's balanced literal renderer.
  let checked ← unwrap "reconstruct wrapper prerequisites"
    (← submission fun _ => checkPacket trusted {}
      (EDSLGrader.AtomicSet64.expectedClaim .union code) packet.text)
  let changed := mkApp (mkConst ``Grading.Artifact.raw) (toExpr (code.set 2 0x31))
  let expected := mkApp2 (mkConst ``Grading.AtomicSet64.Artifact.Claim) operation changed
  reject "literal wrapper for different code" .rejected
    (← submission fun _ => checkExpr checked.env {} expected wrapperValue `EDSLGrader.Internal.set64WrongWrapper)
  let file := elfFile code
  let originalELF := mkApp2 (mkConst ``Grading.Artifact.elf) (toExpr file) (toExpr (5 : Nat))
  let elfValue := mkAppN (mkConst ``Grading.AtomicSet64.Artifact.certify)
    #[operation, originalELF, bytes, selection, packet.value]
  let elfType := mkApp2 (mkConst ``Grading.AtomicSet64.Artifact.Claim) operation originalELF
  let _ ← unwrap "original full-artifact proof"
    (← submission fun _ => checkExpr checked.env {} elfType elfValue `EDSLGrader.Internal.set64OriginalELF)
  let changedELF := mkApp2 (mkConst ``Grading.Artifact.elf)
    (toExpr (file.set 7 3)) (toExpr (5 : Nat))
  let changedType := mkApp2 (mkConst ``Grading.AtomicSet64.Artifact.Claim) operation changedELF
  reject "stale full-artifact proof after nonloaded metadata change" .rejected
    (← submission fun _ => checkExpr checked.env {} changedType elfValue `EDSLGrader.Internal.set64StaleELF)

def checkPackets : IO Unit := do
  let (trustedEnv, clientEnv) ← Export.loadEnvironments `tests.fixtures.AtomicSet64Grading
  let trusted := trustedEnv.toKernelEnv
  let client := clientEnv.toKernelEnv
  for (name, _) in trustedEnv.constants.toList do
    require (!(`EDSL.Tests.Fixtures.AtomicSet64Grading).isPrefixOf name)
      s!"client/helper imported into trusted snapshot: {name}"
  let andCode : List X86.Byte := [0xf0, 0x48, 0x21, 0x37, 0xc3]
  let orCode : List X86.Byte := [0xf0, 0x48, 0x09, 0x37, 0xc3]
  let xorCode : List X86.Byte := [0xf0, 0x48, 0x31, 0x37, 0xc3]
  let _ ← checkCodePacket trusted client .intersection .union andCode
    `EDSL.Tests.Fixtures.AtomicSet64Grading.claimAnd
  let union ← checkCodePacket trusted client .union .symmetricDifference orCode
    `EDSL.Tests.Fixtures.AtomicSet64Grading.claimOr
  let _ ← checkCodePacket trusted client .symmetricDifference .intersection xorCode
    `EDSL.Tests.Fixtures.AtomicSet64Grading.claimXor
  reject "OR proof for XOR opcodes" .rejected
    (← submission fun _ => EDSLGrader.AtomicSet64.grade trusted {} .union (.raw xorCode) union.text)
  let bare ← unwrap "encode bare unknown client reference"
    (encodePacket [] (mkConst `EDSL.Tests.Fixtures.AtomicSet64Grading.claimOr))
  reject "client reference without serialized closure" .malformed
    (← submission fun _ => EDSLGrader.AtomicSet64.grade trusted {} .union (.raw orCode) bare)
  -- This valid v1 proof has the wrong proposition, so version admission must
  -- reach kernel rejection. Fresh helper closures use the compact v2 format.
  let legacy ← unwrap "encode legacy packet" (encodeTreePacket [] (mkConst ``True.intro))
  reject "legacy packet with different proposition" .rejected
    (← submission fun _ => EDSLGrader.AtomicSet64.grade trusted {} .union (.raw orCode) legacy)
  rejectWrapperPacket trusted orCode union

  let file := elfFile orCode
  let _ ← unwrap "full literal ELF wrapper"
    (← submission fun _ => EDSLGrader.AtomicSet64.grade trusted {} .union (.elf file 5) union.text)
  -- ELF OSABI 0 and 3 are independently valid. The same code proof must work
  -- after the complete file changes; the controller checks a new wrapper.
  let _ ← unwrap "changed valid nonloaded ELF metadata"
    (← submission fun _ => EDSLGrader.AtomicSet64.grade trusted {} .union (.elf (file.set 7 3) 5) union.text)
  reject "ELF selected-byte mutation" .rejected
    (← submission fun _ => EDSLGrader.AtomicSet64.grade trusted {} .union (.elf (file.set 130 0x31) 5) union.text)
  reject "ELF window extends beyond file backing" .unsupported
    (← submission fun _ => EDSLGrader.AtomicSet64.grade trusted {} .union (.elf file 6) union.text)
  -- Requested union is deliberately different from the first two opcodes.
  -- All three real operations survive in the client execution proof.
  let mixed : List X86.Byte := [0xf0, 0x48, 0x31, 0x37, 0xf0, 0x48, 0x31, 0x37,
    0xf0, 0x48, 0x09, 0x37, 0xc3]
  for mode in [Export.Mode.reference, .body] do
    let packet ← unwrap "export mixed union"
      (Export.exportTheorem trusted client
        `EDSL.Tests.Fixtures.AtomicSet64Grading.claimMixedUnion mode)
    let accepted ← unwrap "mixed-opcode desired union"
      (← submission fun _ => EDSLGrader.AtomicSet64.grade trusted {} .union (.raw mixed) packet.text)
    require (accepted.kernelChecks > 2) "mixed proof omitted checked helper reconstruction"
    reject "mixed union falsely offered as symmetric difference" .rejected
      (← submission fun _ => EDSLGrader.AtomicSet64.grade trusted {} .symmetricDifference (.raw mixed) packet.text)
  IO.println "PASS atomic set packets: default-budget desired task/bytes, fresh helpers, literal wrappers, raw/ELF and mixed uninterrupted union; legacy proposition rejection"

#eval checkPackets

end EDSL.Tests.AtomicSet64GradingPackets

#print axioms EDSL.Grading.AtomicSet64.Artifact.certify
#audit_edsl
