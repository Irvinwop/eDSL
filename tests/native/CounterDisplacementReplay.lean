/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.native.RegisterCapture
import EDSL.X86.Sequential.Address32
import EDSL.X86.Sequential.TestImmediate8

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.CounterDisplacementReplay
open X86 X86.Sequential RegisterCapture

/- One family validator for any future client of these instructions. Probe
metadata is a literal contract, not a decoder/encoder or alternate executor.
All claimed model behavior is checked with public production decodeAt/step.
Physical snapshots cover only selectedRegisters. Synthetic canaries and RAM
maps plus universal fullRAMFrame/fullRAMAt remain MODEL frame challenges.
PUSHFQ RF/VM masking, AC/DF/debug/ordinary-RAM/CET target limits remain explicit;
finite observations do not establish universal physical ISA or OS refinement. -/
def selectedRegisters : List Register :=
  [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.r8,.r9,.r12,.r13,.r15]

inductive AddressForm where
  | base | indexed | baseDisp8 | sibDisp8
  deriving BEq, DecidableEq, Inhabited

structure Probe where
  name : String
  kind : Nat -- 0 ADD32, 1 INC32, 2 LEA64, 3 SUB32, 4 CMP32, 5 LEA32, 6 TEST-low8
  destination : Register
  base : Register
  index : Option Register
  scale : Fin 4
  immediate : Byte
  prefixed : Bool
  addressForm : AddressForm
  code : List Byte

instance : Inhabited Probe := ⟨⟨"",0,.rax,.rax,none,0,0,false,.base,[]⟩⟩

/-- Declared address syntax, never inferred from opcode bytes or length. -/
def Probe.address (p : Probe) : Address :=
  match p.addressForm with
  | .base => .base p.base
  | .indexed => .indexed p.base (p.index.getD .rax) p.scale
  | .baseDisp8 => .baseDisp8 p.base p.immediate
  | .sibDisp8 => .sibDisp8 p.base p.index p.scale p.immediate

def Probe.afPolicy (p : Probe) : AFPolicy :=
  if p.kind == 6 then .undefinedAF else .exact

/-- Schema/admission checks; writing live RSP is always forbidden. -/
def Probe.metadataOK (p : Probe) : Bool :=
  p.kind < 7 && selectedRegisters.contains p.destination &&
  (p.destination != .rsp || p.kind == 6) &&
  if p.kind == 2 || p.kind == 5 then
    selectedRegisters.contains p.base &&
    (match p.index with
      | none => true
      | some index => selectedRegisters.contains index && index != .rsp) &&
    (p.kind != 2 || (p.prefixed &&
      (p.addressForm == .baseDisp8 || p.addressForm == .sibDisp8))) &&
    match p.addressForm with
    | .base => p.index.isNone && p.scale.val == 0 && p.immediate == 0 &&
        p.base != .rsp && p.base != .r12 && p.base != .rbp && p.base != .r13
    | .indexed => p.index.isSome && p.immediate == 0 && p.base != .rbp && p.base != .r13
    | .baseDisp8 => p.index.isNone && p.scale.val == 0 && p.base != .rsp && p.base != .r12
    | .sibDisp8 => true
  else p.addressForm == .base && p.base == .rax && p.index.isNone &&
    p.scale.val == 0 && (p.kind != 1 || p.immediate == 1)

def Probe.instruction (p : Probe) : Sequential.Instruction :=
  if p.kind == 0 then .addImm32 p.destination p.immediate p.prefixed
  else if p.kind == 1 then .inc32 p.destination p.prefixed
  else if p.kind == 3 then .subImm32 p.destination p.immediate p.prefixed
  else if p.kind == 4 then .cmpImm32 p.destination p.immediate p.prefixed
  else if p.kind == 5 then .lea32 p.destination p.address p.prefixed
  else if p.kind == 6 then .testImm8 p.destination p.immediate p.prefixed
  else .lea64 p.destination p.address

structure Row where
  probe : Probe
  capture : Capture
  seed : Nat
  deriving Inhabited

def signedByte (b : Byte) : Int :=
  if b.toNat < 128 then Int.ofNat b.toNat else Int.ofNat b.toNat - 256

def input (r : Row) (register : Register) : Word :=
  registers selectedRegisters r.capture.before register

/-- Signed wide sum from full64 PRESTATE inputs. This does not use Address.eval.
Noncanonical/unmapped source values impose no data-access requirement. -/
def mathematicalAddress (r : Row) : Int :=
  Int.ofNat (input r r.probe.base).toNat +
    (match r.probe.index with
      | none => 0
      | some index => Int.ofNat (input r index).toNat * Int.ofNat (2 ^ r.probe.scale.val)) +
    (if r.probe.addressForm == .baseDisp8 || r.probe.addressForm == .sibDisp8 then
      signedByte r.probe.immediate else 0)

/-- Arithmetic byte intersection, independent of bitwise/model flag helpers.
The immediate is raw unsigned8, including its bit7. -/
def mathematicalByteIntersection (r : Row) : Nat :=
  let x := (input r r.probe.destination).toNat % 256
  let mask := r.probe.immediate.toNat
  (List.range 8).foldl (fun total i =>
    total + 2^i * ((x / 2^i) % 2) * ((mask / 2^i) % 2)) 0

/-- Independent low32 arithmetic, including the difference used only for CMP
flags. No model arithmetic, execution or flag API is used. -/
def mathematicalALUResult (r : Row) : Word :=
  let x := (input r r.probe.destination).toNat % 4294967296
  let y := if r.probe.kind == 1 then 1 else signedByte r.probe.immediate
  let result := if r.probe.kind == 3 || r.probe.kind == 4 then Int.ofNat x - y
    else Int.ofNat x + y
  BitVec.ofInt 64 (result % 4294967296)

/-- Independent modular mathematical register result, with prestate operands.
CMP/TEST preserve the entire operand, including its high32 bits. -/
def mathematicalResult (r : Row) : Word :=
  if r.probe.kind == 2 then BitVec.ofInt 64 (mathematicalAddress r)
  else if r.probe.kind == 5 then BitVec.ofInt 64 (mathematicalAddress r % 4294967296)
  else if r.probe.kind == 4 || r.probe.kind == 6 then input r r.probe.destination
  else mathematicalALUResult r

/-- Six arithmetic predicates independently defined in Nat/Int: unsigned
carry/borrow, signed overflow, low-nibble carry/borrow, even low-byte parity,
zero and sign. CMP flags use the difference even though its GPR is unchanged.
INC uses incoming CF, including on wrap. All other saved bits are compared. -/
def mathematicalFlags (r : Row) : Word :=
  if r.probe.kind == 2 || r.probe.kind == 5 then r.capture.flagsBefore
  else if r.probe.kind == 6 then
    let output := mathematicalByteIntersection r
    let bits := (List.range 8).foldl (fun total i => total + (output / 2^i) % 2) 0
    let status := (if bits % 2 == 0 then 4 else 0) +
      (if output == 0 then 64 else 0) + (if output ≥ 128 then 128 else 0)
    -- CF=OF=0, AF normalized to zero; all saved nonarithmetic bits exact.
    (r.capture.flagsBefore &&& ~~~UnaryReplay.arithmeticMask) ||| BitVec.ofNat 64 status
  else
    let x := (input r r.probe.destination).toNat % 4294967296
    let y := if r.probe.kind == 1 then 1 else signedByte r.probe.immediate
    let unsignedY := (y % 4294967296).toNat
    let signedX : Int := if x < 2147483648 then Int.ofNat x else Int.ofNat x - 4294967296
    let subtraction := r.probe.kind == 3 || r.probe.kind == 4
    let signedResult := if subtraction then signedX - y else signedX + y
    let output := (mathematicalALUResult r).toNat
    let bits := (List.range 8).foldl (fun total i => total + (output / 2^i) % 2) 0
    let cf := if r.probe.kind == 1 then r.capture.flagsBefore.toNat % 2 == 1
      else if subtraction then decide (x < unsignedY)
      else decide (x + unsignedY ≥ 4294967296)
    let af := if subtraction then decide (x % 16 < unsignedY % 16)
      else decide (x % 16 + unsignedY % 16 ≥ 16)
    let status := (if cf then 1 else 0) + (if bits % 2 == 0 then 4 else 0) +
      (if af then 16 else 0) +
      (if output == 0 then 64 else 0) + (if output ≥ 2147483648 then 128 else 0) +
      (if signedResult < -2147483648 ∨ signedResult > 2147483647 then 2048 else 0)
    (r.capture.flagsBefore &&& ~~~UnaryReplay.arithmeticMask) ||| BitVec.ofNat 64 status

def independentCheck (r : Row) : Bool :=
  r.probe.metadataOK && r.capture.code == r.probe.code &&
  r.capture.before.length == 11 && r.capture.after.length == 11 && r.seed < 4 &&
  r.capture.flagsBefore &&& UnaryReplay.arithmeticMask ==
    (UnaryReplay.seedFlags[r.seed]?).getD 0 &&
  r.capture.flagsBefore &&& 0x40500 == 0 && r.capture.flagsBefore &&& 2 == 2 &&
  (r.capture.flagsBefore ||| r.capture.flagsAfter) &&& 0x30000 == 0 &&
  input r .rsp != 0 && (input r .rsp).toNat % 8 == 0 &&
  registers selectedRegisters r.capture.after r.probe.destination == mathematicalResult r &&
  selectedRegisters.all (fun register => if register = r.probe.destination then true
    else registers selectedRegisters r.capture.after register == input r register) &&
  (match r.probe.afPolicy with
    | .exact => r.capture.flagsAfter == mathematicalFlags r
    | .undefinedAF => r.capture.flagsAfter &&& ~~~(0x10 : Word) == mathematicalFlags r)

def check (r : Row) : Bool :=
  independentCheck r && RegisterCapture.checkWithAF selectedRegisters r.capture
    r.probe.instruction r.probe.afPolicy

private def register (n : Nat) : IO Register := do
  let some r := UnaryReplay.allRegisters[n]? | throw (IO.userError "invalid register number")
  return r

/-- Required literal name/metadata/byte keys. This is an admission inventory,
not a decoder or expected-result generator. It is never learned from a run. -/
private def requiredProbeKeys : List String :=
  ["add_eax_80\t0\t0\t0\t16\t0\t128\t0\t0\t83c080",
   "add_eax_ff\t0\t0\t0\t16\t0\t255\t0\t0\t83c0ff",
   "add_eax_00\t0\t0\t0\t16\t0\t0\t0\t0\t83c000",
   "add_eax_01\t0\t0\t0\t16\t0\t1\t0\t0\t83c001",
   "add_eax_7f\t0\t0\t0\t16\t0\t127\t0\t0\t83c07f",
   "add_ecx_80\t0\t1\t0\t16\t0\t128\t0\t0\t83c180",
   "add_ecx_ff\t0\t1\t0\t16\t0\t255\t0\t0\t83c1ff",
   "add_ecx_00\t0\t1\t0\t16\t0\t0\t0\t0\t83c100",
   "add_ecx_01\t0\t1\t0\t16\t0\t1\t0\t0\t83c101",
   "add_ecx_7f\t0\t1\t0\t16\t0\t127\t0\t0\t83c17f",
   "add_eax40_80\t0\t0\t0\t16\t0\t128\t1\t0\t4083c080",
   "add_eax40_ff\t0\t0\t0\t16\t0\t255\t1\t0\t4083c0ff",
   "add_eax40_00\t0\t0\t0\t16\t0\t0\t1\t0\t4083c000",
   "add_eax40_01\t0\t0\t0\t16\t0\t1\t1\t0\t4083c001",
   "add_eax40_7f\t0\t0\t0\t16\t0\t127\t1\t0\t4083c07f",
   "add_ecx40_80\t0\t1\t0\t16\t0\t128\t1\t0\t4083c180",
   "add_ecx40_ff\t0\t1\t0\t16\t0\t255\t1\t0\t4083c1ff",
   "add_ecx40_00\t0\t1\t0\t16\t0\t0\t1\t0\t4083c100",
   "add_ecx40_01\t0\t1\t0\t16\t0\t1\t1\t0\t4083c101",
   "add_ecx40_7f\t0\t1\t0\t16\t0\t127\t1\t0\t4083c17f",
   "add_r8d_80\t0\t8\t0\t16\t0\t128\t1\t0\t4183c080",
   "add_r8d_ff\t0\t8\t0\t16\t0\t255\t1\t0\t4183c0ff",
   "add_r8d_00\t0\t8\t0\t16\t0\t0\t1\t0\t4183c000",
   "add_r8d_01\t0\t8\t0\t16\t0\t1\t1\t0\t4183c001",
   "add_r8d_7f\t0\t8\t0\t16\t0\t127\t1\t0\t4183c07f",
   "add_r9d_80\t0\t9\t0\t16\t0\t128\t1\t0\t4183c180",
   "add_r9d_ff\t0\t9\t0\t16\t0\t255\t1\t0\t4183c1ff",
   "add_r9d_00\t0\t9\t0\t16\t0\t0\t1\t0\t4183c100",
   "add_r9d_01\t0\t9\t0\t16\t0\t1\t1\t0\t4183c101",
   "add_r9d_7f\t0\t9\t0\t16\t0\t127\t1\t0\t4183c17f",
   "add_r12d_80\t0\t12\t0\t16\t0\t128\t1\t0\t4183c480",
   "add_r12d_ff\t0\t12\t0\t16\t0\t255\t1\t0\t4183c4ff",
   "add_r12d_00\t0\t12\t0\t16\t0\t0\t1\t0\t4183c400",
   "add_r12d_01\t0\t12\t0\t16\t0\t1\t1\t0\t4183c401",
   "add_r12d_7f\t0\t12\t0\t16\t0\t127\t1\t0\t4183c47f",
   "add_r13d_80\t0\t13\t0\t16\t0\t128\t1\t0\t4183c580",
   "add_r13d_ff\t0\t13\t0\t16\t0\t255\t1\t0\t4183c5ff",
   "add_r13d_00\t0\t13\t0\t16\t0\t0\t1\t0\t4183c500",
   "add_r13d_01\t0\t13\t0\t16\t0\t1\t1\t0\t4183c501",
   "add_r13d_7f\t0\t13\t0\t16\t0\t127\t1\t0\t4183c57f"] ++
  ["inc_eax\t1\t0\t0\t16\t0\t1\t0\t0\tffc0",
   "inc_ecx\t1\t1\t0\t16\t0\t1\t0\t0\tffc1",
   "inc_eax40\t1\t0\t0\t16\t0\t1\t1\t0\t40ffc0",
   "inc_ecx40\t1\t1\t0\t16\t0\t1\t1\t0\t40ffc1",
   "inc_r8d\t1\t8\t0\t16\t0\t1\t1\t0\t41ffc0",
   "inc_r9d\t1\t9\t0\t16\t0\t1\t1\t0\t41ffc1",
   "inc_r12d\t1\t12\t0\t16\t0\t1\t1\t0\t41ffc4",
   "inc_r13d\t1\t13\t0\t16\t0\t1\t1\t0\t41ffc5"] ++
  ["lea_plain_48\t2\t0\t0\t16\t0\t128\t1\t2\t488d4080",
   "lea_plain_alias\t2\t1\t1\t16\t0\t255\t1\t2\t488d49ff",
   "lea_plain_4d\t2\t8\t8\t16\t0\t0\t1\t2\t4d8d4000",
   "lea_plain_high_alias\t2\t9\t9\t16\t0\t127\t1\t2\t4d8d497f",
   "lea_plain_49\t2\t0\t13\t16\t0\t255\t1\t2\t498d45ff",
   "lea_plain_4c\t2\t13\t5\t16\t0\t128\t1\t2\t4c8d6d80",
   "lea_plain_r15\t2\t15\t3\t16\t0\t127\t1\t2\t4c8d7b7f",
   "lea_plain_rbp\t2\t2\t5\t16\t0\t0\t1\t2\t488d5500",
   "lea_plain_4a\t2\t0\t3\t16\t0\t255\t1\t2\t4a8d43ff",
   "lea_plain_4b\t2\t1\t13\t16\t0\t128\t1\t2\t4b8d4d80",
   "lea_plain_4e\t2\t15\t5\t16\t0\t127\t1\t2\t4e8d7d7f",
   "lea_plain_4f\t2\t8\t13\t16\t0\t0\t1\t2\t4f8d4500",
   "lea_sib_rsp\t2\t0\t4\t16\t0\t128\t1\t3\t488d442480",
   "lea_sib_noindex_r12\t2\t1\t12\t16\t1\t255\t1\t3\t498d4c64ff",
   "lea_sib_noindex_scale4\t2\t8\t5\t16\t2\t0\t1\t3\t4c8d44a500",
   "lea_sib_noindex_scale8\t2\t9\t13\t16\t3\t127\t1\t3\t4d8d4ce57f",
   "lea_sib_r12index\t2\t0\t5\t12\t0\t128\t1\t3\t4a8d442580",
   "lea_sib_base_index_alias\t2\t1\t12\t12\t1\t255\t1\t3\t4b8d4c64ff",
   "lea_sib_dest_index_alias\t2\t12\t5\t12\t2\t0\t1\t3\t4e8d64a500",
   "lea_sib_all_alias\t2\t13\t13\t13\t3\t127\t1\t3\t4f8d6ced7f",
   "lea_sib_dest_base_alias\t2\t0\t0\t1\t1\t255\t1\t3\t488d4448ff",
   "lea_sib_low_alias\t2\t9\t1\t1\t2\t128\t1\t3\t4c8d4c8980",
   "lea_sib_high_index\t2\t15\t0\t8\t3\t127\t1\t3\t4e8d7cc07f",
   "lea_sib_high_banks\t2\t8\t12\t9\t0\t0\t1\t3\t4f8d440c00"] ++
  ["sub_eax_80\t3\t0\t0\t16\t0\t128\t0\t0\t83e880",
   "sub_eax_ff\t3\t0\t0\t16\t0\t255\t0\t0\t83e8ff",
   "sub_eax_00\t3\t0\t0\t16\t0\t0\t0\t0\t83e800",
   "sub_eax_7f\t3\t0\t0\t16\t0\t127\t0\t0\t83e87f",
   "sub_ecx_80\t3\t1\t0\t16\t0\t128\t0\t0\t83e980",
   "sub_ecx_ff\t3\t1\t0\t16\t0\t255\t0\t0\t83e9ff",
   "sub_ecx_00\t3\t1\t0\t16\t0\t0\t0\t0\t83e900",
   "sub_ecx_7f\t3\t1\t0\t16\t0\t127\t0\t0\t83e97f",
   "sub_eax40_80\t3\t0\t0\t16\t0\t128\t1\t0\t4083e880",
   "sub_eax40_ff\t3\t0\t0\t16\t0\t255\t1\t0\t4083e8ff",
   "sub_eax40_00\t3\t0\t0\t16\t0\t0\t1\t0\t4083e800",
   "sub_eax40_7f\t3\t0\t0\t16\t0\t127\t1\t0\t4083e87f",
   "sub_ecx40_80\t3\t1\t0\t16\t0\t128\t1\t0\t4083e980",
   "sub_ecx40_ff\t3\t1\t0\t16\t0\t255\t1\t0\t4083e9ff",
   "sub_ecx40_00\t3\t1\t0\t16\t0\t0\t1\t0\t4083e900",
   "sub_ecx40_7f\t3\t1\t0\t16\t0\t127\t1\t0\t4083e97f",
   "sub_r8d_80\t3\t8\t0\t16\t0\t128\t1\t0\t4183e880",
   "sub_r8d_ff\t3\t8\t0\t16\t0\t255\t1\t0\t4183e8ff",
   "sub_r8d_00\t3\t8\t0\t16\t0\t0\t1\t0\t4183e800",
   "sub_r8d_7f\t3\t8\t0\t16\t0\t127\t1\t0\t4183e87f",
   "sub_r9d_80\t3\t9\t0\t16\t0\t128\t1\t0\t4183e980",
   "sub_r9d_ff\t3\t9\t0\t16\t0\t255\t1\t0\t4183e9ff",
   "sub_r9d_00\t3\t9\t0\t16\t0\t0\t1\t0\t4183e900",
   "sub_r9d_7f\t3\t9\t0\t16\t0\t127\t1\t0\t4183e97f",
   "sub_r12d_80\t3\t12\t0\t16\t0\t128\t1\t0\t4183ec80",
   "sub_r12d_ff\t3\t12\t0\t16\t0\t255\t1\t0\t4183ecff",
   "sub_r12d_00\t3\t12\t0\t16\t0\t0\t1\t0\t4183ec00",
   "sub_r12d_7f\t3\t12\t0\t16\t0\t127\t1\t0\t4183ec7f",
   "sub_r13d_80\t3\t13\t0\t16\t0\t128\t1\t0\t4183ed80",
   "sub_r13d_ff\t3\t13\t0\t16\t0\t255\t1\t0\t4183edff",
   "sub_r13d_00\t3\t13\t0\t16\t0\t0\t1\t0\t4183ed00",
   "sub_r13d_7f\t3\t13\t0\t16\t0\t127\t1\t0\t4183ed7f"] ++
  ["cmp_eax_80\t4\t0\t0\t16\t0\t128\t0\t0\t83f880",
   "cmp_eax_ff\t4\t0\t0\t16\t0\t255\t0\t0\t83f8ff",
   "cmp_edx_00\t4\t2\t0\t16\t0\t0\t0\t0\t83fa00",
   "cmp_eax_7f\t4\t0\t0\t16\t0\t127\t0\t0\t83f87f",
   "cmp_ecx_80\t4\t1\t0\t16\t0\t128\t0\t0\t83f980",
   "cmp_ecx_ff\t4\t1\t0\t16\t0\t255\t0\t0\t83f9ff",
   "cmp_ecx_00\t4\t1\t0\t16\t0\t0\t0\t0\t83f900",
   "cmp_ecx_7f\t4\t1\t0\t16\t0\t127\t0\t0\t83f97f",
   "cmp_eax40_80\t4\t0\t0\t16\t0\t128\t1\t0\t4083f880",
   "cmp_eax40_ff\t4\t0\t0\t16\t0\t255\t1\t0\t4083f8ff",
   "cmp_eax40_00\t4\t0\t0\t16\t0\t0\t1\t0\t4083f800",
   "cmp_eax40_7f\t4\t0\t0\t16\t0\t127\t1\t0\t4083f87f",
   "cmp_ecx40_80\t4\t1\t0\t16\t0\t128\t1\t0\t4083f980",
   "cmp_ecx40_ff\t4\t1\t0\t16\t0\t255\t1\t0\t4083f9ff",
   "cmp_ecx40_00\t4\t1\t0\t16\t0\t0\t1\t0\t4083f900",
   "cmp_ecx40_7f\t4\t1\t0\t16\t0\t127\t1\t0\t4083f97f",
   "cmp_r8d_80\t4\t8\t0\t16\t0\t128\t1\t0\t4183f880",
   "cmp_r8d_ff\t4\t8\t0\t16\t0\t255\t1\t0\t4183f8ff",
   "cmp_r8d_00\t4\t8\t0\t16\t0\t0\t1\t0\t4183f800",
   "cmp_r8d_7f\t4\t8\t0\t16\t0\t127\t1\t0\t4183f87f",
   "cmp_r9d_80\t4\t9\t0\t16\t0\t128\t1\t0\t4183f980",
   "cmp_r9d_ff\t4\t9\t0\t16\t0\t255\t1\t0\t4183f9ff",
   "cmp_r9d_00\t4\t9\t0\t16\t0\t0\t1\t0\t4183f900",
   "cmp_r9d_7f\t4\t9\t0\t16\t0\t127\t1\t0\t4183f97f",
   "cmp_r12d_80\t4\t12\t0\t16\t0\t128\t1\t0\t4183fc80",
   "cmp_r12d_ff\t4\t12\t0\t16\t0\t255\t1\t0\t4183fcff",
   "cmp_r12d_00\t4\t12\t0\t16\t0\t0\t1\t0\t4183fc00",
   "cmp_r12d_7f\t4\t12\t0\t16\t0\t127\t1\t0\t4183fc7f",
   "cmp_r13d_80\t4\t13\t0\t16\t0\t128\t1\t0\t4183fd80",
   "cmp_r13d_ff\t4\t13\t0\t16\t0\t255\t1\t0\t4183fdff",
   "cmp_r13d_00\t4\t13\t0\t16\t0\t0\t1\t0\t4183fd00",
   "cmp_r13d_7f\t4\t13\t0\t16\t0\t127\t1\t0\t4183fd7f"] ++
  ["lea32_base_np\t5\t0\t1\t16\t0\t0\t0\t0\t8d01",
   "lea32_index_np\t5\t1\t3\t1\t3\t0\t0\t1\t8d0ccb",
   "lea32_disp_np_alias\t5\t1\t1\t16\t0\t255\t0\t2\t8d49ff",
   "lea32_sib_np_noindex\t5\t2\t5\t16\t1\t128\t0\t3\t8d546580",
   "lea32_base_40\t5\t0\t3\t16\t0\t0\t1\t0\t408d03",
   "lea32_base_41\t5\t1\t8\t16\t0\t0\t1\t0\t418d08",
   "lea32_index_42\t5\t0\t3\t12\t0\t0\t1\t1\t428d0423",
   "lea32_index_43_alias\t5\t1\t12\t12\t1\t0\t1\t1\t438d0c64",
   "lea32_disp_44\t5\t8\t5\t16\t0\t128\t1\t2\t448d4580",
   "lea32_disp_45\t5\t9\t13\t16\t0\t127\t1\t2\t458d4d7f",
   "lea32_sib_46_dest_index\t5\t12\t5\t12\t2\t0\t1\t3\t468d64a500",
   "lea32_sib_47_all_alias\t5\t13\t13\t13\t3\t127\t1\t3\t478d6ced7f",
   "lea32_sib_rsp\t5\t0\t4\t16\t0\t128\t1\t3\t408d442480",
   "lea32_sib_noindex_1\t5\t1\t12\t16\t1\t255\t1\t3\t418d4c64ff",
   "lea32_sib_noindex_2\t5\t8\t5\t16\t2\t0\t1\t3\t448d44a500",
   "lea32_sib_noindex_3\t5\t9\t13\t16\t3\t127\t1\t3\t458d4ce57f",
   "lea32_sib_dest_base\t5\t0\t0\t1\t1\t255\t1\t3\t408d4448ff"] ++
  ["test_al_00\t6\t0\t0\t16\t0\t0\t0\t0\tf6c000",
   "test_al_01\t6\t0\t0\t16\t0\t1\t0\t0\tf6c001",
   "test_al_7f\t6\t0\t0\t16\t0\t127\t0\t0\tf6c07f",
   "test_al_80\t6\t0\t0\t16\t0\t128\t0\t0\tf6c080",
   "test_al_ff\t6\t0\t0\t16\t0\t255\t0\t0\tf6c0ff",
   "test_cl_ff\t6\t1\t0\t16\t0\t255\t0\t0\tf6c1ff",
   "test_dl_ff\t6\t2\t0\t16\t0\t255\t0\t0\tf6c2ff",
   "test_bl_ff\t6\t3\t0\t16\t0\t255\t0\t0\tf6c3ff",
   "test_al40_00\t6\t0\t0\t16\t0\t0\t1\t0\t40f6c000",
   "test_al40_01\t6\t0\t0\t16\t0\t1\t1\t0\t40f6c001",
   "test_al40_7f\t6\t0\t0\t16\t0\t127\t1\t0\t40f6c07f",
   "test_al40_80\t6\t0\t0\t16\t0\t128\t1\t0\t40f6c080",
   "test_al40_ff\t6\t0\t0\t16\t0\t255\t1\t0\t40f6c0ff",
   "test_spl_ff\t6\t4\t0\t16\t0\t255\t1\t0\t40f6c4ff",
   "test_spl_80\t6\t4\t0\t16\t0\t128\t1\t0\t40f6c480",
   "test_bpl_00\t6\t5\t0\t16\t0\t0\t1\t0\t40f6c500",
   "test_bpl_01\t6\t5\t0\t16\t0\t1\t1\t0\t40f6c501",
   "test_bpl_7f\t6\t5\t0\t16\t0\t127\t1\t0\t40f6c57f",
   "test_bpl_80\t6\t5\t0\t16\t0\t128\t1\t0\t40f6c580",
   "test_bpl_ff\t6\t5\t0\t16\t0\t255\t1\t0\t40f6c5ff",
   "test_r8b_00\t6\t8\t0\t16\t0\t0\t1\t0\t41f6c000",
   "test_r8b_01\t6\t8\t0\t16\t0\t1\t1\t0\t41f6c001",
   "test_r8b_7f\t6\t8\t0\t16\t0\t127\t1\t0\t41f6c07f",
   "test_r8b_80\t6\t8\t0\t16\t0\t128\t1\t0\t41f6c080",
   "test_r8b_ff\t6\t8\t0\t16\t0\t255\t1\t0\t41f6c0ff",
   "test_r9b_ff\t6\t9\t0\t16\t0\t255\t1\t0\t41f6c1ff",
   "test_r12b_ff\t6\t12\t0\t16\t0\t255\t1\t0\t41f6c4ff",
   "test_r12b_80\t6\t12\t0\t16\t0\t128\t1\t0\t41f6c480",
   "test_r13b_ff\t6\t13\t0\t16\t0\t255\t1\t0\t41f6c5ff",
   "test_r15b_ff\t6\t15\t0\t16\t0\t255\t1\t0\t41f6c7ff"]

private def readProbes (path : System.FilePath) (opcodes : System.FilePath) : IO (Array Probe) := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  require (lines.head? == some "probe\tkind\tdestination\tbase\tindex\tscale\timm8\tprefixed\taddress_form\tinstruction_hex")
    "probe table header/schema mismatch"
  let mut result := #[]
  let mut keys := #[]
  for line in lines.drop 1 do
    if line.isEmpty then continue
    let f := (line.splitOn "\t").toArray
    require (f.size == 10) "malformed probe table"
    require (requiredProbeKeys.contains line) "unexpected probe name/metadata/byte key"
    require (!f[0]!.isEmpty && f[0]!.toList.all (fun c => c.isAlphanum || c == '_') &&
      !result.any (fun p => p.name == f[0]!)) "invalid/duplicate probe name"
    let kind ← parseNat f[1]!
    let dst ← register (← parseNat f[2]!)
    let base ← register (← parseNat f[3]!)
    let idx ← parseNat f[4]!
    let index ← if idx == 16 then pure none else some <$> register idx
    let scale ← parseNat f[5]!
    let imm ← parseNat f[6]!
    let pref ← parseNat f[7]!
    let form ← parseNat f[8]!
    require (kind < 7 && scale < 4 && imm < 256 && pref < 2)
      "unsupported probe contract"
    let addressForm ← match form with
      | 0 => pure AddressForm.base
      | 1 => pure AddressForm.indexed
      | 2 => pure AddressForm.baseDisp8
      | 3 => pure AddressForm.sibDisp8
      | _ => throw (IO.userError "unsupported address form")
    let scale : Fin 4 ← if h : scale < 4 then pure ⟨scale,h⟩
      else throw (IO.userError "unsupported SIB scale")
    let code ← parseCode f[9]!
    let live ← IO.FS.readBinFile (opcodes / s!"{f[0]!}.bin")
    require (live.toList.map (BitVec.ofNat 8 ∘ UInt8.toNat) == code) "live opcode file mismatch"
    let p : Probe := ⟨f[0]!,kind,dst,base,index,scale,BitVec.ofNat 8 imm,
      pref == 1,addressForm,code⟩
    require p.metadataOK "unobserved operand, malformed address or forbidden native RSP write"
    result := result.push p
    keys := keys.push line
  require (keys.size == requiredProbeKeys.length &&
    requiredProbeKeys.all (fun key => keys.contains key)) "incomplete required probe key inventory"
  return result

private def requiredInputs : Array (String × Word) :=
  #[("zero_dirty",0xdeadbeef00000000),("one_dirty",0x1234567800000001),
    ("nibble_last",0xfedcba980000000f),("nibble_next",0x0000800000000010),
    ("byte_signed",0xffff80000000007f),("byte_high",0x0000000000000080),
    ("byte_last",0xa5a5a5a5000000ff),("byte_next",0x5a5a5a5a00000100),
    ("signed_max",0x876543217fffffff),("signed_min",0x1122334480000000),
    ("neg128",0xffffffffffffff80),("wrap",0xffffffffffffffff)]

private def readInputs (path : System.FilePath) : IO (Array (String × Word)) := do
  let mut result := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.isEmpty then continue
    let f := (line.splitOn "\t").toArray
    require (f.size == 2 && !result.any (fun i => i.1 == f[0]!)) "malformed/duplicate input table"
    result := result.push (f[0]!,← parseHex 16 f[1]!)
  require (result == requiredInputs) "incomplete or changed required input rotation"
  return result

private def header : String :=
  "case_id\tprobe\tseed\tinstruction_hex\trflags_before\trflags_after" ++
  "\tbefore_rax\tbefore_rcx\tbefore_rdx\tbefore_rbx\tbefore_rsp\tbefore_rbp" ++
  "\tbefore_r8\tbefore_r9\tbefore_r12\tbefore_r13\tbefore_r15" ++
  "\tafter_rax\tafter_rcx\tafter_rdx\tafter_rbx\tafter_rsp\tafter_rbp" ++
  "\tafter_r8\tafter_r9\tafter_r12\tafter_r13\tafter_r15"

private def readRows (probes : Array Probe) (inputs : Array (String × Word))
    (path : System.FilePath) : IO (Array Row) := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  require (lines.head? == some header) "capture header/schema mismatch"
  let mut result := #[]
  let mut seen : Array (String × String × Nat) := #[]
  for line in lines.drop 1 do
    if line.isEmpty then continue
    let f := (line.splitOn "\t").toArray
    require (f.size == 28) "malformed capture field count"
    let some p := probes.find? (fun p => p.name == f[1]!)
      | throw (IO.userError "unknown probe")
    let some c := inputs.toList.findIdx? (fun i => i.1 == f[0]!)
      | throw (IO.userError "unknown input")
    let seed ← parseNat f[2]!
    require (seed < 4) "invalid seed"
    let key := (f[0]!,p.name,seed)
    require (!seen.contains key) "duplicate observation"
    seen := seen.push key
    require (f[3]! == codeHex p.code) "captured opcode mismatch"
    let before ← (f.toList.drop 6 |>.take 11).mapM (parseHex 16)
    let after ← (f.toList.drop 17 |>.take 11).mapM (parseHex 16)
    let row : Row := ⟨p,⟨p.code,before,after,← parseHex 16 f[4]!,← parseHex 16 f[5]!⟩,seed⟩
    for j in [0:11] do
      if j == 4 then continue
      let requested := inputs[(c + (if j < 4 then j else j-1)) % 12]!.2
      require (before[j]! == requested) "controlled input mismatch"
    require (independentCheck row) "independent mathematical result/flags/frame mismatch"
    result := result.push row
  require (result.size == inputs.size * probes.size * 4) "incomplete matrix"
  for i in inputs do
    for p in probes do
      for seed in [0:4] do
        require (seen.contains (i.1,p.name,seed)) "missing required observation"
  return result

private def registerSource (r : Register) : String :=
  match r with
  | .rax => ".rax" | .rcx => ".rcx" | .rdx => ".rdx" | .rbx => ".rbx"
  | .rsp => ".rsp" | .rbp => ".rbp" | .rsi => ".rsi" | .rdi => ".rdi"
  | .r8 => ".r8" | .r9 => ".r9" | .r10 => ".r10" | .r11 => ".r11"
  | .r12 => ".r12" | .r13 => ".r13" | .r14 => ".r14" | .r15 => ".r15"

private def Probe.source (p : Probe) : String :=
  "{ name := " ++ reprStr p.name ++ ", kind := " ++ toString p.kind ++
  ", destination := " ++ registerSource p.destination ++ ", base := " ++ registerSource p.base ++
  ", index := " ++ (match p.index with | none => "none" | some r => "some " ++ registerSource r) ++
  ", scale := " ++ toString p.scale.val ++ ", immediate := " ++ wordSource (p.immediate.setWidth 64) ++
  ", prefixed := " ++ toString p.prefixed ++ ", addressForm := " ++
    (match p.addressForm with
      | .base => ".base" | .indexed => ".indexed"
      | .baseDisp8 => ".baseDisp8" | .sibDisp8 => ".sibDisp8") ++
  ", code := " ++ listSource (p.code.map (·.setWidth 64)) ++ " }"

private def selftest (rows : Array Row) : IO Unit := do
  let mut count := 0
  -- These controls bypass all independent/schema/fixture guards and challenge
  -- the actual production full-step projection on REAL captured observations.
  for name in ["add_eax_01","inc_r12d","lea_sib_dest_index_alias","lea_sib_all_alias",
      "sub_eax_80","cmp_eax_7f","lea32_sib_46_dest_index","lea32_sib_47_all_alias"] do
    let some row := rows.find? (fun r => r.probe.name == name && r.seed == 1)
      | throw (IO.userError "missing semantic corruption control")
    let c := row.capture
    let some dest := selectedRegisters.findIdx? (· == row.probe.destination)
      | throw (IO.userError "unobserved destination")
    let other := if dest == 0 then 1 else 0
    require (RegisterCapture.stepCheck selectedRegisters c) "production step rejected valid control"
    for bad in [
        { c with after := c.after.set dest (c.after[dest]! ^^^ 0x100000000) },
        { c with after := c.after.set other (c.after[other]! ^^^ 1) },
        { c with flagsAfter := c.flagsAfter ^^^ 1 },
        { c with flagsAfter := c.flagsAfter ^^^ 0x10 },
        { c with flagsAfter := c.flagsAfter ^^^ 0x800 },
        { c with flagsAfter := c.flagsAfter ^^^ 0x1000000000000000 }] do
      require (!RegisterCapture.stepCheck selectedRegisters bad)
        "full production step accepted corrupted observation"
      count := count+1
  let some inc := rows.find? (fun r => r.probe.name == "inc_r12d" && r.seed == 1)
    | throw (IO.userError "missing INC CF control")
  require (!RegisterCapture.stepCheck selectedRegisters
    { inc.capture with flagsBefore := inc.capture.flagsBefore ^^^ 1 })
    "INC production step ignored incoming CF"
  let some lea := rows.find? (fun r => r.probe.name == "lea_sib_noindex_r12")
    | throw (IO.userError "missing no-index/R12 control")
  require (!RegisterCapture.stepCheck selectedRegisters
    { lea.capture with code := [0x4b,0x8d,0x4c,0x64,0xff] })
    "production step confused no-index with R12"
  let some alias := rows.find? (fun r => r.probe.name == "lea_sib_all_alias")
    | throw (IO.userError "missing prestate alias control")
  let some pos := selectedRegisters.findIdx? (· == .r13)
    | throw (IO.userError "missing R13 capture")
  require (!RegisterCapture.stepCheck selectedRegisters
    { alias.capture with before := alias.capture.before.set pos (alias.capture.before[pos]! ^^^ 1) })
    "LEA production step ignored aliased prestate"
  count := count+3
  let some narrow := rows.find? (fun r => r.probe.name == "lea32_sib_noindex_1" &&
      (input r .r12).toNat % 4294967296 != 0)
    | throw (IO.userError "missing LEA32 no-index/R12 control")
  require (!RegisterCapture.stepCheck selectedRegisters
    { narrow.capture with code := [0x43,0x8d,0x4c,0x64,0xff] })
    "LEA32 production step confused no-index with R12"
  let some narrowAlias := rows.find? (fun r => r.probe.name == "lea32_sib_47_all_alias")
    | throw (IO.userError "missing LEA32 prestate alias control")
  require (!RegisterCapture.stepCheck selectedRegisters
    { narrowAlias.capture with
      before := narrowAlias.capture.before.set pos (narrowAlias.capture.before[pos]! ^^^ 1) })
    "LEA32 production step ignored aliased prestate"
  require (!RegisterCapture.checkWithAF selectedRegisters narrowAlias.capture
    narrowAlias.probe.instruction .undefinedAF) "AF policy admitted a deterministic LEA"
  count := count+3
  -- AF-only flips are SYNTHETIC positive controls, never extra native rows.
  -- Full expected flags bind each actual step choice to AF=false/true.
  for name in ["test_al_ff","test_al40_ff","test_r8b_ff","test_spl_ff"] do
    let some row := rows.find? (fun r => r.probe.name == name && r.seed == 1)
      | throw (IO.userError "missing TEST AF admissibility control")
    require (check row) "production rejected valid TEST control"
    require (!RegisterCapture.check selectedRegisters row.capture row.probe.instruction)
      "exact compatibility wrapper admitted undefined AF"
    let flipped := { row with capture := { row.capture with flagsAfter := row.capture.flagsAfter ^^^ 0x10 } }
    require (independentCheck flipped && RegisterCapture.stepCheckWithAF selectedRegisters
      flipped.capture .undefinedAF && check flipped) "TEST AF policy excluded an independent choice"
    count := count+2
  let some test := rows.find? (fun r => r.probe.name == "test_al_ff" && r.seed == 0 &&
      (input r .rax).toNat % 256 == 128 && (input r .rcx).toNat % 256 == 255)
    | throw (IO.userError "missing distinguishing TEST byte/register control")
  -- Every other saved flag bit, including all preserved bits, must reject.
  for bit in [0:64] do
    if bit == 4 then continue
    let bad := { test.capture with flagsAfter := test.capture.flagsAfter ^^^ BitVec.ofNat 64 (2^bit) }
    require (!RegisterCapture.stepCheckWithAF selectedRegisters bad .undefinedAF)
      "TEST projection accepted a defined/preserved flag mutation"
    count := count+1
  -- Every physically observed GPR, including full RSP, must survive TEST.
  for index in [0:selectedRegisters.length] do
    for mask in ([1,0x100000000] : List Word) do
      let bad := { test.capture with
        after := test.capture.after.set index (test.capture.after[index]! ^^^ mask) }
      require (!RegisterCapture.stepCheckWithAF selectedRegisters bad .undefinedAF)
        "TEST projection accepted a full GPR mutation"
      count := count+1
  for code in ([[0xf6,0xc0,0x00],[0xf6,0xc1,0xff]] : List (List Byte)) do
    require (!RegisterCapture.stepCheckWithAF selectedRegisters
      { test.capture with code := code } .undefinedAF)
      "TEST production step ignored a distinguishing mask or register selector"
    count := count+1
  -- Public decoder/length authentication must not allow a valid extra byte.
  require (!RegisterCapture.checkWithAF selectedRegisters
    { test.capture with code := test.capture.code ++ [0x90] } test.probe.instruction .undefinedAF)
    "production capture check accepted a wrong exact window length"
  count := count+1
  IO.println s!"PASS: {count} direct production-step/admission controls; AF flips are synthetic."

private def generate (rows : Array Row) (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  let mut modules := []
  -- Split finite DATA per module; never change kernel recursion/heartbeat caps.
  for chunk in [0:(rows.size+15)/16] do
    let name := s!"CounterDisplacementChunk{chunk}"
    modules := modules ++ [name]
    let mut source := "import tests.native.CounterDisplacementReplay\nset_option autoImplicit false\n" ++
      "set_option warningAsError true\n" ++
      "set_option maxHeartbeats 300000\nset_option maxRecDepth 128\n" ++
      "namespace EDSL.Tests.CounterDisplacementReplay.Generated\n"
    for i in [chunk*16:min rows.size ((chunk+1)*16)] do
      let r := rows[i]!
      source := source ++ s!"def row{i} : Row := " ++ "{ probe := " ++ r.probe.source ++
        ", capture := " ++ r.capture.source ++ ", seed := " ++ toString r.seed ++ " }\n" ++
        s!"theorem row{i}_pass : check row{i} = true := by decide +kernel\n"
    source := source ++ "end EDSL.Tests.CounterDisplacementReplay.Generated\n"
    IO.FS.writeFile (directory / s!"{name}.lean") source
  IO.FS.writeFile (directory / "CounterDisplacement.modules") (String.intercalate "\n" modules ++ "\n")
  IO.println s!"Generated {rows.size} observations in {modules.length} modules; kernel compilation required."

def main (args : List String) : IO Unit := do
  match args with
  | ["generate",probes,inputs,capture,opcodes,directory] =>
    let ps ← readProbes probes opcodes
    let ins ← readInputs inputs
    let rows ← readRows ps ins capture
    selftest rows
    generate rows directory
  | ["check",probes,inputs,capture,opcodes] =>
    let ps ← readProbes probes opcodes
    let ins ← readInputs inputs
    let rows ← readRows ps ins capture
    for row in rows do
      require (check row) "production check rejected persisted control"
    selftest rows
    IO.println s!"Checked {rows.size} complete persisted rows; no proof source emitted."
  | _ => throw (IO.userError "usage: CounterDisplacementReplay generate PROBES.tsv INPUTS.tsv CAPTURE.tsv OPCODES OUTPUT | check PROBES.tsv INPUTS.tsv CAPTURE.tsv OPCODES")

end EDSL.Tests.CounterDisplacementReplay
