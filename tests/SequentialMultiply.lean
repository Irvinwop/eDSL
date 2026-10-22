/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Sequential.Multiply
import EDSL.X86.Sequential.ExecutionChoices
import EDSL.X86.VCGen.Choices
import EDSL.X86.Sequential.CFGDiscovery
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

/-!
Owned synthetic byte-level IMUL controls. Expected products, status words,
branch results, instruction counts and reads below are literal contracts.
The abstract undefined-flag choices make no claim that a processor realizes
every valuation. Hardware correspondence retains the production target's
long-mode and disabled-CET assumptions.

-/

namespace EDSL.Tests.SequentialMultiply
open X86 X86.Sequential

private instance {α β : Type} [DecidableEq α] [DecidableEq β] :
    DecidableEq (Except α β)
  | .error left, .error right =>
    if same : left = right then .isTrue (congrArg Except.error same)
    else .isFalse (fun equal => same (Except.error.inj equal))
  | .ok left, .ok right =>
    if same : left = right then .isTrue (congrArg Except.ok same)
    else .isFalse (fun equal => same (Except.ok.inj equal))
  | .error _, .ok _ => .isFalse (by intro equal; cases equal)
  | .ok _, .error _ => .isFalse (by intro equal; cases equal)

private def registers : Register → Word
  | .rax => 3
  | .rcx => 7
  | .rsi => 5
  | .r8 => 0x100000003
  | .r9 => 5
  | .rsp => 32768
  | _ => 0x123456789abcdef0

/-- Only the code window is executable. The original stack slot contains
8192 in little-endian order and is readable without being executable. -/
private def entry (code : List Byte) (bank : Register → Word := registers)
    (flags : Word := 0x202) : State where
  registers := bank
  rip := 4096
  flags := flags
  memory := {
    read := fun address =>
      if address = 32769 then some 0x20
      else if 32768 ≤ address.toNat ∧ address.toNat < 32776 then some 0
      else code[(address - 4096).toNat]?
    executable := fun address => decide ((address - 4096).toNat < code.length)
    writable := fun _ => false }

private def operands (left right : Word) : Register → Word :=
  fun register => if register = .rax then left
    else if register = .rsi then right else registers register

/-- CF/OF are deliberately true here; fitting products must still clear them. -/
private def undefinedChoices (pf af zf sf : Bool) : FlagChoices :=
  ⟨true, pf, af, zf, sf, true⟩

/-- A decidable projection of a real decoded step, without memory-function
equality or a product-type equality instance. -/
private structure Snapshot where
  value : Word
  source : Word
  flags : Word
  rip : Word
  reads : List Read
  deriving DecidableEq, Repr

private def nextSnapshot (choices : FlagChoices) (initial : State)
    (destination : Register := .rax) (source : Register := .rsi) : Except Error Snapshot := do
  let observation ← Sequential.stepWith choices initial
  match observation.result with
  | .next final =>
    return ⟨final.registers destination, final.registers source,
      final.flags, final.rip, observation.reads⟩
  | _ => throw .unexpectedReturn

/-- All four independent undefined bits, PF/AF/ZF/SF in that order. No
expected word is computed by the multiplication flag helper or a bit assembler. -/
theorem sixteen_literal_flag_words :
    ([undefinedChoices false false false false,
      undefinedChoices false false false true,
      undefinedChoices false false true false,
      undefinedChoices false false true true,
      undefinedChoices false true false false,
      undefinedChoices false true false true,
      undefinedChoices false true true false,
      undefinedChoices false true true true,
      undefinedChoices true false false false,
      undefinedChoices true false false true,
      undefinedChoices true false true false,
      undefinedChoices true false true true,
      undefinedChoices true true false false,
      undefinedChoices true true false true,
      undefinedChoices true true true false,
      undefinedChoices true true true true] : List FlagChoices).map
      (fun choices => (nextSnapshot choices (entry [0x48,0x0f,0xaf,0xc6])).map
        Snapshot.flags) =
    [.ok 0x202,.ok 0x282,.ok 0x242,.ok 0x2c2,
     .ok 0x212,.ok 0x292,.ok 0x252,.ok 0x2d2,
     .ok 0x206,.ok 0x286,.ok 0x246,.ok 0x2c6,
     .ok 0x216,.ok 0x296,.ok 0x256,.ok 0x2d6] := by
  decide +kernel

/-- The exact four executable bytes suffice, and advance RIP by four. -/
theorem nonzero_product_and_exact_extent :
    nextSnapshot (undefinedChoices false false false false)
      (entry [0x48,0x0f,0xaf,0xc6]) = .ok ⟨15,5,0x202,4100,[]⟩ := by
  decide +kernel

/-- An unsigned high half would set carry for this signed, fitting product. -/
theorem negative_one_times_two_has_no_signed_overflow :
    nextSnapshot (FlagChoices.uniform false)
      (entry [0x48,0x0f,0xaf,0xc6] (operands 0xffffffffffffffff 2)) =
      .ok ⟨0xfffffffffffffffe,2,0x202,4100,[]⟩ := by
  decide +kernel

theorem signed_max_times_two_overflows :
    nextSnapshot (FlagChoices.uniform false)
      (entry [0x48,0x0f,0xaf,0xc6] (operands 0x7fffffffffffffff 2)) =
      .ok ⟨0xfffffffffffffffe,2,0xa03,4100,[]⟩ := by
  decide +kernel

theorem signed_min_times_negative_one_overflows :
    nextSnapshot (FlagChoices.uniform false)
      (entry [0x48,0x0f,0xaf,0xc6]
        (operands 0x8000000000000000 0xffffffffffffffff)) =
      .ok ⟨0x8000000000000000,0xffffffffffffffff,0xa03,4100,[]⟩ := by
  decide +kernel

/-- Undefined ZF/SF are not inferred from the zero destination. -/
theorem zero_product_can_have_sign_without_zero :
    nextSnapshot (undefinedChoices false false false true)
      (entry [0x48,0x0f,0xaf,0xc6] (operands 0 5)) =
      .ok ⟨0,5,0x282,4100,[]⟩ := by
  decide +kernel

/-- Reading an already overwritten operand for overflow would see zero. -/
theorem self_alias_uses_old_signed_min_for_overflow :
    nextSnapshot (FlagChoices.uniform false)
      (entry [0x48,0x0f,0xaf,0xc0] (operands 0x8000000000000000 5)) .rax .rax =
      .ok ⟨0,0,0xa03,4100,[]⟩ := by
  decide +kernel

/-- Literal ModRM C1 distinguishes REX.R and REX.B, including ignored X. -/
theorem decode_all_rex_w_register_banks :
    ([0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f] : List Byte).map
      (fun rex => Sequential.decodeAt (entry [rex,0x0f,0xaf,0xc1])) =
    [.ok (.imulReg64 .rax .rcx),.ok (.imulReg64 .rax .r9),
     .ok (.imulReg64 .rax .rcx),.ok (.imulReg64 .rax .r9),
     .ok (.imulReg64 .r8 .rcx),.ok (.imulReg64 .r8 .r9),
     .ok (.imulReg64 .r8 .rcx),.ok (.imulReg64 .r8 .r9)] := by
  decide +kernel

/-- The high half participates in the product. R9 survives, and adding X
does not change operands or require a fifth executable byte. -/
theorem extended_register_steps_and_ignored_x :
    ([0x4d,0x4f] : List Byte).map (fun rex =>
      nextSnapshot (FlagChoices.uniform false) (entry [rex,0x0f,0xaf,0xc1]) .r8 .r9) =
    [.ok ⟨0x50000000f,5,0x202,4100,[]⟩,
     .ok ⟨0x50000000f,5,0x202,4100,[]⟩] := by
  decide +kernel

/-- Width, LOCK and memory forms cannot acquire a register-only meaning. -/
theorem unsupported_width_prefix_and_memory_forms :
    ([[0x0f,0xaf,0xc1],[0x40,0x0f,0xaf,0xc1],[0x47,0x0f,0xaf,0xc1],
      [0x66,0x0f,0xaf,0xc1],[0x66,0x48,0x0f,0xaf,0xc1],
      [0xf0,0x48,0x0f,0xaf,0xc6],[0xf0,0x0f,0xaf,0xc6],
      [0x48,0x48,0x0f,0xaf,0xc6],
      [0x48,0x0f,0xaf,0x06],[0x48,0x0f,0xaf,0x46,0],
      [0x48,0x0f,0xaf,0x86,0,0,0,0],[0x4d,0x0f,0xaf,0x01]] :
      List (List Byte)).map (fun bytes => Sequential.decodeAt (entry bytes)) =
    List.replicate 12 (.error .unsupportedEncoding) := by
  decide +kernel

/-- The first missing required byte is reported at its actual address. -/
theorem truncation_fault_addresses :
    ([[],[0x48],[0x48,0x0f],[0x48,0x0f,0xaf],
      [0x4d],[0x4d,0x0f],[0x4d,0x0f,0xaf]] : List (List Byte)).map
      (fun bytes => Sequential.decodeAt (entry bytes)) =
    [.error (.inaccessibleInstruction 4096),.error (.inaccessibleInstruction 4097),
     .error (.inaccessibleInstruction 4098),.error (.inaccessibleInstruction 4099),
     .error (.inaccessibleInstruction 4097),.error (.inaccessibleInstruction 4098),
     .error (.inaccessibleInstruction 4099)] := by
  decide +kernel

private def deniedModRM : State :=
  let initial := entry [0x48,0x0f,0xaf,0xc6]
  { initial with memory := { initial.memory with
      executable := fun address =>
        if address = 4099 then false else initial.memory.executable address } }

/-- Readability of the ModRM byte cannot replace its execute permission. -/
theorem readable_nonexecutable_modrm_rejected :
    [(Sequential.decodeAt deniedModRM).map (fun _ => ()),
     (Sequential.stepWith (FlagChoices.uniform false) deniedModRM).map (fun _ => ())] =
    [.error (.inaccessibleInstruction 4099),.error (.inaccessibleInstruction 4099)] := by
  decide +kernel

/- Exact offsets: 0 IMUL; 4 JZ20; 6 JP14; 8 MOV0; 13 RET;
14 MOV1; 19 RET; 20 JP28; 22 MOV2; 27 RET; 28 MOV3; 33 RET. -/
private def branchBytes : List Byte :=
  [0x48,0x0f,0xaf,0xc6,
   0x74,0x0e, 0x7a,0x06,
   0xb8,0,0,0,0, 0xc3,
   0xb8,1,0,0,0, 0xc3,
   0x7a,0x06,
   0xb8,2,0,0,0, 0xc3,
   0xb8,3,0,0,0, 0xc3]

/-- A literal 34-byte, 12-node graph checked under the unchanged default
profile. JP is the actual parity condition, encoding nibble ten. -/
private def branchGraph : CFG.Graph :=
  ⟨[⟨0,.imulReg64 .rax .rsi,true,12⟩,
    ⟨4,.je 0x0e,false,11⟩,
    ⟨6,.jcc .parity 0x06,false,10⟩,
    ⟨8,.legacy (.mov32 .rax 0),false,9⟩,
    ⟨13,.legacy .ret,false,8⟩,
    ⟨14,.legacy (.mov32 .rax 1),false,7⟩,
    ⟨19,.legacy .ret,false,6⟩,
    ⟨20,.jcc .parity 0x06,false,5⟩,
    ⟨22,.legacy (.mov32 .rax 2),false,4⟩,
    ⟨27,.legacy .ret,false,3⟩,
    ⟨28,.legacy (.mov32 .rax 3),false,2⟩,
    ⟨33,.legacy .ret,false,1⟩],12⟩

private def branchStart : branchGraph.Index := ⟨0,by decide⟩
private def branchInitial : State := entry branchBytes

theorem branch_graph_checked : CFG.check branchBytes branchGraph = true := by
  decide +kernel

private theorem branch_graph_valid : CFG.Valid branchBytes branchGraph :=
  CFG.check_sound branch_graph_checked

/-- The proposed graph cannot supply a source register absent from the bytes. -/
theorem graph_rejects_changed_imul_source :
    CFG.check (branchBytes.set 3 0xc7) branchGraph = false := by
  decide +kernel

/-- Changing JP into JNP cannot retain the supplied parity instruction. -/
theorem graph_rejects_changed_parity_condition :
    CFG.check (branchBytes.set 6 0x7b) branchGraph = false := by
  decide +kernel

private structure ReturnSnapshot where
  value : Word
  rsp : Word
  rip : Word
  flags : Word
  instructions : Nat
  reads : List Read
  deriving DecidableEq, Repr

private def returnSnapshot (result : Result) : ReturnSnapshot :=
  ⟨result.state.registers .rax,result.state.registers .rsp,result.state.rip,
    result.state.flags,result.instructions,result.reads⟩

/-- Four actual decoded executions use the same nonzero product, and each
executes both flag tests, one MOV and one RET after IMUL. -/
theorem actual_branches_return_all_four :
    ([undefinedChoices false false false false,
      undefinedChoices true false false false,
      undefinedChoices false false true false,
      undefinedChoices true false true false] : List FlagChoices).map
      (fun choices => (runWith (fun _ => choices) 5 branchInitial).map returnSnapshot) =
    [.ok ⟨0,32776,8192,0x202,5,[⟨.stack,32768,8⟩]⟩,
     .ok ⟨1,32776,8192,0x206,5,[⟨.stack,32768,8⟩]⟩,
     .ok ⟨2,32776,8192,0x242,5,[⟨.stack,32768,8⟩]⟩,
     .ok ⟨3,32776,8192,0x246,5,[⟨.stack,32768,8⟩]⟩] := by
  decide +kernel

/-- This restricted vector experiment demonstrates why one shared Bool
cannot justify the universal diagonal result contract. -/
theorem uniform_vectors_miss_cross_results :
    ([false,true] : List Bool).map (fun value =>
      (runWith (fun _ => FlagChoices.uniform value) 5 branchInitial).map
        (fun result => result.state.registers .rax)) = [.ok 0,.ok 3] := by
  decide +kernel

/-- The compatibility boundary is observed through real Bool steps of the
same bytes; projecting away the observation avoids state equality. -/
theorem bool_step_rejects_same_imul :
    ([false,true] : List Bool).map (fun value =>
      (Sequential.step value branchInitial).map (fun _ => ())) =
    [.error .unsupportedEncoding,.error .unsupportedEncoding] := by
  decide +kernel

private def permitReturn (_state : State) (read : Read) : Prop :=
  read = ⟨.stack,32768,8⟩

private def denyReturn (_state : State) (_read : Read) : Prop := False

private def unionContract (result : Result) : Prop :=
  (result.state.registers .rax = 0 ∨ result.state.registers .rax = 1 ∨
    result.state.registers .rax = 2 ∨ result.state.registers .rax = 3) ∧
  result.state.registers .rsp = 32776 ∧ result.state.rip = 8192 ∧
  result.instructions = 5 ∧ result.reads = [⟨.stack,32768,8⟩]

private def diagonalContract (result : Result) : Prop :=
  result.state.registers .rax = 0 ∨ result.state.registers .rax = 3

private instance : DecidablePred unionContract := by
  intro result
  unfold unionContract
  infer_instance

private instance : DecidablePred diagonalContract := by
  intro result
  unfold diagonalContract
  infer_instance

private instance (Post : X86.VCGen.Contract) [DecidablePred Post] :
    Decidable (X86.VCGen.wpWith branchGraph 4096 permitReturn 5 branchStart branchInitial Post) :=
  X86.VCGen.decidableWPWith branchGraph 4096 permitReturn
    (fun _ read => inferInstanceAs (Decidable (read = ⟨.stack,32768,8⟩)))
    5 branchStart branchInitial Post (fun _ => inferInstance)

private instance (Post : X86.VCGen.Contract) [DecidablePred Post] :
    Decidable (X86.VCGen.wpWith branchGraph 4096 denyReturn 5 branchStart branchInitial Post) :=
  X86.VCGen.decidableWPWith branchGraph 4096 denyReturn
    (fun _ _ => inferInstanceAs (Decidable False))
    5 branchStart branchInitial Post (fun _ => inferInstance)

theorem vector_vcg_accepts_union :
    X86.VCGen.checkChoices branchGraph 4096 permitReturn 5 branchStart branchInitial
      unionContract = true := by
  decide +kernel

/-- Correlating PF and ZF into one Bool would wrongly accept this contract. -/
theorem vector_vcg_rejects_diagonal :
    X86.VCGen.checkChoices branchGraph 4096 permitReturn 5 branchStart branchInitial
      diagonalContract = false := by
  decide +kernel

/-- The successful decoded RETs above establish actual modeled readability.
The independent caller read policy must still be enforced. -/
theorem vector_vcg_rejects_denied_return_read :
    X86.VCGen.checkChoices branchGraph 4096 denyReturn 5 branchStart branchInitial
      unionContract = false := by
  decide +kernel

/-- Enumerate only the 34 actual code offsets, not the address space. -/
private theorem branch_code : CodeAt branchInitial.memory 4096 branchBytes := by
  refine ⟨by decide +kernel, ?_⟩
  intro offset byte present
  obtain ⟨inside, same⟩ := List.getElem?_eq_some_iff.mp present
  have fetched : ∀ index : Fin branchBytes.length,
      fetchByte branchInitial.memory (4096 + BitVec.ofNat 64 index.val) =
        .ok (branchBytes[index.val]'index.isLt) := by
    decide +kernel
  simpa only [same] using fetched ⟨offset,inside⟩

/-- The accepted formula is bound to real executable RAM and checked bytes,
and entails actual runs and permitted traces for every complete vector stream. -/
theorem checked_union_covers_every_vector_stream (choices : ChoiceStream FlagChoices) :
    ∃ result, runWith choices 5 branchInitial = .ok result ∧ unionContract result ∧
      result.instructions ≤ 5 ∧
      X86.VCGen.CheckedTraceWith permitReturn choices branchInitial result :=
  X86.VCGen.checked_soundWith (node := branchStart) branch_graph_valid branch_code (by rfl)
    vector_vcg_accepts_union choices

end EDSL.Tests.SequentialMultiply

#print axioms EDSL.Tests.SequentialMultiply.sixteen_literal_flag_words
#print axioms EDSL.Tests.SequentialMultiply.negative_one_times_two_has_no_signed_overflow
#print axioms EDSL.Tests.SequentialMultiply.signed_max_times_two_overflows
#print axioms EDSL.Tests.SequentialMultiply.signed_min_times_negative_one_overflows
#print axioms EDSL.Tests.SequentialMultiply.zero_product_can_have_sign_without_zero
#print axioms EDSL.Tests.SequentialMultiply.self_alias_uses_old_signed_min_for_overflow
#print axioms EDSL.Tests.SequentialMultiply.decode_all_rex_w_register_banks
#print axioms EDSL.Tests.SequentialMultiply.extended_register_steps_and_ignored_x
#print axioms EDSL.Tests.SequentialMultiply.actual_branches_return_all_four
#print axioms EDSL.Tests.SequentialMultiply.bool_step_rejects_same_imul
#print axioms EDSL.Tests.SequentialMultiply.branch_graph_checked
#print axioms EDSL.Tests.SequentialMultiply.vector_vcg_accepts_union
#print axioms EDSL.Tests.SequentialMultiply.vector_vcg_rejects_diagonal
#print axioms EDSL.Tests.SequentialMultiply.vector_vcg_rejects_denied_return_read
#print axioms EDSL.Tests.SequentialMultiply.checked_union_covers_every_vector_stream
#audit_edsl
