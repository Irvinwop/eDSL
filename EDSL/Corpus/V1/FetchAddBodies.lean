/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.FetchAddWindows
import EDSL.X86.VCGen.AtomicMethods

set_option warningAsError true

/-!
Universal standalone fetch-add body facts for both unchanged frozen compiler
windows. Whole-file/name/extent identity is inherited from FetchAddWindows;
functional behavior is supplied by the shared atomic-method proof. Actual-
address resource construction, complete call/ABI adapters, independent history
registry acceptance and corpus reporting remain separate obligations. This
module changes no score and makes no physical/Linux/fairness/minimum claim.
-/

namespace EDSL.Corpus.V1.FetchAddBodies
open X86 OS OS.TSO64 X86.VCGen.AtomicMethods

abbrev Compiler := FetchAddWindows.Compiler

def padding : Compiler → List Padding
  | .defaultGCC => [.endbr64]
  | .defaultClang => []

/-- Static decoding and entire-window coverage, including GCC ENDBR64. -/
theorem shape_checked (compiler : Compiler) :
    check (FetchAddWindows.bytes compiler) .rsi LockedAdd64.frozen (padding compiler) = true := by
  cases compiler <;> decide +kernel

theorem shape (compiler : Compiler) :
    Shape (FetchAddWindows.bytes compiler) .rsi LockedAdd64.frozen 0 (padding compiler) :=
  (check_sound (shape_checked compiler)).2

/-- Arbitrary admitted entry data and current resources. No initial target
word is fixed, and no target word is carried across interleavings. The return
and no-wrap requirements describe this abstract ABI/stack profile explicitly. -/
structure Invocation where
  base : Word
  registers : Register → Word
  flags : Word
  resources : Resources
  identifier : Atomics64.HandleId64
  handle : Atomics64.Handle
  cell : Atomics64.Cell
  returnAddress : Word
  originalRsp : registers .rsp = resources.callerAddress
  returnCanonical : canonical returnAddress = true
  stackNoWrap : (registers .rsp).toNat + 8 < 2^64

def Invocation.method (invocation : Invocation) (compiler : Compiler) : Method where
  bytes := FetchAddWindows.bytes compiler
  input := .rsi
  locked := LockedAdd64.frozen
  base := invocation.base
  entry := invocation.registers
  resources := invocation.resources
  identifier := invocation.identifier
  handle := invocation.handle
  cell := invocation.cell
  returnAddress := invocation.returnAddress
  size := (check_sound (shape_checked compiler)).1
  sourceNotRsp := by decide +kernel
  originalRsp := invocation.originalRsp
  returnCanonical := invocation.returnCanonical
  stackNoWrap := invocation.stackNoWrap

/-- Production attachment establishes running phase and an EMPTY own FIFO.
Current checks executable bytes, original caller read and actual target-handle
selection. It places no desired value gate on a future machine/world state. -/
structure Pre (compiler : Compiler) (invocation : Invocation) (state : OS.TSO64.State)
    (worker : Worker) : Prop where
  current : Current (invocation.method compiler) state
  made : makeWorker state.world invocation.resources.actor
    ⟨invocation.registers, invocation.base, invocation.flags⟩
    invocation.resources.code.identifier invocation.resources.caller.identifier
    invocation.resources.grants invocation.resources.atomics = .ok worker
  resources : worker.resources = invocation.resources

theorem Pre.entry {compiler : Compiler} {invocation : Invocation} {state : OS.TSO64.State}
    {worker : Worker} (pre : Pre compiler invocation state worker) :
    At (invocation.method compiler) (.preamble 0 (padding compiler)) worker :=
  entry_of_makeWorker (shape compiler) pre.made pre.resources rfl rfl

/-- Present selection identifies the object at the entry RDI pointer. The
generic family uses the post-copy base, retaining correct alias semantics. -/
theorem Pre.targetAddress {compiler : Compiler} {invocation : Invocation} {state : OS.TSO64.State}
    {worker : Worker} (pre : Pre compiler invocation state worker) :
    invocation.cell.address = invocation.registers .rdi := by
  have address := (atomicFor_sound pre.current.selected).2.2
  change invocation.cell.address = written invocation.registers LockedAdd64.frozen.source
    (invocation.registers .rsi) LockedAdd64.frozen.base at address
  have base : LockedAdd64.frozen.base = .rdi := by decide +kernel
  have source : LockedAdd64.frozen.source = .rax := by decide +kernel
  rw [base, source, written_other _ _ _ _ (by decide +kernel)] at address
  exact address

/-- Exact ELF/name/extent byte binding AND universal current-resource body
correctness. The initial data and every successful interleaving/completed
outcome are arbitrary. No invocation/point/response-label checker is assumed.

The result contains actual old-word RAX, entry RSI delta, one own typed RMW
with exact same-run prefix/suffix, original caller/code/resources, all other
GPR frames except RSP, stack pop, and nonarithmetic flag preservation. -/
theorem all_completed (compiler : Compiler) (invocation : Invocation)
    {state : OS.TSO64.State} {tid : Nat} {initial : Worker}
    (pre : Pre compiler invocation state initial) (live : state.workers[tid]? = some initial)
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    (success : schedule state actions = .ok result) {final : Worker}
    (finalLive : result.1.workers[tid]? = some final) (returned : final.phase = .returned) :
    (FetchAddWindows.input compiler).check (FetchAddWindows.file compiler) FetchAddWindows.name = true ∧
    Current (invocation.method compiler) result.1 ∧ ∃ event,
      BodyPost (invocation.method compiler) final event ∧
      final.context.registers .rax = event.arithmetic.event.before ∧
      event.arithmetic.delta = invocation.registers .rsi ∧
      event.arithmetic.event.address = invocation.registers .rdi ∧
      result.2.filterMap (ownEvent tid) = [event] ∧
      RMWOrigin (invocation.method compiler) tid state actions result event ∧
      ownIssues tid actions = (padding compiler).length + 3 ∧
      final.context.flags &&& ~~~arithmeticFlagMask = initial.context.flags &&& ~~~arithmeticFlagMask := by
  obtain ⟨current, event, post, unique, origin, count, flags⟩ :=
    all_completed_origin pre.current live pre.entry success finalLive returned
  have response : final.context.registers .rax = event.arithmetic.event.before := by
    have source : (invocation.method compiler).locked.source = .rax := by
      change LockedAdd64.frozen.source = .rax
      decide +kernel
    rw [← source]
    exact post.response
  exact ⟨FetchAddWindows.checked compiler, current, event, post, response, post.correct.input,
    post.correct.address.trans pre.targetAddress, unique, origin, count, flags⟩

/-- Each admitted frozen body has a bounded own-only completing schedule.
GCC retires four modeled instructions; Clang retires three. Interference and
scheduler fairness are separate from this own-progress statement. -/
theorem completion (compiler : Compiler) (invocation : Invocation)
    {state : OS.TSO64.State} {tid : Nat} {initial : Worker}
    (pre : Pre compiler invocation state initial) (live : state.workers[tid]? = some initial)
    (choices : Nat → Bool) :
    ∃ actions result final event,
      actions.length = (padding compiler).length + 3 ∧
      (∀ action ∈ actions, ∃ af, action = .issue tid af) ∧
      schedule state actions = .ok result ∧ result.1.workers[tid]? = some final ∧
      BodyPost (invocation.method compiler) final event := by
  obtain ⟨actions, result, final, event, length, own, scheduled, finalLive, located⟩ :=
    complete pre.current live pre.entry choices
  exact ⟨actions, result, final, event, length, own, scheduled, finalLive, located.done_post⟩

end EDSL.Corpus.V1.FetchAddBodies

#audit_edsl
