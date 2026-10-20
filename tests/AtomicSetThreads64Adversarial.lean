/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicSetThreads64.Model
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.AtomicSetThreads64Adversarial
open X86 OS.AddressSpace OS.AtomicSetThreads64

abbrev Shared := OS.Atomics64.State
abbrev Fault := OS.AtomicThreads64.Fault
abbrev State := OS.AtomicSetThreads64.State

local instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok left, .ok right => left == right
    | .error left, .error right => left == right
    | _, _ => false

/-- Synthetic loader input only. Workers, loans and handles below are created
by the checked APIs. Padding stays executable beyond every declared window. -/
def loader (bytes : List Byte) (caller target : Word) : Space where
  cells address :=
    let n := address.toNat
    if 4096 ≤ n ∧ n < 4160 then
      some ⟨bytes[n - 4096]?.getD 0x90, readExecute⟩
    else if caller.toNat ≤ n ∧ n < caller.toNat + 8 then
      some ⟨target.extractLsb' (8 * (n - caller.toNat)) 8, readOnly⟩
    else if 65536 ≤ n ∧ n < 65552 then
      some ⟨(0x8000000000000001 : Word).extractLsb' (8 * (n - 65536)) 8, readWrite⟩
    else none

def entry (caller : Word) : Context where
  registers register := if register = .rdi then 65536 else if register = .rsp then caller
    else if register = .rsi then 0 else 0x0123456789abcdef
  rip := 4096
  flags := 0xed7

def withTicket (shared : Shared) (operation : OS.Ownership.Mutation) :
    Except Fault (Shared × OS.Ownership.Ticket) := do
  let (after, ticket) ← (OS.Atomics64.mutate shared operation).mapError OS.AtomicThreads64.Fault.atomic
  let some ticket := ticket | throw .unexpectedStep
  return (after, ticket)

def setup (bytes : List Byte) (caller : Word := 32768) (target : Word := 8192) :
    Except Fault (State × Start × OS.Ownership.Ticket) := do
  let initial := OS.Atomics64.empty
    (OS.Atomics.empty (OS.Borrowing.empty (OS.Ownership.empty (loader bytes caller target))))
  let (data, dataTicket) ← withTicket initial (.adopt 0 ⟨65536, 16⟩)
  let (code, codeTicket) ← withTicket data (.adopt 0 ⟨4096, 64⟩)
  let (stack, stackTicket) ← withTicket code (.adopt 0 ⟨caller, 8⟩)
  let (registered, cell) ← (OS.Atomics64.enroll stack 0 dataTicket 65536).mapError OS.AtomicThreads64.Fault.atomic
  return (empty registered, ⟨entry caller, bytes, cell, codeTicket, stackTicket⟩, dataTicket)

def faultOf {α : Type} : Except Fault α → Option Fault
  | .error fault => some fault
  | .ok _ => none

def expect [BEq α] [Repr α] (name : String) (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw (IO.userError s!"{name}: expected {repr expected}, got {repr actual}")

def atWorker (state : State) (identifier : Nat) : Except Fault Worker :=
  match state.workers identifier with
  | some worker => .ok worker
  | none => .error .missingThread

def memory (state : State) : Memory := toMemory state.shared.legacy.shared.resources.space

-- All expected encodings and fault/value outcomes are literal. In particular,
-- neither bodyBytes nor the logical operation evaluator generates an oracle.
def twoInstructions : List Byte := [0xf0,0x48,0x21,0x37,0xf0,0x48,0x31,0x37,0xc3]

def truncatedWindows : Except Fault
    (List (Option Fault) × Except Error LockedSet64.Instruction × Except Error LockedSet64.Instruction) := do
  let (state, start, _) ← setup twoInstructions
  -- Lengths 1--3 cut the first instruction; 5--7 cut the later one. Lengths
  -- 4 and 8 lack RET. The backing RAM nevertheless holds BOTH whole encodings.
  let faults := [0,1,2,3,4,5,6,7,8].map fun length =>
    faultOf (spawn state 0 { start with bytes := twoInstructions.take length })
  let first := LockedSet64.decodeAt (start.entry.snapshot state.shared.legacy.shared.resources.space)
  let later := LockedSet64.decodeAt
    ({ start.entry with rip := 4100 }.snapshot state.shared.legacy.shared.resources.space)
  return (faults, first, later)

#eval expect "truncated original windows despite adjacent executable complete instructions"
  truncatedWindows (.ok
    ([some .unsupportedCode,some .unsupportedCode,some .unsupportedCode,
      some .unsupportedCode,some .unsupportedCode,some .unsupportedCode,
      some .unsupportedCode,some .unsupportedCode,some .unsupportedCode],
     .ok (.logicalRdiRsi .band),.ok (.logicalRdiRsi .bxor)))

def rejectedSyntax : List (String × List Byte) :=
  [("trailing NOP after RET", [0xc3,0x90]),
   ("two returns", [0xc3,0xc3]),
   ("logical instruction after RET", [0xc3,0xf0,0x48,0x09,0x37,0xc3]),
   ("trailing byte after logical body", [0xf0,0x48,0x09,0x37,0xc3,0x90]),
   ("duplicate LOCK prefix", [0xf0,0xf0,0x48,0x09,0x37,0xc3]),
   ("reordered REX/LOCK prefixes", [0x48,0xf0,0x09,0x37,0xc3]),
   ("missing LOCK prefix", [0x48,0x09,0x37,0xc3]),
   ("32-bit operand alias", [0xf0,0x09,0x37,0xc3]),
   ("different address register", [0xf0,0x48,0x09,0x30,0xc3]),
   ("SIB alias for RDI", [0xf0,0x48,0x09,0x34,0x27,0xc3]),
   ("zero-displacement alias", [0xf0,0x48,0x09,0x77,0x00,0xc3]),
   ("immediate OR encoding", [0xf0,0x48,0x83,0x0f,0x01,0xc3]),
   ("unsupported ADD opcode", [0xf0,0x48,0x01,0x37,0xc3]),
   ("unsupported return immediate", [0xc2,0x00,0x00])]

def syntaxSpawnFault (bytes : List Byte) : Except Fault (Option Fault) := do
  let (state, start, _) ← setup bytes
  return faultOf (spawn state 0 start)

#eval do
  for (name, bytes) in rejectedSyntax do
    expect s!"strict layout: {name}" (checkLayout bytes) none
    expect s!"checked spawn: {name}" (syntaxSpawnFault bytes) (.ok (some .unsupportedCode))
  IO.println "strict layout rejects trailing, aliased and unsupported synthetic encodings"

/-- Only the explicit hostile-state tests below use this projection override.
It is NOT a managed action or a claim of managed WellFormed preservation. -/
def rawSpace (state : State) (space : Space) : State :=
  { state with shared := { state.shared with legacy := { state.shared.legacy with
    shared := { state.shared.legacy.shared with resources := {
      state.shared.legacy.shared.resources with space := space } } } } }

def spawnCurrentInputs : Except Fault (List (Option Fault)) := do
  let (state, start, _) ← setup [0xf0,0x48,0x31,0x37,0xc3]
  let wrongLiteral := faultOf (spawn state 0 { start with bytes := [0xf0,0x48,0x09,0x37,0xc3] })
  let (badTail, tailStart, _) ← setup [0xf0,0x48,0x31,0x37,0x90]
  let wrongTerminal := faultOf (spawn badTail 0 { tailStart with bytes := [0xf0,0x48,0x31,0x37,0xc3] })
  let (nonExecutable, _) ← mutate state (.protect 0 start.codeTicket readOnly)
  let deniedCode := faultOf (spawn nonExecutable 0 start)
  -- These are loader/admission inputs before any worker exists. An unreadable
  -- eighth caller byte must fail the actual read even with a valid ticket.
  let hiddenCaller := rawSpace state
    (protectUnchecked state.shared.legacy.shared.resources.space ⟨32775,1⟩ inaccessible)
  let deniedCaller := faultOf (spawn hiddenCaller 0 start)
  let wrongCallerAllocation := faultOf (spawn state 0 { start with stackTicket := start.codeTicket })
  let (writable, _) ← mutate state (.protect 0 start.stackTicket readWrite)
  let (changed, _) ← mutate writable (.store64 0 start.stackTicket 32768 0x0000800000000000)
  let currentTarget := faultOf (spawn changed 0 start)
  return [wrongLiteral,wrongTerminal,deniedCode,deniedCaller,wrongCallerAllocation,currentTarget]

#eval expect "spawn checks all literal current bytes, execute permission and current private caller"
  spawnCurrentInputs (.ok
    [some .unsupportedCode,some .unsupportedCode,some .unsupportedCode,
     some (.machine (.inaccessibleStack 32775)),
     some (.atomic (.legacy (.authority .outsideAllocation))),
     some (.machine (.noncanonicalReturn 0x0000800000000000))])

def callerBounds : Except Fault (List (Option Fault) × Except Error Word × Except Error Word × Word) := do
  -- Both complete eight-byte reads succeed. The low-half endpoint makes the
  -- post-RET RSP noncanonical; the very top endpoint would wrap RSP to zero.
  let (low, lowStart, _) ← setup [0xc3] 0x00007ffffffffff8
  let (top, topStart, _) ← setup [0xc3] 0xfffffffffffffff8
  let lowRead := readWord (memory low) 0x00007ffffffffff8
  let topRead := readWord (memory top) 0xfffffffffffffff8
  let lowFault := faultOf (spawn low 0 lowStart)
  let topFault := faultOf (spawn top 0 topStart)
  let (near, nearStart, _) ← setup [0xc3] 0xfffffffffffffff0
  let (started, identifier) ← spawn near 0 nearStart
  let (done, _) ← dispatch started identifier false
  let (_, context) ← join done 0 identifier
  return ([lowFault,topFault],lowRead,topRead,context.registers .rsp)

#eval expect "RET-only admission enforces strict caller bound and canonical post-RET stack"
  callerBounds (.ok ([some .unexpectedStep,some .unexpectedStep],.ok 8192,.ok 8192,0xfffffffffffffff8))

structure RetOnlyObserved where
  ranks : List Nat
  events : List (Option OS.Atomics64.Event)
  capturedCounts : List Nat
  faults : List (Option Fault)
  staleStackRead : Except OS.Borrowing.ReadFault Word
  freshStackRead : Except OS.Borrowing.ReadFault Word
  returned : Word × Word
  deriving BEq, Repr

/-- Empty logical bodies must still execute one RET, retain authority through
completion, and revoke it at join. Re-spawning must not revive old authority. -/
def retOnly (af : Bool) : Except Fault RetOnlyObserved := do
  let (initial, start, _) ← setup [0xc3]
  let (started, identifier) ← spawn initial 0 start
  let before ← atWorker started identifier
  let (done, event) ← dispatch started identifier af
  let after ← atWorker done identifier
  let repeated := faultOf (dispatch done identifier (!af))
  let codePinned := faultOf (mutate done (.protect 0 start.codeTicket readOnly))
  let stackPinned := faultOf (mutate done (.release 0 start.stackTicket))
  let cellPinned := faultOf (retire done 0 start.cell)
  let (joined, context) ← join done 0 identifier
  let (fresh, next) ← spawn joined 0 start
  let freshWorker ← atWorker fresh next
  let staleDispatch := faultOf (dispatch fresh identifier af)
  let staleHandle := faultOf ((OS.Atomics64.logicalUpdate .bxor fresh.shared
    (principal identifier) before.handle 1).mapError OS.AtomicThreads64.Fault.atomic)
  let staleStack := OS.Borrowing.loadWord64 fresh.shared.legacy.shared
    (principal identifier) before.stackLoan 32768
  let freshStack := OS.Borrowing.loadWord64 fresh.shared.legacy.shared
    (principal next) freshWorker.stackLoan 32768
  let (freshDone, nextEvent) ← dispatch fresh next (!af)
  let nextAfter ← atWorker freshDone next
  let (allJoined, _) ← join freshDone 0 next
  -- Successful operations prove the pins were discharged, rather than merely
  -- inspecting whether the fixture's stored handle/loan fields disappeared.
  let (unprotected, _) ← mutate allJoined (.protect 0 start.codeTicket readOnly)
  let _ ← mutate unprotected (.release 0 start.stackTicket)
  return ⟨[before.rank,after.rank,freshWorker.rank,nextAfter.rank], [event,nextEvent],
    [after.events.length,nextAfter.events.length],
    [repeated,codePinned,stackPinned,cellPinned,staleDispatch,staleHandle],
    staleStack,freshStack,(context.rip,context.registers .rsp)⟩

#eval do
  let expected : RetOnlyObserved :=
    ⟨[1,0,1,0],[none,none],[0,0],
      [some .alreadyCompleted,some (.atomic (.legacy (.authority .borrowed))),
       some (.atomic (.legacy (.authority .borrowed))),some (.atomic .liveHandles),
       some .missingThread,some (.atomic .missingHandle)],
      .error (.authority .missingLoan),.ok 8192,(8192,32776)⟩
  expect "RET-only rank/events, completed pins and stale authority, AF=false" (retOnly false) (.ok expected)
  expect "RET-only rank/events, completed pins and stale authority, AF=true" (retOnly true) (.ok expected)
  IO.println "RET-only progress, completed-resource pinning and fresh-spawn revocation checks passed"

/-- Hostile raw-state injections, OUTSIDE managed WellFormed histories. Each
starts after successful checked spawn and dispatch. No invariant theorem is
applied to the injected states. The assertion is actual dispatch rejection,
not just a resource validator result or a claim that hostile mutation is legal.
The lower layer already tests permission sweeps; here one late operand byte,
one late fetch byte, the caller's last byte and the current epoch target the
scheduler's use of a fresh current snapshot at later cursors and RET. -/
def hostileDispatch : Except Fault
    (List (Option Fault) × List (Option OS.Atomics64.Event)) := do
  let (initial, start, ticket) ← setup [0xf0,0x48,0x31,0x37,0xf0,0x48,0x09,0x37,0xc3]
  let (started, identifier) ← spawn initial 0 start
  let (later, first) ← dispatch started identifier false
  let operandDenied := rawSpace later
    (protectUnchecked later.shared.legacy.shared.resources.space ⟨65543,1⟩ readOnly)
  let deniedRmw := faultOf (dispatch operandDenied identifier true)
  let codeDenied := rawSpace later
    (protectUnchecked later.shared.legacy.shared.resources.space ⟨4103,1⟩ readOnly)
  let deniedLaterFetch := faultOf (dispatch codeDenied identifier true)
  -- This explicitly bypasses the typed64 reservation by using a legacy API.
  let (epochChanged, _) ← (OS.Atomics.mutate later.shared.legacy (.transfer 0 ticket 0)).mapError
    (fun fault => OS.AtomicThreads64.Fault.atomic (.legacy fault))
  let staleEpoch := faultOf (dispatch { later with shared := { later.shared with legacy := epochChanged } }
    identifier true)
  let (returning, second) ← dispatch later identifier true
  let retDenied := rawSpace returning
    (protectUnchecked returning.shared.legacy.shared.resources.space ⟨4104,1⟩ readOnly)
  let deniedRetFetch := faultOf (dispatch retDenied identifier false)
  let stackDenied := rawSpace returning
    (protectUnchecked returning.shared.legacy.shared.resources.space ⟨32775,1⟩ inaccessible)
  let deniedRetRead := faultOf (dispatch stackDenied identifier false)
  let (_, last) ← dispatch returning identifier false
  return ([deniedRmw,deniedLaterFetch,staleEpoch,deniedRetFetch,deniedRetRead], [first,second,last])

#eval expect "outside-managed-WF current permission/epoch injections reject actual later dispatch"
  hostileDispatch (.ok
    ([some (.atomic (.machine (.writeDenied 65536))),some (.machine (.inaccessibleInstruction 4103)),
      some (.atomic (.ownership .staleEpoch)),some (.machine (.inaccessibleInstruction 4104)),
      some (.machine (.inaccessibleStack 32775))],
     [some ⟨1,⟨0⟩,⟨0⟩,⟨.bxor,0,⟨65536,0x8000000000000001,0x8000000000000001⟩⟩⟩,
      some ⟨1,⟨0⟩,⟨0⟩,⟨.bor,0,⟨65536,0x8000000000000001,0x8000000000000001⟩⟩⟩,none]))

end EDSL.Tests.AtomicSetThreads64Adversarial

#audit_edsl
