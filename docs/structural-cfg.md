# Structural CFG certificates

`EDSL.X86.Sequential.StructuralCFG` checks the structure of an exact machine-code
window independently of instruction effects. It reuses the production decoder,
CFG data, instruction lengths, partition checker and fetch transport. The
namespace is `EDSL.X86.Sequential.CFG.Structural`.

A successful structural check establishes:

- Every proposed instruction matches the actual selected bytes.
- The nodes partition the complete selected window, within explicit byte and
  node limits. The default is 64 bytes and 32 nodes.
- Entry is a cutpoint, every computed successor names a node boundary, and
  depth decreases along edges whose destinations are not cutpoints.
- Given current executable `CodeAt` memory and the corresponding RIP, each
  selected instruction is decoded from that actual memory.

Cutpoints permit cycles; structural depth bounds only the interiors between
cutpoints. Consumers must retain executable text and prove the appropriate
instruction, resource and effect obligations at each actual step.

## Using the checker

Candidate graphs use `CFG.Graph` and `CFG.Node`. They remain untrusted hints.

```lean
import EDSL.X86.Sequential.StructuralCFG

open EDSL.X86.Sequential

#check CFG.Structural.checkWith
#check CFG.Structural.checkWith_sound
#check CFG.Structural.checkWith_complete
#check CFG.Structural.Valid.decoded
```

`checkWith_sound` turns a successful check into `Structural.Valid` for the same
bytes, graph and explicit profile. `Valid.decoded` transports decoding into a
caller's current executable memory. It requires the actual code mapping and RIP;
metadata alone supplies neither.

## Automatic structural discovery

Import `EDSL.X86.Sequential.StructuralDiscovery`. In `CFG.Structural`,
`analyzeWith profile bytes` returns `Except CFG.DiscoveryError CFG.Graph` and
`discoverWith profile bytes` returns `Option CFG.Graph`. `analyze` and `discover`
use the 64-byte/32-node default. These static scan limits are independent of
dynamic execution fuel.

Discovery calls `CFG.proposeWith (fun _ => true)` with the production decoder and
instruction lengths. It scans the entire selected window, including bytes after
RET, without read-only filtering or omitted effects. The proposal marks entry
and nonforward-edge targets as cutpoints and assigns depths by instruction
index. `Structural.checkWith` checks every proposal against those same bytes
and profile. Failed admission returns `invalidGraph`, without a fallback.

The `analyzeWith_sound` and `discoverWith_sound` theorems yield `Structural.Valid`;
their `_checked` counterparts yield checker acceptance. Default-profile variants
provide the same guarantees. The proposal heuristic has no completeness claim.
Diagnostics include empty input, byte/node limits, offset-specific decode or
truncation errors, and invalid graphs; the Option API discards diagnostics.
Unsupported production opcodes still fail decoding. Failure rejects the
discovery attempt and does not establish a program defect.

## Following actual store and atomic steps

`EDSL.X86.Sequential.StructuralControl` connects the checked graph to actual
production execution without imposing the read-only policy.
`Structural.Valid.continues` requires the current executable `CodeAt`, the
current node RIP, and a successful `stepWith` observation. If that observation
contains an ordinary or atomic successor state, the theorem locates its RIP
at a checked successor node. Atomic events remain in the observation; syscall
requests and returned results are boundaries outside this continuation rule.

The rule covers successful stores, legacy DWORD XCHG and XADD, and the current
registered vector effects and ordinary instructions. Failed execution provides
no continuation witness. Adding a registered effect requires proving its
fallthrough law.

This rule establishes control flow. A store can overwrite the next instruction
even though its successor RIP is a checked node. Before taking the next checked
step, a consumer must establish `CodeAt` again from an appropriate ownership and
write-separation argument.
Atomic event interpretation, store publication, scheduling and lock ownership
remain separate obligations.

The [effect-aware VCG](effect-vcg.md) composes structural admission with finite
WP checking and an executable-code frame. `Effects.certifySeparated` checks a
supplied graph, actual initial executable bytes, entry RIP and the bounded WP
together. Its shared separation adapter preserves the selected code through
supported stores and legacy DWORD atomics. Structural discovery itself proves
only structure and decoding.

## Read-only APIs

`CFG.analyzeWith`, `CFG.discoverWith`, `CFG.checkWith` and `CFG.Valid` require
the `CFG.readOnly` admission policy. `Structural.Valid.ofReadOnly` forgets only
that restriction. `Structural.Valid.toReadOnly` yields read-only validity when
every node satisfies `CFG.readOnly`.

`Structural.checkWith_readOnly_iff` proves, for every graph, byte window and
profile, that `CFG.checkWith` is exactly the structural check plus the per-node
read-only condition. Structural admission cannot substitute for the
missing policy obligation in a read-only execution theorem.

## Evidence and limits

[`tests/StructuralDiscovery.lean`](../tests/StructuralDiscovery.lean) checks the
actual automatically proposed nodes and successors of the frozen Clang
spinlock-acquire window, including its real XCHG. Read-only discovery rejects
that instruction. A branch-interior mutation produces a fresh proposal whose
decoding and partition match, while successor closure rejects it. Other controls
cover truncation, exact caps and unsupported suffixes after RET.

[`tests/StructuralCFG.lean`](../tests/StructuralCFG.lean) also checks stale
instruction proposals, incomplete partitions, missing entry cutpoints and
invalid depths. [`tests/StructuralControl.lean`](../tests/StructuralControl.lean)
checks actual store, XCHG and XADD results, permission failure, and syscall/RET
boundaries. A writable-text fixture follows a checked edge while replacing the
next RET with NOP and invalidating `CodeAt`.

Structural admission establishes no spinlock behavior, memory safety,
termination, ownership or scheduler contract. A bridge to OS execution must
evolve the current world and ownership/epochs coherently with actual effects,
interpret atomic events and publication, and connect to the production
scheduler. Neither structural validity nor a CPU predicate referring to an
initial OS world supplies that bridge.
