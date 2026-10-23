# Structural CFG certificates

`EDSL.X86.Sequential.StructuralCFG` checks the structure of an exact machine-code
window independently of instruction effects. It reuses the production decoder,
CFG data, instruction lengths, partition checker and fetch transport. This is a
foundation for verifying shared-memory programs with branches and loops.

A successful structural check establishes:

- Every proposed instruction matches the actual selected bytes.
- The nodes partition the complete selected window, within explicit byte and
  node limits. The default remains 64 bytes and 32 nodes.
- Entry is a cutpoint, every computed successor names a node boundary, and
  depth decreases along edges whose destinations are not cutpoints.
- Given current executable `CodeAt` memory and the corresponding RIP, each
  selected instruction is decoded from that actual memory.

These facts do not establish instruction behavior, memory safety, termination,
lock ownership or a scheduler contract. Consumers must prove the appropriate
resource and effect rules and retain executable text at each actual step.
Cutpoints permit cycles; structural depth is not a loop-termination argument.

## Using the checker

The namespace is `EDSL.X86.Sequential.CFG.Structural`. Candidate graphs use the
existing `CFG.Graph` and `CFG.Node` types. They remain untrusted hints.

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

The current graph discovery tools and read-only VCG retain their existing
admission policy. They do not acquire effectful execution support through this
module. Graph proposals for the structural API can be supplied independently;
future effectful consumers need their own proved execution/resource bridge.

## Retaining read-only verification

The existing `CFG.Valid`, `CFG.checkWith` and read-only execution APIs are
unchanged. `Structural.Valid.ofReadOnly` forgets only the effect restriction.
`Structural.Valid.toReadOnly` restores the original validity proposition when
every node satisfies `CFG.readOnly`.

`Structural.checkWith_readOnly_iff` proves, for every graph, byte window and
profile, that the old checker is exactly the structural check plus that original
per-node read-only condition. Structural admission cannot substitute for the
missing policy obligation in a read-only execution theorem.

## Validation and next obligations

`tests/StructuralCFG.lean` checks the complete frozen Clang spinlock-acquire
window as a structural example. Its real XCHG is accepted structurally and
rejected by the existing read-only checker. A branch-interior mutation updates
both the encoded displacement and its graph proposal: decoding and partitioning
still succeed, while successor closure rejects it. Other controls cover stale
instruction proposals, truncated fetch, incomplete extents, missing entry
cutpoints, invalid depths and explicit admission limits.

The tests belong to `CFGProfileTests` and the full corpus replay target. This
example supplies no spinlock behavior certificate or additional corpus credit.
The next shared-memory layer must connect actual decoded effects to current
ownership, atomic events, store publication and the production scheduler.
