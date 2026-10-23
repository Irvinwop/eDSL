# Mixed instruction graphs

`EDSL.X86.VCGen.MixedCFG` checks complete machine-code windows containing
ordinary instructions and locked arithmetic RMW instructions. It uses the
production TSO64 decoder. A successful check proves the static instruction
partition and control-flow structure; clients separately prove behavior and
satisfy the scheduler's current resource checks.

Select both the instruction family and static caps explicitly:

```lean
open EDSL.X86.VCGen.MixedCFG
-- checkWith family caps bytes proposedGraph : Bool
-- analyzeWith family caps bytes : Except DiscoveryError (Graph family)
```

The caps use `Sequential.CFG.Profile`: maximum bytes, maximum nodes and a
no-wrap bound. `.xaddOnly` retains the original locked XADD domain;
`.arithmetic` also permits the supported qword ADD-immediate and INC forms.
Ordinary-memory authority profiles remain a separate scheduler input.

The checker authenticates every node against the exact bytes, checks a positive
contiguous partition covering the whole window, and requires every branch or
fallthrough target to be an instruction boundary. RET has no static successor.
Locked instructions retain their real tags and lengths. In particular, a final
INC without a following instruction fails successor closure.

Cutpoints and depths are checked certificate data. Depth decreases along edges
into noncut nodes, bounding acyclic interiors between cuts. Loop termination
and dynamic instruction counts require separate client invariants.

Discovery scans the complete window, including instructions after the first
RET, with the selected node cap as fuel. Its proposal is admitted only after
the independent checker succeeds. Unsupported bytes, insufficient caps and
invalid graphs return an error without a fallback profile or omitted suffix.

## From static bytes to current execution

`MixedCFGTransport` supplies `Valid.decoded`, `Valid.guarded_decoded`,
`Valid.codeFits` and `Valid.issue_eq_dispatch`. They require the authenticated
whole window in current executable memory and its containment in the original
code loan. Dispatch also requires the installed running worker and current
code and caller leases. The conclusion retains the production executor,
including its resource failures, FIFO blocking and shared-memory re-decoding.

A locked fallthrough edge describes retirement. A blocked issue retains the
whole state and takes no such edge. Graph validity supplies no atomic handle,
operand ownership or successful future execution. RET still reads the current
authorized caller slot, checks the loaded target's canonicality and advances
RSP; a particular expected return target belongs in the client's contract.

## Complete frozen counter windows

`EDSL.Corpus.V1.CounterMixedGraphs` binds the complete `c_counter_worker` named
extents to the original literal ELF files and checks their typed graphs:

| Artifact | Complete bytes / nodes | Explicit caps | Retained structure |
| --- | --- | --- | --- |
| GCC | 49 / 17 | 64 / 32 | Both RETs, ENDBR64, three LOCK ADD sites |
| Clang | 86 / 28 | 128 / 32 | Exact NOP13, nine distinct LOCK INC sites |

Both use `.arithmetic`. Named binding uses the same explicit byte cap as the
graph. This establishes static admission, with no additional certified function
count. Exact increment counts, interleavings, ABI, resource lifetimes and
completion remain separate obligations. The existing ordinary Resumable
interface continues to accept ordinary graphs only.

Run `lake build MixedCFGTests`. The regressions check real decoder boundaries,
insufficient caps, default-family rejection, missing suffixes, branches into
padding and terminal-INC closure. The full certificate gate includes these
regressions in its fresh replay and axiom audit.
