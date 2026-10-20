# Explicit CFG verification profiles

The implementation uses one structural checker invariant and one proof
stack, with explicit static admission data. `CFG.Profile` supplies `maxBytes`,
`maxNodes`, and a proof that `maxBytes + 15 ≤ 2^64`. The slack prevents wrapping
the finite static decoder's fetch offsets. It changes neither the decoder nor
the instruction set. Zero caps are permitted and reject nonempty programs.

`CFG.checkWith`, `analyzeWith`, and `discoverWith` select that profile explicitly.
`CFG.Valid bytes graph profile` carries the selected bounds in its type.
Omitting the profile in `Valid`, or using the original `check`, `analyze`, or
`discover`, means exactly 64 bytes and 32 nodes. Existing field/constructor
order is retained. `VCGen.certifyWith` additionally checks actual executable RAM
and the current RIP; the original `certify` retains the default profile.

The trust argument is unchanged across profiles: discovery proposes a finite
graph; the checker independently validates a complete positive-length partition,
decode agreement, read-only instructions, entry cutpoint, every possible
successor, and interior depth decreases. Offset injectivity follows from that
partition and the profile's no-wrap bound. Current executable `CodeAt` supplies
the entire byte window and the runtime mapping's no-wrap/canonical fetch facts.
Decode transport uses actual RAM and RIP. The same production executor, bounded
WP, sparse cutpoint WP, all-choice composition, prefix policy, and caller-resource
adapters consume the profile-indexed validity proof.

The only propagation outside generic CFG/VCG is
`Sequential.code_fetch_transport_of_bound`; the original
`code_fetch_transport` keeps its 64-byte premise. Legacy artifact import,
`vcgen_graph`, and the 32-index successor tactic keep their existing limits.
Larger clients select the explicit checker/discovery API and supply checked
graph data; this does not enlarge those frontends or task admission.

These caps govern structural admission, not execution fuel, dynamic loop rank,
packet decoding, source inputs, compiler options, or task registration. Larger
admission adds no writes, atomics, syscalls, unsupported opcodes, native CPU/OS
claims, certificates, corpus coverage, or cost optimality. Trusted registered
tasks and packet limits are unchanged. A failed discovery/check/WP is not proof
of a defect or of successful execution. Branch targets use the existing modular
64-bit ISA arithmetic; closure must find an actual checked instruction boundary,
and actual execution retains its canonical-target checks.

`tests/CFGProfiles.lean` exercises two owned literal 68-byte functions through
production decoding, bounded/sparse WP, actual all-choice runs and caller-resource
transport. Controls cover both caps, the default 65-byte rejection, malformed
partitions, interior/wrapped branches, suffix mutation, canonical mapping/return
failures, wrong results and failed dynamic ranks. An early RET still requires
every padding byte to be partitioned, decoded and authenticated.
