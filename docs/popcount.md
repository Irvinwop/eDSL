# Popcount loops over full64 inputs

Both unchanged frozen `c_popcount_loop` bodies are proved against an independent
set-bit cardinality contract. The result is the unsigned low32 cardinality;
the upper half of RAX is unconstrained by the task. The domain includes every
64-bit input, including zero, the high bit alone and all ones. A useful current
call at `0x81` establishes inhabited admission separately.

This row-11 milestone brought conditional coverage to **12/40 functions
and 24/80 compiler artifacts**, including one distinct concurrent function under
the existing managed model. The new
[measurement record](../corpus/measurements/popcount-v1/) preserves the earlier
11/40 milestone and all frozen compiler inputs.

## Reusable proof components

| Responsibility | Shared implementation |
| --- | --- |
| Independent mathematical result and progress | [WordMath.Popcount](../EDSL/WordMath/Popcount.lean), [Arithmetic64.Popcount](../EDSL/Arithmetic64/Popcount.lean) |
| Width32 counter arithmetic and signed disp8 addresses | [Counter32](../EDSL/X86/Sequential/Counter32.lean), production [decoder](../EDSL/X86/Sequential/Decode.lean)/[executor](../EDSL/X86/Sequential/Machine.lean) |
| Sparse generated blocks and current-resource policy | [CutpointPolicy](../EDSL/X86/VCGen/CutpointPolicy.lean), [VCGen.PureCall](../EDSL/X86/VCGen/PureCall.lean) |
| Register, RAM, flags and terminal return frame | [PureCall.Frame](../EDSL/PureCall/Frame.lean) |
| Exact frozen code, invariants and result evidence | [PopcountCode](../EDSL/Corpus/V1/PopcountCode.lean), [PopcountBodies](../EDSL/Corpus/V1/PopcountBodies.lean) |
| Complete file/name/extent and useful current resources | [PopcountWindows](../EDSL/Corpus/V1/PopcountWindows.lean), [PopcountCertificates](../EDSL/Corpus/V1/PopcountCertificates.lean) |

The mathematical specification counts set positions. It does not evaluate the
compiled clearing-bit loop. A separate theorem proves that `x & (x - 1)` removes
exactly one set bit for nonzero `x`. The natural invariant is accumulated count
plus remaining cardinality equals initial cardinality. This bounds the machine
counter and supplies the strict decreasing rank. A finite CFG block bound does
not restrict the number of loop iterations or mathematical input values.

The instruction extension supports sign-extended imm8 ADD32, INC32 preserving
CF, and signed disp8 LEA64 across the admitted register/address forms. ADD32
and INC32 clear the destination's upper half. LEA computes a full64 address
without reading the addressed memory. Unsupported encodings retain explicit
failure; the extension does not admit the same new addressing forms for every
memory instruction.

Each artifact supplies its own `gcc_generated`/`clang_generated` and
`gcc_semantics`/`clang_semantics` to the shared scalar cutpoint bridge and
certificate constructors. A proof packet for one compiler therefore need not
carry the other's annotation proofs. Required dependencies stay intact and
kernel checked; no dependency trimming, trust promotion, new interpreter or
per-program executable is involved. The compiler-indexed family remains a
convenience interface over the two proofs.

| Compiler | File offset | Virtual address | Complete function bytes |
| --- | ---: | ---: | ---: |
| GCC | 11776 | 4206080 | 31 |
| Clang | 4976 | 4199280 | 28 |

The complete final ELF, unique requested name and full declared extent are
checked independently from the body proof. Both artifacts use the registered
`populationCount64` task, equal to `Arithmetic64.populationCount`: full64 RDI
is bound, all Word64 inputs are admitted, and only unsigned low32 cardinality
is required. GCC's ENDBR64 remains in the exact
code under the recorded CET-off target. Every admitted AF stream returns the
specified result, preserves complete RAM and permissions, restores callee-saved
registers and returns the original caller's current resource authority. The
return-slot read must succeed in current modeled memory; no future execution or
result condition is assumed in admission.

Both scalar certificates require the selected full-image mapping, fresh model
installation, code/caller separation and current code and original eight-byte
caller-slot loans with their owners/epochs. The shared constructor inhabits a
declared model world; it does not infer native ownership or loading authority.

## Validation and limits

```sh
lake build PopcountTests
bash scripts/verify-counter-displacement.sh
bash scripts/verify-corpus-certificates.sh --full-project
```

`PopcountTests` covers counter/address semantics, compact sparse scalar loops,
both body proofs, exact current-resource admission and fixed-task rejection
controls alongside `VerificationTests` and `UnaryTests`. The full-project gate
composes these closures with the catalogue and corpus CLI. Named parser
regressions use a private script-generated main driver so the reusable test
module composes with the CLI. See [validation](validation.md).

The owned native runner compares 3,456 observations across 72 windows with
independent arithmetic/flag expectations, then replays production decoding and
execution for both AF choices in 216 finite proof modules. Its audit covers
12,737 declarations with only the three permitted Lean axioms. This is finite
CPU conformance, separate from universal symbolic proofs. Synthetic
altered-register, altered-flag, missing,
duplicate and malformed observations must fail for their intended reasons.

The sequential target assumes stable ordinary RAM, no asynchronous interference,
the stated canonical-address profile, CET/IBT/shadow stacks disabled and supplied
logical mappings, ownership and loans. Native Linux resource authority/loading,
physical CPU and native OS refinement, source/IR/compiler preservation,
concurrent or asynchronous interference and minimum physical operation cost
remain outside these conditional certificates. [Unsigned average](unsigned-average.md)
subsequently reuses shared logical shift and bit mathematics. Parity and rotation
remain future exact binary/task/resource obligations; mathematical helpers alone
certify neither function. Failure, timeout
or unsupported code establishes no security defect.
