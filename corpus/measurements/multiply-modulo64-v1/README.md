# Multiplication modulo 2^64 certificates v1

Source snapshot: `ba6f8a9533c2a13ba3c55966c01478ed062a4f5e`.
The milestone adds both unchanged `c_mul_mod64` outputs: **19/40 functions,
38/80 compiler artifacts, three distinct concurrent functions**, with
**21 functions / 42 artifacts** remaining. Both compiler outputs must satisfy
the independent contract before a function counts. Historical measurements
and the original frozen v1 inputs remain unchanged.

| Compiler | File extent | Virtual-address extent | Size | Exact bytes |
| --- | --- | --- | ---: | --- |
| GCC | [11696, 11708) | [4206000, 4206012) | 12 | `f3 0f 1e fa 48 89 f8 48 0f af c6 c3` |
| Clang | [4912, 4920) | [4199216, 4199224) | 8 | `48 89 f8 48 0f af c6 c3` |

The [independent specification](../../../EDSL/Arithmetic64/Multiply.lean)
requires the full64 RAX result to equal the unbounded natural product modulo
2^64 for every pair of full64 operands. Admission concerns present inputs,
bytes and current resources; useful-domain witnesses are separate. The callable
contract preserves complete memory, callee-saved registers and nonarithmetic
flags, returns to the original caller address with RSP advanced by eight, and
retains current code/caller authority at every actual continuing prefix.

Both bodies reuse the [flag-vector VCG and resource bridge](../../../docs/flag-choices.md),
neutral named-ELF adapter and trusted execution/task registry. The vector model
permits PF, AF, ZF and SF to vary independently after IMUL; CF and OF follow
signed overflow. The stored acceptance checks also conclude the literal
supplied operands' product from the installed caller constructors, preventing
an argument-ignoring constructor from narrowing this obligation silently.

The original complete named ELFs are certified separately from the minimal
synthetic ELF containers used by packet controls. The latter establish parser
and packet admission behavior and add no corpus artifacts.

The [validation record](validation.json) identifies the source, complete CI
batch, exact artifact digest and both full-gate runs. All fourteen original
push workflows and 23 jobs passed. The corpus CI gate built 1,350 jobs, audited
37,415 declarations, checked 3,455 command expectations and replayed
`CorpusFullReplay` in a fresh kernel environment from 01:32:17 to 01:41:34 UTC
on 2026-10-23. The matching local full gate also passed, including independent
rehashing of its source, object, input and closed receipt inventories.
Both gates include the stored named acceptance assertions, 605 report rejection
controls, and registered multiplication packets with eight acceptances and
sixteen exact status-5 kernel rejections. Report prose is not semantic evidence;
the typed contracts and actual kernel checks establish the modeled results.

The model retires four instructions for GCC and three for Clang, including RET
and GCC's original ENDBR64. These are exact modeled totals, without a physical
minimum instruction count or timing claim. The target requires stable ordinary RAM,
64-bit mode, disabled CET/IBT/shadow stacks and no asynchronous interference.
Native CPU/Linux correspondence, source/compiler preservation, general
concurrency and whole-kernel verification remain separate obligations.
