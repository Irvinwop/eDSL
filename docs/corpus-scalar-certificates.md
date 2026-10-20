# Shared scalar final-file certificates

The current measurement covers unsigned minimum, maximum, addition modulo
2^64 and signed low32 clamp for both frozen profiles: **4/40 functions and 8/80 artifacts**
under the recorded model assumptions. The original comparison measurement is
retained as history. No frozen concurrent entry receives certification here.

`PureCall.Spec` describes mathematical inputs, six integer argument bindings,
domain, result and usefulness. `Corpus.Scalar.certificate` requires a kernel
proof that the supplied spec equals the fixed registered task. Submissions
cannot choose a weaker spec. Concrete specs still need independent review:
arbitrary input types and predicates cannot enforce mathematical independence
by type alone.

The shared constructor realizes the six declared argument slots and proves
their bindings once. Full64 arguments retain all bits. Its low32 witness uses
zero extension, while the admission predicate permits arbitrary upper bits.
Unbound slots are unconstrained by the spec. Stack arguments beyond those six,
DATA operands, stores, atomics and syscalls need other contracts.

Complete file/name checking, fresh installation, supplied caller facts and
code/stack separation remain explicit proof obligations. The constructor
reuses `ELFResources.initial_facts`, current borrowing loans and the original
caller stack. It constructs useful calls at the actual selected symbol address
in a newly declared modeled ownership world. It does not authenticate native
principals, allocations or preexisting loans. The useful witness is independent
of execution and the desired result.

The resulting `Certificate.resource` applies to every admitted loaded call and
AF stream, with current executable text retained. It requires the registered
mathematical result, actual caller return, RSP adjustment, complete RAM and
permission equality, callee-saved registers, nonarithmetic flags and every-prefix
current-resource policy. Outside-text RAM need not equal the initial installed
image; current resources and `TextUnchanged` remain required. The witness's
chosen arguments restrict no other admitted call.

`addModulo64` fixes `Arithmetic64.addition`: two full64 arguments, domain True,
and `result.toNat = (left.toNat + right.toNat) % 2^64`. Zero and overflow remain
admitted. Usefulness only selects a nonempty independent witness. The grader's
expected-type controller selects this fixed task by name; a valid pair-program
proof does not become an addition proof.

`clampSigned32` fixes `Scalar32.clampSigned`: three signed low32 arguments in
RDI/RSI/RDX, with upper halves arbitrary. Admission requires lower ≤ upper,
including equal endpoints. The independent interval relation requires an
in-range value, the original input inside the interval, and the nearest endpoint
outside it. The registered result observes low32; a separate machine observation
establishes zero upper RAX. Its interior useful witness restricts no other call.
The [compiler client](compiler-clamp32.md) and [named-window adapter](corpus-clamp-windows.md)
reuse this same constructor and caller rather than adding a new OS domain.

`CompilerArithmetic` discharges one production-generated WP family for both
ordinary binaries. `ArithmeticWindows` reuses each compiler's complete literal
file, checked metadata and layout. New public GCC chunk normalizers avoid
private-name access and repeated whole-file normalization; all earlier GCC
data and proof bodies are unchanged. No new per-function interpreter, driver,
resource Domain or full-file literal copy is introduced.

| Compiler | Addition symbol address | File offset | Complete bytes |
| --- | ---: | ---: | --- |
| GCC | 4205984 | 11680 | `f30f1efa488d0437c3` |
| Clang | 4199200 | 4896 | `488d0437c3` |

The shared scalar constructor composes these obligations through
`V1.Arithmetic.certificate compiler`. Existing comparison caller facts and image
freshness are reused. Independent tests exercise actual installed ELF mappings
with 64-bit wrap, low32 carry and a noncanonical integer result. LEA performs
integer arithmetic without reading the computed address. A separate controller
test uses real kernel checking to accept addition and reject an unrelated valid
program proof under the addition task.

The fixed profile requires long mode, CET/IBT and shadow stacks disabled,
supported modeled instruction features, stable ordinary RAM, current code/caller
resources and absent asynchronous interference. Full native stack alignment,
CPU/OS feature state, native loading, physical refinement and source/IR
preservation remain separate. The complete files must equal the literal files
observed by the report command; future mappings or filesystem contents need
separate justification.

Separate observations establish exactly three modeled retired instructions for
GCC addition and two for Clang, including RET and GCC's original ENDBR64, with
one original STACK8 operand read and unchanged flags. These are counts for these
binaries, without global optimality, physical micro-operation or timing claims.

Run `bash scripts/verify-corpus-certificates.sh` for the eight-certificate
gate. It checks the typed instances, approved transitive axioms, actual fresh
`corpus.Certify` replay, both complete files, deterministic reports and rejection
of altered code, opaque metadata, lengths and compiler selection. The published
[measurement](../corpus/measurements/scalar-clamp32-v1/) remains distinct from
CFG admission and native observations. Failed proofs, unsupported inputs and
timeouts establish no defect.

`--full-project` additionally builds the full `EDSL` root and fresh-replays a
stored private module importing both `EDSL` and `corpus.Certify`. Each imported
proof closure is checked in that one fresh environment. Default mode retains
the standalone CLI closure. Receipts name the actual target and scope; cached
build output and source elaboration do not replace fresh replay. Axiom audit
and the deliberate negative dependency probe remain separate checks.
