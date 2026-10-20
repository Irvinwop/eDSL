# Exact frozen byte-equality bodies

The body proofs target the unchanged row 20 GCC 46-byte and Clang 68-byte
`c_bytes_equal` functions and the independent `Grading.ByteEquality.spec`.
The result observes only low8 RAX: one exactly when the complete lists are
equal, zero otherwise. Other nonzero byte values are rejected. No upper32 or
upper56 clearing requirement is imposed; Clang's empty B001 path preserves
the upper 56 bits.

`ByteEqualityWindows.checked` authenticates the full frozen ELF, requested
name, unique complete extent, executable mapping and every byte. GCC uses the
existing default admission profile. Clang uses an explicit 128-byte, 32-node profile;
the 64-byte default still rejects it. Its exact NOP15 and final RET at offset 67 remain
part of the checked window. Decoder acceptance does not prove equality.

The proofs use the production executor and sparse cutpoint VCG. GCC's cursor
indexes the next pair; Clang first compares pair 0, then uses RCX for the next
unread pair, possibly the complete extent. An equal-prefix invariant and a
natural remaining-length rank prove termination for every admitted full-width
count, without a fixed execution-fuel admission premise. Admission includes
equal snapshot lengths `n < 2^64`, argument bindings, current code and the
original callable stack/return conditions. The model instruction bound is
`10 * (n + 2)`. Paired reads, frames,
prefix advancement and rank mathematics reuse the existing byte-comparison
helpers through a result-only Invocation/Pre view. No interpreter or paired
resource implementation is duplicated.

The resulting callable contract retains complete Memory and permission maps,
original caller return/RSP, SysV callee-saved registers and every
nonarithmetic flag, for every choice stream. The existing buffer-call cutpoint
bridge retains current original read authority at every actual continuing
prefix and return. Compatible buffer/code/caller aliases require matching
actual bytes, rather than disjointness. Empty buffers need no DATA access,
canonical address, allocation or DATA loan.

These are the represented sequential callable semantics. Stable ordinary RAM,
absence of asynchronous interference and the existing target profile remain
environmental assumptions, including support for the exact long-NOP form.
Physical CPU refinement, native/Linux execution, source/compiler equivalence,
minimum cost, task registration, certificates and corpus credit are separate
claims. The finite execution regressions do not replace the universal proof.
