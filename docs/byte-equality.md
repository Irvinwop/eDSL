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
part of the checked window. The exact NOP15 bytes are
`66 66 66 66 66 66 2e 0f 1f 84 00 00 00 00 00`.
Decoder acceptance does not prove equality.

The proofs use the production executor and sparse cutpoint VCG. GCC's cursor
indexes the next pair; Clang first compares pair 0, then uses RCX for the next
unread pair, possibly the complete extent. An equal-prefix invariant and a
natural remaining-length rank prove termination for every admitted full-width
count, without a fixed execution-fuel admission premise. Admission includes
equal snapshot lengths `n < 2^64`, argument bindings, current code and the
original callable stack/return conditions. For every modeled undefined-flag
choice stream, `10 * (n + 2)` is an upper bound on retired model instructions,
with no minimum-cost or physical-timing claim. Paired reads, frames,
prefix advancement and rank mathematics reuse the existing byte-comparison
helpers through a result-only Invocation/Pre view. No interpreter or paired
resource implementation is duplicated.

The resulting callable contract retains complete Memory and permission maps
and current original read authority at every actual continuing prefix and
return, for every choice stream. Original caller return/RSP, SysV callee-saved
registers and every nonarithmetic flag satisfy the ABI/frame conditions at
return. Compatible buffer/code/caller aliases require matching
actual bytes, rather than disjointness. Empty buffers need no DATA access,
canonical address, allocation or DATA loan.

These are the represented sequential callable semantics. Stable ordinary RAM,
absence of asynchronous interference and the existing target profile remain
environmental assumptions, including x86-64 long mode, disabled CET/IBT/shadow
stacks and support for the exact NOP15 form above.
`Grading.BufferTask` registers this result as `.equalBytes`.
`ByteEqualityCertificates.certificate` composes the universal body proof with
the full named-file check and a useful call at the actual loaded entry. Its
explicit byte cap is 64 for GCC and 128 for Clang. The original 64-byte admission
path rejects the complete Clang function; it cannot select a smaller prefix.

`ByteEqualityResources` reuses the initialized paired-comparison world with
[`ReadOnlyCallTransport`](read-only-call-transport.md). Code attachment retains
the original caller slot, worker, paired snapshots and exact input-loan
selectors without reinitializing RAM. The complete memory and current resource
authority remain valid at every prefix and return; the ABI return/frame
conditions hold at return. `tests/ByteEqualityCertificates.lean` applies the
actual two certificates to overlapping mismatching inputs for every choice
stream and checks the original caller, memory, permissions and loan authority.

The [byte-equality measurement](../corpus/measurements/byte-equality-v1/)
records the accepted full-project/corpus certificate gate and external fresh
kernel replay on source `383d1f1ef928f551b89a8424ae46c8bb019ce2e2` in
[Frozen corpus run 39454868896](https://github.com/Irvinwop/eDieSeL/actions/runs/39454868896).
See [commit-specific CI results in GitHub Actions](https://github.com/Irvinwop/eDieSeL/actions).
Physical CPU,
Linux/kernel/whole-OS refinement and source/IR/compiler preservation remain
separate obligations. The installed `edsl-grade` packet interface remains
scalar-only; `.equalBytes` uses the typed buffer-certificate API. No equality
packet result is claimed. Existing scalar body/reference packets passed under
the unchanged 300,000-step / depth-128 limits. Finite native regressions do not
strengthen the modeled contract or replace the universal proof.
