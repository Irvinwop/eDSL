# Shared byte comparison and exact padding

This foundation extends the production Sequential decoder, executor, CFG and
VCG, with the same operations lifted into CallReturn. It grants no new corpus
coverage. No full `c_bytes_equal`
behavior, certificate, physical CPU or native refinement is established here.

## Register left, memory right

`Instruction.cmpRegMem8 left address prefixed` subtracts one memory byte from
the low eight bits of the prestate register. It uses `cmpFlags8` and the actual
`readDataByte` primitive. The existing `cmpMemReg8` keeps its opposite operand
order. A failed read remains an error; there is no register comparison fallback.

The decoded subset is opcode **3A /r**, memory mod00, without a prefix or with
exactly one **40..47 non-W REX** byte. Unprefixed left codes0..3 select AL/CL/DL/BL;
codes4..7 would select AH/CH/DH/BH and reject. With REX, the complete LOW8 bank
is modeled: REX.R extends the left register, B the base and X the SIB index.
Prefix presence records the exact length. Supported lengths are2/3 bytes
without REX and3/4 with REX, depending on SIB presence.

Addresses use the existing full64 helpers: a real plain base, or a SIB with a
real base and index and any scale. Plain encoded base4 requires SIB; encoded
base5 and SIB base5 reject even with B=1. Encoded SIB index4 rejects when X=0;
X=1 selects R12. Displacements, absent bases/indices, RIP-relative addressing,
address-size overrides, legacy/stacked prefixes and W=1 aliases are unsupported
for this new operand family. Existing register-mode CMP and memory-left38 /r
support stay distinct. Internal suffix helpers assume their supplied opcode,
prefix and ModRM have been authenticated by the enclosing decoder; only the
public decoder authenticates the complete encoding.

`ByteCompareContext` and `execute_cmpRegMem8_contract` describe arbitrary
states, registers and addresses, including aliases and RSP. They prove actual
DATA1 load success, full GPR and Memory equality (all permission maps included),
exact RIP advance, all six defined arithmetic flags and all other flag bits.
`execute_cmpRegMem8_success_iff`, observation inversion and generic read-origin
proofs retain the real prestate address and read. Both undefined-choice values
produce the same complete observation. The instruction has no store intent,
lock, return or syscall effect.

`VCGen.wp_cmpRegMem8_iff` is a rule for the existing bounded production WP. It
requires the actual load and the actual read permission in the current state,
then the real fallthrough continuation. `BufferCall.Current.cmpRegMem8_step`
derives load success and borrowing permission from the current buffer contract
and a DATA1 footprint, preserving the same resource world. PureCall's original
STACK8 authority never permits DATA1, including at RSP or the return slot.
Reading through RSP creates no new caller or buffer authority.

The complete frozen Clang window also needs unprefixed B9 imm32. Sequential
completes the missing B9/BB/BC/BD low-bank MOV32 immediate forms using the
existing legacy MOV32 executor; B8/BA/BE/BF retain legacy decoder priority.
All five instruction bytes require execute permission. The destination is
zero extended from32 bits, all other registers/flags/Memory are preserved,
and no operand memory read occurs. Prefixed forms remain unsupported by this
completion. The original legacy decoder and its supported subset are unchanged.

## Exact thirteen- and fifteen-byte NOPs

`NopEncoding.thirteen` and its canonical `bytes` are exactly:

```text
66 66 66 66 2e 0f 1f 84 00 00 00 00 00
```

`NopEncoding.fifteen` and its canonical `bytes` are exactly:

```text
66 66 66 66 66 66 2e 0f 1f 84 00 00 00 00 00
```

The decoder fetches and authenticates all thirteen or fifteen required bytes in
order. It checks the common four `66` bytes, then admits only the exact suffix
selected by byte5 (`2e` for NOP13, `66` for NOP15). A missing or
nonexecutable byte reports `inaccessibleInstruction` at that byte's address;
a fetched mismatch reports unsupported encoding before any later fetch. It does
not fetch byte14 for NOP13 or byte16 for NOP15,
split the sequence, strip prefixes, evaluate the apparent address or read DATA.
Every GPR, every flag and the complete Memory remain unchanged. The ordinary
fallthrough is RIP+13 or RIP+15 for every choice. Other supported NOPs remain the exact
1..6 and9 byte forms; this is not a general prefix or hint-NOP grammar.
Unlisted forms reject conservatively. `execute_nop_context` and `wp_nop_iff`
share the existing execution and WP machinery. `step_nop13_context` binds the
thirteen current bytes through `CodeAt`, preserving arbitrary registers, flags
and Memory without requiring byte14 execute permission or apparent-operand RAM.

The architectural basis is Intel SDM **253666-060US / 253667-060US, September
2016**: Volume2A CMP pp.3-153..154, REX §2.2.1 and maximum instruction length;
Volume2B NOP p.4-163. CMP3A uses register minus r/m8 and defines CF/PF/AF/ZF/SF/OF;
NOP leaves flags/registers intact and performs no operand memory access.
See the official [Volume2A](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2a-manual.pdf)
and [Volume2B](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2b-manual.pdf).

Intel's recommended NOP table ends at9 bytes; it does **not** specify an
arbitrary repeated-prefix grammar. The exact13- and15-byte sequences have separate
primary assembler evidence: GNU binutils maintainer H.J. Lu's
[20 March 2015 committed patch](https://ecos.sourceware.org/ml/binutils/2015-03/msg00260.html),
the removed `alt_long_13` and `alt_long_15` in `gas/config/tc-i386.c`. Its removed
assembler test expectations also contain the exact13-byte sequence as a single
long NOP. The patch reduces the assembler's preferred padding length for
performance. Modeling these exact repeated-prefix encodings assumes
a target supporting those assembler forms, in addition to the existing
`targetProfile` assumptions (64-bit mode, multi-byte NOP, CET/IBT and shadow
stacks disabled). This assumption is explicit, not inferred from successful
decoding or from the Intel recommendation table. Stable ordinary RAM and the
existing canonical-address model remain environmental boundaries.

The cited primary documents establish the architectural interpretation and
the separate assembler precedent. Neither establishes a native experiment or
physical refinement of this model.

## Fetch transport strengthening

`SuccessfulFetchTransportWithin extent source destination` transports only
successful byte fetches at offsets below the supplied extent. The shared
`SuccessfulFetchTransport` now specializes it to15. The former nine-byte
premise is insufficient for NOP15; a regression changes byte14 while preserving
the first9. `restrict` and `legacy_decodeAt_transport_short` retain a nine-byte
bridge for the unchanged legacy decoder. The universal instruction bound is
now `Instruction.length_le_fifteen` in both Sequential and CallReturn; the old
universal `length_le_nine` statement would be false.

Both decoder transport proofs use the strengthened relation. Code's existing
`code_fetch_transport_of_bound` proves it from `CodeAt` and `bytes.length+15≤2^64`.
`CFG.Profile.fetchNoWrap` still requires `maxBytes+15≤2^64`; canonicality, exact
partition spans, runtime CodeAt binding and no-wrap proofs remain in force.
This relation never requires an unsuccessful source fetch to succeed at the
destination: final RET/NOP windows need no following byte. Profiles remain
explicit static admission caps; default64 bytes/32 nodes is unchanged. No
dynamic fuel, rank, packet-node/depth or grading-runtime limit changes occur.

## Scope of validation

`tests/SequentialByteComparePadding.lean` uses literal architectural flag
vectors, independently named register/address encodings, full-context framing,
all required truncation and nonexecute boundaries, prefix/ModRM/SIB mutations,
current data failures, caller-only policy rejection and a real bounded VCG run
combining CMP, NOP15, SETae and RET. The shared arbitrary-state contracts retain
all banks and aliases without distinct-register assumptions. No decoder,
interpreter or checker is mocked or copied.

`tests/CounterPadding13.lean` specifies independent literal NOP13/NOP15 windows,
every NOP13 truncation, missing-byte and execute-denial boundary, ordered
mismatch/fetch failures, malformed and unlisted prefixes, a present but
nonexecutable byte14, inaccessible apparent operands, arbitrary-state framing,
CallReturn lifting, literal emission and exact CFG instruction boundaries.

The frozen GCC46-byte and Clang68-byte symbol windows are tested through
production discovery and checker. Clang uses explicit128 bytes/32 nodes;
default64 still rejects it. Its partition includes one NOP at17 of length15,
and authenticates through the final RET at67. These are **decode/check tests**,
not equality behavior or certificate credit. The manifests and
`objdump --disassemble=c_bytes_equal` were read without executing either ELF.
The source signature is `bool` (`functions.h:40`): the eventual result contract
must be low8 Boolean. In particular Clang's n=0 path uses B001 and preserves
the upper56 bits of RAX; neither low32 nor full64 clearing may be required.

Validation distinguishes scoped source checks, the transitive axiom audit
(allowed only `propext`, `Quot.sound`, `Classical.choice`), intentional
foreign-axiom rejection and fresh stored-object kernel replay. Whole-project,
corpus, CI and native gates are outside this foundation; full-routine proofs
and registration require separate validation. Rejection, unsupported input
and timeout establish no security finding.
