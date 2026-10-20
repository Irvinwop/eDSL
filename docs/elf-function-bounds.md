# Explicit bounds for named ELF functions

Named ELF import has a caller-selected byte-bound path. Existing entry points
retain their 64-byte limit; CFG defaults remain 64 bytes and 32 nodes. A symbol's
size never chooses a profile automatically.

The low-level ELF API takes `maxBytes : Nat`, avoiding a dependency on CFG:

- `FunctionWindow.Window.BoundsWith`, `FunctionWindow.checkWith` and
  `FunctionWindow.admitWith` check the complete selected interval.
- `FunctionSymbol.checkWith` and `FunctionSymbol.admitWith` additionally
  authenticate the requested unique byte name and its entire declared extent.
- `FunctionInput.checkWith` and `FunctionInput.admitWith` carry the same bound
  through an untrusted named-function input.
- `CallerResources.admittedWith`, `stack_cellsWith`, `stack_agreesWith` and
  `initial_factsWith` transport the same explicit bound through fresh installation
  and the ordinary current caller-resource domain. `Corpus.ELFResources` forwards
  these neutral proofs; their existing names retain the default signatures.
- `FunctionCandidate.extractWith` proposes metadata and bytes, then checks them
  against the complete external file and requested name under the supplied cap.
- `FunctionCandidate.checked_bindingWith` and `checked_codeWith` expose the
  typed binding and exact executable `CodeAt` consequences. `Binding` and
  `FunctionWindow.Selection` have a trailing byte-bound parameter defaulting to
  64. Generalized window and symbol soundness, admission, selected-segment and
  current-code theorems have a `With` suffix; existing theorem names specialize
  those proofs to the default.

For example, `input.checkWith 96 file name` explicitly permits a named extent of
up to 96 bytes. This does not truncate a longer function, infer missing sizes,
select a prefix ending at RET, or authorize a different file or name. The existing
whole-file and ELF metadata bounds still apply.

`FunctionCandidate.sourceWithProfile profile namespace file name input graph`
emits a literal `observedProfile : CFG.Profile`. Its named-input checker uses
`observedProfile.maxBytes`, its binding records that bound, and its CFG proof uses
`CFG.checkWith` and `CFG.Valid` with the same profile. The generated loaded-code
proof uses the corresponding generalized ELF theorem. `source` specializes this
emitter to `CFG.defaultProfile`. Emission supplies source, not proof acceptance:
Lean must check the emitted file and all independent functional and resource
obligations. Invalid namespace components still reject before rendering.

All paths retain literal full-file metadata authentication, exact source bytes,
PROGBITS/symbol/LOAD address and file-offset agreement, full file-backed execute
coverage, low canonical nonwrapping addresses, disjoint rounded LOAD pages and
freshness on admission. An early RET does not hide the remainder of a named
extent. Current-memory code use still requires an explicit text and execute
permission preservation premise. A larger static cap changes none of these
contracts.

BUFFER resources and certificates also carry an explicit bound.
`Corpus.BufferResources.admittedWith`, `installed_cellWith` and
`programSpace_eqWith` use the same checker evidence. The indexed `programSpace`
remains equal to the complete installed space, including every cell and permission
outside the selected function; it is not a selected-function-only image.
`Corpus.Buffer.LoadedCall` and `Corpus.Buffer.Certificate` have a trailing
`maxBytes : Nat := 64` parameter. Admission, named checking, binding and the
loaded-call witness share that parameter. `Certificate.ofLoadedCallWith` packages
an independently proved registered BUFFER semantic claim and actual useful current
resources; `ofLoadedCall` retains its original default signature. Current code,
full-image retention, original caller authority, return guarantees and read
authority at every execution prefix are unchanged. No byte bound supplies a
semantic claim or substitutes readable RAM for a live ownership loan.

The standalone regression module `tests/ELFFunctionBounds.lean` independently
encodes a real ELF64LE file whose named 68-byte extent contains an early RET,
short NOP padding and a final RET. Default import rejects it; an explicit 68-byte
cap accepts it. Controls cover suffix mutations beyond byte 64, partial extents,
wrong name/address/offset, mismatched extent, canonicality/wrapping, missing
execute/read permission, insufficient LOAD coverage, truncated metadata and
malformed rows. A complete CFG also requires enough explicit nodes; enlarging
only the byte cap preserves node-cap rejection. Concrete modeled executions
check the independent return-value/continuation contract and reject a missing
return-stack read. The existing `VCGen.certifyWith` API accepts that concrete
independent contract with caller read authority, rejects the wrong return value,
and rejects a denied read policy even when the stack remains readable. These
checks establish no source-compiler or native-CPU correspondence.

`tests/ELFCallerBounds.lean` reuses that real 68-byte function with a longer RX
BSS tail. It constructs an actual useful BUFFER loaded call through the generic
caller domain and compatible code/input loans. Checks cover the last selected
byte, complete-space retention outside the function, denied adjacent readable RAM,
the original stack address, real loan revocation and rounded-page admission
collision. Its certificate adapter requires an explicit registered semantic claim;
it supplies no such claim for the constant-result fixture.

Scalar corpus certificates remain at the default 64-byte bound. These APIs do
not extend task identities, registries or concrete program bodies.
`VerificationTests` builds both standalone regression modules; the full-project
gate imports them for audit and fresh replay. Existing installed proof-packet,
kernel, decoder and runtime
budgets remain unchanged. A larger model profile is not authority to increase
those budgets or a claim that a larger client packet is accepted. No new opcode,
backend, frozen-corpus acceptance or native proof is established by this API.
