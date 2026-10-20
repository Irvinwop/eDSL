# Scalar scratch frames

Import `EDSL.X86.VCGen.ScratchFrame`, the `EDSL.X86.VCGen` facade, or `EDSL`. `PureCall.ScratchFrame scratch
initial current` preserves the **entire** `Memory` value (read, executable and
writable functions), every GPR outside `scratch`, and all bits outside the six
arithmetic flags. RIP is unconstrained. A frame describes present states; it
does not grant a read or establish an execution.

The small compositional API in `EDSL.PureCall.Frame` provides:

- `frame.weaken subset`: an explicit proof `scratch ⊆ wider` permits widening.
- `frame.writeRegister destination value member`: requires `destination ∈ scratch`.
- `frame.withRip rip`: changes only RIP.
- `frame.withFlags flags preserved`: requires full nonarithmetic-mask equality.
- `frame.of_fields next registers memory flags`: transports across proved field
  equalities; arbitrary RAM and both permission functions remain protected.

For concrete production-generated states, use:

```lean
vcgen_factor => vcgen_scratch_frame framed
```

The tactic reduces projections and reconstructs nested register `if` updates
as applications of `writeRegister`. It proves membership by assumptions or
kernel reduction of concrete scratch definitions, without enumerating all 16
registers. Register values remain opaque. Memory uses reduction and the
supplied frame's equality. Flags use that frame and existing full-mask
preservation theorems for status/logical, SHR-one, comparison, addition and
increment/decrement flags. No instruction semantics are duplicated.

For an additional proved flag operation, replace the flag proof explicitly:

```lean
vcgen_scratch_frame framed with
  simp only [Result.prepend, State.writeRegister, myFlags_preserves]
```

The tactic must close the entire frame. A missing destination membership,
unknown register-function form, changed memory/permissions or unproved flag
mask equality fails with an error/remaining obligation. Symbolic function
updates beyond nested register equality tests need a manual compositional
proof. Scratch and initial state must match definitionally; the tactic never
infers a larger scratch set.

RET needs an explicit widening, for example:

```lean
vcgen_scratch_frame
  (framed.weaken (List.subset_cons_self Register.rsp scratch))
```

`ScratchFrame.post_return` still requires a separate proof that scratch
excludes ABI callee-saved registers, as well as the mathematical result and
actual RIP/RSP equations. VCG clients still supply read authority, invariants,
ranks and termination arguments; the existing scalar bridge supplies current
OS-resource framing from the generated proof.

`tests/VCGenScratchFrame.lean` checks a complete SHR/ADD call against unsigned
division/modular addition and a positive MOV/TEST/LOOP countdown using a sparse
invariant. Both quantify arbitrary initial registers/flags, original memory
maps and AF streams, and connect generated VCs to actual fetched execution.
An owned MOV-to-RBX/RET negative proves that a changed protected register
cannot satisfy the promised frame. These are synthetic semantic regressions;
they add no corpus, native CPU/OS, compiler or cost coverage.

For the complete SHR/ADD example, the corresponding manual frame proof is
eight nonblank lines; the replacement is the single `vcgen_factor` line above.
Both retain the same explicit scratch widening and mathematical obligations.

The generated GCC and Clang rotation proofs use the custom flag hook with
`Sequential.rolFlags64_preserves`. Their independent bit-origin result,
masked-zero flag preservation, defined one-bit OF, larger-count OF choices,
caller return and current-resource obligations remain separate from the frame.
`tests/RotationBodies.lean` exercises those proofs on the exact frozen symbols.

Recognition is conservative: even a reversed equality guard may fail the final
definitional reconstruction. Use the compositional API for other extensionally
equal register functions.
