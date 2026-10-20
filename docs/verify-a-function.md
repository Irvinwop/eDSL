# Verify a new function

Start with [the complete doubling example](../EDSL/Examples/Verification/Double.lean).
It proves a five-byte function against unsigned modular doubling and reuses the
production checker, ABI contract and OS caller-resource adapter. It adds no
interpreter, instruction rule, grader task or command driver.

```sh
lake build EDSL.Examples.Verification.Double VerificationTests
```

[The companion checks](../tests/VerifyFunction.lean) construct a useful current
OS-resource world, apply the universal theorem with arbitrary initial registers,
flags and AF choices, exercise full64 wraparound, and reject changed operands.
This is a synthetic raw-code example, not a final-ELF or corpus certificate.
All commands here run from the repository root.

## 1. State the independent contract

Use `EDSL.PureCall.Spec` for a read-only scalar call. Define mathematical inputs,
argument bindings, the input domain, a result relation and useful inputs.
`word64` binds the entire register; `low32` intentionally leaves the upper half
arbitrary. Six SysV integer argument slots are available.

The example's mathematical result is:

```lean
result value output := output.toNat = (2 * value.toNat) % 2^64
```

Keep instructions, desired executions and checker results out of this
specification and its admission conditions. `PureCall.Post` adds actual return,
RSP adjustment, full unchanged RAM/permissions, callee-saved registers and
nonarithmetic flags. Do not copy these frames into each program's contract.

## 2. Supply exact bytes and a checked CFG

The example supplies LEA RAX,[RDI+RDI]; RET:

```lean
def bytes : List Byte := [0x48, 0x8d, 0x04, 0x3f, 0xc3]
def graph : CFG.Graph := vcgen_graph bytes
theorem valid : CFG.Valid bytes graph := CFG.discover_sound (by decide +kernel)
```

`vcgen_graph` normalizes the existing discovery result into finite candidate
data, so clients need no handwritten instruction table or decoder expansion.
It supplies no correctness proof. Kernel-checked production decoding authenticates
it. It cannot replace an instruction with an annotation. Runtime `CodeAt` binds
the same bytes to current executable RAM.

For an external artifact, the existing CLI emits checked raw/ELF CFG obligations:

```sh
lake build edsl-cfg-import
lake exe edsl-cfg-import function.bin artifacts/Imported.lean
# Select a named function in a complete ELF, including a non-entry function:
lake exe edsl-cfg-import --elf-symbol function_name program.elf artifacts/Imported.lean
```

The [named-function importer](named-elf-import.md) proposes all ELF metadata and
generates kernel-checked exact-file/name and CFG bindings. Reuse its
`observedBytes`, `observedGraph` and `valid` with the VCG and call adapters below.
See [CFG import](cfg.md) for raw input and the restricted ELF-entry option.
Importing establishes code structure and artifact identity; the independent
functional theorem and current ownership facts are still required.

## 3. Prove the generated conditions

For finite execution, state `VCGen.wp` with the checked entry, an instruction
budget, `PureCallAllowed initial` and the independent postcondition. Prove it
for every admitted input/state. The example's `generated` theorem is the
program-specific proof.

`vcgen_run graph entry simp [...]` composes production steps, both undefined-AF
choices and checked successor equalities. Supply present argument/stack facts
and discharge the remaining mathematics. `vcgen_next` searches the existing
32-node CFG profile; each proposed index and RIP equality gets a kernel proof.
These tactics generate ordinary proof terms and add no trusted solver.

Finite automation keeps graph references intact and normalizes the selected
instruction at each step. It factors the client simplifier into checked
continuation lemmas; unresolved conditions remain proof goals. The callback
must preserve the local context, as ordinary `simp [...]` does. This avoids
copying the whole graph into every proof step and serialized auxiliary type.

Loops use `VCGen.Cutpoints.wp` and `vcgen_block graph cut simp [...]` with sparse
invariants and a strictly decreasing rank. Invariants, ranks, memory permissions
and mathematical progress remain explicit. The existing byte-scan, first-match
and byte-comparison clients share this automation. A cyclic CFG alone does not
prove termination.

The [full64 popcount guide](popcount.md) adds a scalar-loop example using shared
cardinality mathematics, counter/address rules and scratch/return frames.

## 4. Reuse the call/resource bridge

`pureCall_semantics_of_generated` lifts the WP theorem to every admitted
execution and every-prefix original caller authority. The example's `semantics`
and `resources_survive` are direct applications of this shared bridge.

For sparse scalar loops, use `pureCall_semantics_of_cutpoints` and
`PureCall.ScratchFrame` from the [scalar-call guide](pure-call.md). Supply the
selected artifact's generated annotation proof and entry invariant; the shared
bridge derives total execution and every-prefix current-resource preservation.

`Pre` requires current executable bytes and a valid original return stack.
`ResourcePre` additionally requires current OS code/caller loans, ownership and
lifetimes. Construct useful present inputs independently: the companion checks
reuse `OS.CallResources.Domain` and `nonvacuous_of_resource`. No result or
successful-run premise supplies that admission.

For a scalar raw-code candidate, `PureCall.Candidate.nonvacuous` shares the
present mapping/loan and six-argument construction. Supply the independent
specification, one admitted useful value and the nonempty/4096-byte bounds;
the helper requires no instruction support or successful execution. The
[unsigned-average client](unsigned-average.md) shows this path with an
overflowing full64 pair and separate compiler-specific semantic evidence.

For read-only buffers, use `EDSL.BufferCall` and its VCG adapter. Snapshots,
permitted operand reads and current input loans are additional obligations;
accessible RAM alone is not authority. Writable memory, syscalls and concurrent
operations require the appropriate resource/effect model. The sequential CFG
profile rejects those operations.

## 5. Bind the theorem to a final executable

Use [`PureCall.ELFCertificate`](elf-certificates.md) for a standalone scalar
specification. [`DoubleELF`](../EDSL/Examples/Verification/DoubleELF.lean) is a
complete example with a named function distinct from the ELF entry point.
Its byte theorem reuses the same Double proof from the earlier steps.

Use the named import's `observedInput` and `inputChecked`, or supply
`ELF.FunctionInput` metadata witnesses and exact selected bytes yourself. Pass
the complete file and requested byte name separately. The production
[named-symbol checker](elf-function-symbol.md) authenticates the supplied data.
A host parser can propose witnesses; the kernel-checked acceptance proof
establishes their binding. Then use the shared constructor:

```lean
def certificate : PureCall.ELFCertificate spec file name :=
  PureCall.ELFCertificate.ofCaller spec input checked semantics
    caller fresh callerFacts separate value domain useful
```

The inputs describe present caller mappings, a fresh image installation,
code/stack separation and a useful mathematical input. The constructor proves
useful admission at this file's actual selected address. Its universal resource
theorem applies to every admitted loaded call, including other inputs,
registers, flags and AF choices. File, name and specification remain explicit
type indices. Current text/execute permissions and OS loans remain required.

This API consumes checked witness data and a semantic theorem. The importer
automates witness extraction and artifact checks; the semantic proof and useful
present resource witness remain client obligations.

For a **registered contract**, reuse `Corpus.Scalar.certificate` or the buffer
certificate constructor. `Corpus.Certificate` is indexed by the fixed
`Grading.TaskID`; the scalar route requires proof that the supplied specification
equals that registered contract. See [certificate composition](corpus-certificates.md)
and [the registered scalar constructor](corpus-scalar-certificates.md).
Standalone certificates add no grading registration or frozen-corpus credit.
Both routes share the existing ELF and current-resource providers.

## 6. Validate and state the scope

Build your client with warnings as errors, audit its transitive theorem
dependencies and replay the accepted proof closure in a fresh kernel. Use
[the validation guide](validation.md) for repository-wide checks. Add tests for
independent behavior, wrong bytes or lost authority where they can catch a
plausible defect; assigned-field assertions add no evidence.

The sequential profile assumes stable ordinary RAM, absent asynchronous or
concurrent interference, supported canonical addresses and CET disabled.
Current logical OS ownership does not authenticate a native thread or kernel.
State those boundaries in the theorem/report. Failed discovery, proof search,
timeouts and unsupported instructions produce no certificate or defect claim.
Source/IR preservation, native Linux behavior and physical CPU refinement are
separate obligations.
