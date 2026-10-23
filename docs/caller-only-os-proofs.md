# Reusing sequential proofs in the OS model

`EDSL.OS.TSO64.EffectSimulation.Resumable.CallerOnly` connects existing generated
sequential verification conditions to the resumable OS proof rules. A client
reuses its mathematical specification and body proof. The shared adapter supplies
current instruction decoding, resource and caller-read checks, queue effects,
and the connection to actual scheduler steps.

The adapter covers the [caller-only instruction subset](caller-only-transport.md):
register and control operations, padding, and RET through the original caller
slot. Ordinary DATA loads, stores, syscalls, subject atomic operations and the
excluded independent vector flag profiles require other adapters.

## What a client supplies

- The actual byte window, structurally checked graph and native dispatch
  admission. `CallerOnlyGraph` retains the instruction classification, original
  code-window checks and existing 64-byte native transport bound.
- Present OS admission: a live worker, valid resources, protected code and
  original caller word. Invocation argument bindings, input domain and return
  canonicality remain part of the program's independent entry contract.
- An existing `VCGen.wp` or `VCGen.Cutpoints.wp` proof, using the original
  production executor, choices and fuel. Its read contract must imply the
  original caller STACK8 contract.
- A projection from that proof's result evidence to the desired returned
  context. Mathematical results, registers, flags, return address and ABI
  observations can be projected without asserting equality of current RAM.

`Admission.reference_code` and `Admission.reference_caller` allow the reference
memory to be exactly the initial worker's actual local view. A valid incoming
FIFO may be nonempty; no earlier issue history is invented.

For later states, `Binding.pause_reference` retains the complete private context
used by the sequential proof while permitting current memory and pending queues
to change. The reference memory records the sequential proof's assertions. It
does not replace the RAM used by real scheduler execution.

## Shared proof rules

`rwp_of_callerOnly_cutpointWP` lifts a generated cutpoint block into
`Resumable.rwp`. At every instruction boundary, passive actions may occur before
the worker resumes. The rule reconstructs current code, original caller authority
and the actual production observation, then authenticates its CFG successor.
It takes no successful future OS issue or desired successor as an input.

`callerOnlyAnnotations` adapts sparse sequential annotations to the existing
resumable restart and historical-response interface. Clients supply cutpoint
invariants rather than instruction-local OS proofs.

`rwp_of_callerOnly_wp` handles bounded bodies whose graph has no edges into
cutpoints. It consumes the existing `VCGen.wp` and its `Result` evidence; the
original fuel and both Bool choices are retained. Its exit assertion is false,
so a completed block returns instead of exposing a cutpoint continuation.

The descriptor must use `authorityCallerPolicy`. This policy checks current OS
resource validity, caller-read identity and the admitted instruction effect.
Arbitrary policies with additional memory-sensitive assertions need their own
stability proof.

## Returns and interference

`returnedContext` concerns the actual installed worker at its return tick,
including its original resources and complete returned context. The surrounding
`Residual`, `Response` and `Done` interfaces preserve authentic history and the
historical return witness. A later peer publication need not preserve a
memory-sensitive postcondition in the current world.

The permitted pauses are those in the existing TSO64 model: peer issues and
publication drains, including the subject's own drains. Original code and caller
loans stay protected. Allocation, revocation, unmapping, external device writes
and arbitrary OS activity are outside this action set.

The source cutpoint WP retains its rank checks on reference states. This adapter
establishes partial correctness and current own-step enabledness. It supplies no
scheduler fairness, starvation freedom, global termination or minimum-operation
claim. Instruction counts in input sequential evidence are not counts of
unfiltered scheduler positions.

The inherited long-mode, CET-disabled, ordinary coherent RAM, translation,
nonaliasing, authority and lifetime assumptions remain explicit. These proofs do
not establish physical CPU/Linux correspondence or compiler preservation. See
[resumable blocks](effect-scheduler-bridge.md) and [validation](validation.md) for the
underlying interfaces and checking commands.

## Worked corpus adapters

`EDSL.Corpus.V1.CallerOnlyAdapters` demonstrates both default GCC and Clang
windows for `absSigned32` and `rotateLeft64`. Each program adapter applies the
shared `CallSite.lift_generated` rule to its existing graph, original fuel and
exported `generated_vc`; it contains no instruction-execution proof cases.
Finite kernel decisions establish the instruction/native/graph obligations.

`CallSite` selects the protected code extent and original worker. `CallInputs`
records present argument, domain, entry, original-RSP and canonicality conditions;
code and caller-read success come from OS `Admission`. The concrete site types
use the exact frozen ELF symbol addresses, and each adapter retains the
production file/name/window check. Loading or relocating a native process is a
separate obligation.

`absSigned32` and `rotateLeft64` return generated resumable blocks.
`AbsResult` and `RotationResult` retain a complete reference result witness whose
entire context equals the actual returned context. `absSigned32_context` and
`rotateLeft64_context` extract their independent mathematical results, original
caller RIP/RSP, callee-saved registers and flag contracts. The reference result's
memory equality concerns reference RAM only.

A new bounded caller-only program can use `CallSite.lift_generated` with its own
independent specification and generated body proof. OS instruction gates and
passive closure stay in the shared library. Loops use the cutpoint-annotation
interface instead. These examples reuse previously certified corpus bodies and
add no new end-to-end corpus coverage.
