# Proving concrete OS implementations

eDieSeL aims to verify concrete kernel and runtime components and compose their
contracts into program and security-property proofs. This track is **planned**.
A privileged kernel execution model and concrete kernel component proofs
require additional implementation.

Current [counter workers](counter-workers.md), [mutex workers](mutex-workers.md)
and [futex clients](futex.md) prove scoped userspace behavior under abstract OS,
resource and scheduling contracts. They do not prove native thread creation,
publication, context switching, syscall handling or cleanup. Concrete OS proofs
must establish those same contracts before replacing them in client theorems.

## Ingest the real build

Identify the selected source revision, configuration and complete deployed
build: architecture, compiler/backend, flags, generated headers/bindings,
conditional features, dependencies, startup assembly, runtime libraries,
modules, firmware and device assumptions. Retain exact final image identity;
source/IR mappings are untrusted assistance until justified.

Compile each component through its recorded build path, preserving assembly,
intrinsics and external effects. A different build that happens to emit useful
IR cannot substitute for the deployed binary. Verify final bytes after linking
and any admitted runtime patching. Imported source/artifacts retain upstream
licenses; the project's tooling license does not relicense a kernel.

## The new architecture profile

The current userspace ISA cannot model kernel execution. Add the facilities
required by the selected component, with explicit unsupported behavior:

- Privilege levels, protected state, control registers and privileged operations.
- Page-table walks, permissions, translation caches and invalidation.
- Exceptions, interrupts, entry/return frames, masking and preemption.
- Per-CPU state, multiple cores, context switching, kernel stacks and callbacks.
- Atomic operations and the applicable kernel memory-order rules.
- MMIO, DMA, IOMMU, device transitions and interrupts.
- Boot/initialization invariants, resource exhaustion and failure paths.

Pin the selected [Intel system-architecture specification](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)
and target profile. Physical hardware conformance remains an environmental
assumption unless separately justified. For relevant Linux synchronization,
relate the [Linux Kernel Memory Model](https://docs.kernel.org/dev-tools/lkmm/index.html)
to concrete execution; userspace C/C++ orders are a separate model.

A component executes against privileged hardware and device semantics. It
cannot assume that the very OS service it is meant to verify already works.
Temporary contracts for other components need a sound composition or global
invariant argument to discharge cycles.

## Discharge contracts component by component

Start with a bounded helper, allocator fragment, syscall path or synchronization
primitive. Define an independent functional/resource contract, allowed callers,
failure outcomes and interference, plus a relation between current machine
state and abstract OS state. Prove actual final-code execution meets that
contract for every admitted behavior. Loops, callbacks, interrupts and
concurrency require explicit invariants and compositional rules.

Replacing a client assumption requires all of the following:

1. Exact implementation bytes and reachable dependencies are covered.
2. The implementation meets the client's existing contract, including effects,
   errors, resource lifetimes and progress qualifications.
3. Boot/callers establish entry and global invariants; every admitted peer,
   interrupt handler and device transition preserves them.
4. Client and implementation compose under the same ABI, memory model,
   resource identities and environmental assumptions.

An exclusive-memory, interrupt-free helper proof does not establish its use in
a preemptible shared kernel. An environment invariant is itself an obligation;
assuming it after arbitrary peer steps would hide the required preservation.
A coverage ledger must identify remaining components and contracts before any
whole-kernel claim.

## Security properties and evidence

Memory/resource safety, isolation, authorization and information flow need
independent properties and explicit observations or attacker capabilities.
Functional correctness alone does not imply every security property. Current
conditional resource models provide useful access, lifetime and framing
contracts; they establish no native kernel enforcement or general
noninterference result. Timing/speculation and device effects require additional
models if included in a claim.

Results should distinguish a theorem, a checked property violation and an
unsupported/unknown analysis. A violation requires a feasible initial state,
justified contract and supported execution. Proof failure or timeout does not
establish a defect. Keep real findings, metadata and reproducers private and
out of CI logs/artifacts; see [findings](findings.md).

## Staged deliverables

1. A reproducible build manifest and exact final-image ingestion.
2. A pure concrete helper through the existing function-byte route.
3. Owned memory and explicit caller/interference contracts for one component.
4. The privileged/interrupt/translation slice needed by that component.
5. A syscall or synchronization implementation proof, composed with a client
   theorem to remove its previous external assumption.
6. Wider boot, scheduling, module and device coverage, with remaining contracts
   visible and security claims separately scoped.

The [roadmap](roadmap.md) records dependencies; [trust](trust.md) explains the
remaining model and physical boundary. A component proof reduces trust only
when it discharges a specific contract used by the larger result.
