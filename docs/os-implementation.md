# Proving concrete OS implementations

Status: planned extension of the binary-first verifier. No OS source importer,
kernel model, component proof, vulnerability scanner or reporting service is
implemented yet.

## Ingest the real build

The input is a pinned OS source tree plus its complete selected build, not an
isolated source filename. Record configuration, architecture, compiler/backend,
flags, generated headers/bindings, conditional features, dependencies, startup
assembly, native libraries, linked modules, firmware/device assumptions and
the exact deployed image. Preserve source/IR-to-binary mappings as untrusted
assistance and reproducibility data.

Imported OS source and build artifacts retain their upstream licenses and
attribution. The project's Apache-2.0 license covers project-owned tooling;
ingestion does not relicense a third-party kernel.

Compile implementation languages through their real build path. Rust-generated
LLVM IR or assembly can feed the same analysis as C-generated artifacts.
Some components already contain assembly or compiler intrinsics; preserve their
semantics and effects. Check final code bytes after linking and permitted
runtime patching. A GCC-built kernel may require a separate build to produce
LLVM IR; that different build must not be substituted for the deployed image.

The [kernel Rust documentation](https://docs.kernel.org/rust/index.html) describes
its build integration, and [rustc](https://doc.rust-lang.org/rustc/command-line-arguments.html)
documents output kinds. Neither makes translation into IR a proof of the
source, IR, binary, or kernel behavior.

## The new architecture profile

Userspace machine semantics are insufficient for kernel execution. Extend the
selected ISA profile with the facilities a component actually uses:

- Privilege levels, protected state, control registers and privileged operations.
- Page-table walks, access permissions, translation caches and invalidation.
- Exceptions, interrupts, entry/return frames, interrupt masking and preemption.
- Per-CPU state, multiple cores, atomic operations and kernel memory ordering.
- Device registers, MMIO, DMA, IOMMU, external device transitions and interrupts.
- Boot/initialization invariants, context switching, kernel stacks and callbacks.
- Faults, resource exhaustion and permitted concurrent callers/interrupt handlers.

The [Intel system-architecture manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)
are a specification source for x86 facilities. Pin the chosen revision/profile.
Hardware conformance remains a physical-world assumption unless separately
justified. Use the [Linux Kernel Memory Model](https://docs.kernel.org/dev-tools/lkmm/index.html)
when reviewing relevant Linux kernel primitives; it is distinct from userspace
C/C++ memory rules and needs a justified link to concrete machine execution.

Kernel code executes against privileged hardware and device semantics, not an
assumption that the OS service being proved already works. Other components
may have explicit temporary contracts. Discharge cyclic dependencies through a
sound composition/global-invariant argument, not mutually assumed correctness.

## Discharge contracts component by component

Start with a useful bounded kernel/runtime helper, allocator fragment, syscall
path or synchronization primitive. Give it an independent functional/resource
contract, allowed callers and interference, and an invariant relating machine
state to abstract OS state. Prove its actual machine-code implementation meets
that contract for every admitted execution. Loops need invariants; recursion,
callbacks, interrupts and concurrency need appropriate compositional rules.

To replace an OS assumption in an application theorem, prove:

1. The exact implementation bytes and their dependencies are covered.
2. The implementation establishes the same contract the application uses,
   including effects, error outcomes, lifetimes and progress qualifications.
3. Its entry and global invariants are established by boot/callers and preserved
   by every admitted peer, interrupt handler and device interaction.
4. The kernel/runtime implementation and application execution compose under
   the same ABI, memory model, resource identities and environment assumptions.

A proof about a helper with no interrupts and exclusive memory does not verify
its use in a preemptible shared kernel context. A supplied invariant is a proof
obligation; assuming it holds after every arbitrary environment step would
hide the hard part. Make remaining components/contracts visible in a coverage
ledger and never promote partial coverage to a whole-kernel claim.

## Staged deliverables

1. Build manifest and final-image ingestion, with exact artifact identity.
2. A pure concrete helper proved through the existing function-byte route.
3. Owned memory and an explicit caller/interference contract for one component.
4. A privileged-instruction/interrupt/page-table slice required by that component.
5. A syscall or synchronization implementation proof and application-level
   composition that removes its previous external contract assumption.
6. Wider component coverage, module initialization, devices, scheduling and boot
   invariants, each with explicit remaining assumptions.

Verification results include a theorem, a checked violation, or an honest
unsupported/unknown result. Send candidate defects to the private
[findings workflow](findings.md); an unfinished proof does not convict the code.
