# Roadmap

Only the repository bootstrap is complete. Milestones below describe planned
work and completion criteria, without dates or API stability promises.

## 0. Repository foundation

- [x] Public project scope covering all four language domains and the OS domain.
- [x] Architecture proposal and OS semantics map.
- [x] Build checks for exact GNU C23 and GNU C++26 modes.
- [x] CI configuration for those build checks.

## 1. Contracts, embedding, and the first OS slice

- [ ] Decide the C/C++ embedding boundary and document host vs generated execution.
- [ ] Define the smallest typed program representation with source diagnostics,
      values, functions, resources, and effects.
- [ ] Specify allocation/lifetime, thread start/join, and atomic increment/load.
- [ ] Implement GNU C23 generation and a native Linux adapter in C/assembly.
- [ ] Compile and run the shared-counter workload, including cleanup after
      partial failure.

Exit criterion: a builder-generated program uses real OS threads and shared
memory with independently specified results and lifecycle checks.

## 2. GNU C++26 and cross-language composition

- [ ] Add the C++ language domain and GNU C++26 generation.
- [ ] Define C/C++ linkage, layout, ownership, and error propagation boundaries.
- [ ] Implement the chosen C-hosted construction interface.
- [ ] Run the same OS workload through both language paths.

Exit criterion: both generated language paths satisfy the same OS contract,
with feature checks for the constructs actually used.

## 3. LLVM IR

- [ ] Pin a supported LLVM version and target data layout.
- [ ] Lower the shared core and OS ABI calls to verified LLVM IR.
- [ ] Define atomic ordering and synchronization-scope mappings.
- [ ] Add LLVM verifier checks and executable comparisons with the source paths.

Exit criterion: verified IR executes the OS slice without weakening its contract.

## 4. Assembly

- [ ] Define a typed x86-64 instruction/operand model and ABI boundaries.
- [ ] Represent registers, constraints, clobbers, memory effects, and fences.
- [ ] Support assembly composition and object generation using a native assembler.
- [ ] Validate calling conventions and atomic mappings independently.

Exit criterion: the assembly path preserves the same workload contract and
interoperates with the native runtime.

## 5. Synchronization and memory depth

- [ ] Mutexes, condition variables, semaphores, barriers, and explicit wait/wake.
- [ ] Publication, compare/exchange, ordering, and lock-free capability checks.
- [ ] Arenas, mapped/shared memory, page permissions, and resource diagnostics.
- [ ] Scheduling, affinity, topology, deadlines, interruption, and cancellation.

Exit criterion: each operation has a documented native mapping and meaningful
integration coverage; concurrency claims also have appropriate model evidence.

## 6. Program-wide OS coverage and more targets

- [ ] Processes, signals, IPC, filesystem, networking, and async I/O.
- [ ] Environment, permissions, resource limits, dynamic libraries, and devices
      as required by concrete programs.
- [ ] Additional CPU and OS adapters with explicit capability matrices.
- [ ] Compare generated performance and code size against equivalent native
      C/C++/assembly workloads before making performance claims.

Every milestone includes error reporting, target capability checks, and
documentation. Broad coverage must not replace precise per-operation semantics.
