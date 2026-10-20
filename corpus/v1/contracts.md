# Common v1 contract obligations

These obligations apply to every row in `specifications.tsv`. They are proof
targets and assumptions to make explicit in a later machine contract, not
established theorems.

The callable ABI is SysV x86-64 on Linux: a valid aligned private stack, live
readable return continuation, preservation of callee-saved registers, and a
separately authorized private stack/scratch region. Memory frames describe
caller-owned observable bytes after return and exclude that authorized scratch;
they do not prohibit stack spills. The loaded code, external-call targets and
all required instruction/data permissions must match the final ELF environment.
No source semantics or ELF extraction result implies those machine facts.

Pointer-bearing rows require live typed allocations and valid source pointer
provenance, alignment, and nonwrapping byte extents including element-size
multiplication. For n=0, bounded array/string operations perform no object
access and permit null or valid one-past pointers; `strlen` and the nonempty
maximum have their stronger row-specific preconditions. Overlap is permitted
for read-only inputs and explicitly forbidden for copy destinations. Writable
arrays and destination structs require exclusive write authority; read-only
inputs must remain stable for the relevant execution. A machine proof must
justify any compiler-generated widened reads, SIMD operations, scratch accesses,
external libc calls, errno/TLS use, and OS resource lifetime.

Concurrent atomic cells remain live and correctly aligned through every thread
completion and join. Access authority may be shared only through the modeled
atomic protocol. Acquire/release synchronization is conditional on the required
reads-from and release-sequence relations; reading an initial or relaxed value
need not synchronize with any release. Linearizability, progress/fairness,
source-to-machine memory-order preservation, and x86-TSO correspondence are
separate proof obligations. A correct uninterrupted result or a finite native
stress observation establishes none of them by itself.
