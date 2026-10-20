# Address-space contracts and binary composition

The first OS implementation module is `EDSL.OS.AddressSpace`, a sequential
abstract address-space contract in Lean 4. It supplies the mapping/permission
vocabulary used by the machine model. It does not establish correctness of a
Linux kernel or syscall implementation.

The separate [ownership registry](ownership.md) layers allocation identities,
principal/epoch authority and revocation over this same space, with a checked
owned-store/binary bridge. Those logical resources are not encoded in `Cell`
permissions or raw hardware addresses.

## State and checked operations

A `Space` maps 64-bit addresses to optional `Cell` values. A cell has a stored
byte and read/write/execute permissions. Stored contents and accessible bytes
are distinct: removing read permission hides a byte without erasing it. The
`toMemory` projection exposes only readable bytes and their supported write and
execute permissions to `EDSL.X86`.

A `Region` is a nonempty natural half-open interval. Validation excludes 64-bit
wrap and the gap between the two canonical address halves in the pinned x86
profile. These are byte intervals; page alignment and Linux userspace-address
limits are not imposed here.

| Operation | Successful result | Explicit rejection |
| --- | --- | --- |
| `map` | Fresh zero-filled cells, preserving all existing mappings | Invalid range, unsupported permissions, any mapped-byte overlap |
| `protect` | New permissions with identical stored bytes | Invalid range, unsupported permissions, any unmapped-byte hole |
| `unmap` | Cells removed from the whole region | Invalid range, any unmapped-byte hole |
| `writeByte` | One writable byte changed with other cells preserved | Noncanonical address, unmapped cell or denied write |
| `storeWord` | Four-byte store after complete operand preflight, preserving cell permissions | Denied, unmapped, wrapping or noncanonical operand |

The current machine interface needs readable bytes for both instruction fetch
and stores. Write-only and execute-only permission requests are explicitly
unsupported. Inaccessible mappings are supported and can later regain access.

Functions named `*Unchecked` are pure internal updates; they do not prove their
preconditions. `map_ok`, `protect_ok` and `unmap_ok` extract validation evidence
from successful checked operations. `contains_mem_addresses` proves that finite
range checks cover every semantic interval byte, including the final byte.
There is no backing-resource budget or allocation-failure branch yet.

## Proved properties

- `map_preserves_existing` rules out replacement of an existing mapped cell
  by a successful fresh mapping.
- `protect_preserves_contents` preserves all stored bytes through protection
  changes, including hidden contents.
- `map_frame`, `protect_frame` and `unmap_frame` preserve cells outside the region.
- `protect_denies_store` proves a machine four-byte store fails after write
  permission is removed at its first byte.
- `unmap_denies_read`, `unmap_denies_fetch` and `unmap_denies_store` establish
  machine-visible access revocation.
- `toMemory_agrees_at`, `agrees_read` and `agrees_code` carry cell framing to
  byte reads, return-stack reads and executable-code binding.
- `load32_after_protect` combines a **successful checked** protection operation
  with the exact-byte load proof. If the changed region avoids the function's
  code, data and return stack, the function retains its result, two-instruction
  termination and unique completed result/count.
- `writeWord_projects` equates a natural-address OS cell update to the machine's
  modular-address four-byte store for every admitted state and value.
- `storeWord_sound` connects checked success, machine store, exact readback,
  mappedness/permission preservation and outside-footprint framing.
- `store32_updates_space` proves that actual store/RET bytes return with the OS
  cell update projected into the final machine state, including termination and
  unique state/count. The proof retains the code and return-stack premises.

`tests/AddressSpace.lean` exercises a checked map/write/protect/hide/restore/
unmap/remap lifecycle, checking retained data, zeroing on remap and neighboring
mapping preservation. It also checks overlap, fourth-byte holes, wrapping and
canonical-boundary rejection. `tests/OSComposition.lean` instantiates the generic
composition theorem with concrete admitted inputs and exact compiler bytes,
checks the caller-visible result, and confirms that revoking the actual data
region makes the modeled load fail. The transitive axiom audit covers both
modules and their regression declarations.

`tests/WordStore.lean` supplies admitted entries for every old 32-bit value and
every 64-bit store argument, and exercises store/hide/restore/read behavior with
neighboring guard cells. It checks fourth-byte permission denial, hidden/unmapped
cells, wrapped operands and truncation of high source-register bits. `storeWord`
shares the machine operand preflight; its OS update uses natural addresses and
byte slices, while the machine uses modular offsets. The projection theorem
proves these representations agree. Failure returns no updated state; it does
not model hardware exception delivery or concurrent visibility.

## Linux conformance observations and remaining work

The owned C fixture `fixtures/vm-contract.c` separately probes Linux anonymous
zero filling, read-only write denial, inaccessible reads, retained contents
after restoring access, unmapping, and neighboring-page preservation. Deliberate
invalid accesses run in child processes; the parent checks `SIGSEGV`, with core
dumps disabled. The compiler integration script and CI run this fixture.
These are observations of selected behavior, not a proof of Linux conformance.

Linux operations are page granular and have additional failure cases, flags,
address-selection rules and interactions. In particular, Linux `munmap` permits
holes, while this abstract operation requires full mappedness. A future Linux
adapter must normalize page ranges and relate Linux outcomes to the contract;
it must not silently identify the two APIs. See the primary
[mmap/munmap documentation](https://man7.org/linux/man-pages/man2/mmap.2.html)
and [mprotect documentation](https://man7.org/linux/man-pages/man2/mprotect.2.html).

Next obligations are page-based syscall semantics and errors, resource identity
and exhaustion, loading/ABI proofs, and threads/atomics with an explicit memory model. Aliasing,
physical pages, protection keys, TLB revocation, signals and kernel-byte
refinement remain outside the present contract. All current updates are
sequential; functional state updates alone make no concurrent atomicity claim.
