# Allocation identities, transfer and revocation

`EDSL.OS.Ownership` adds a sequential resource registry over the existing
address-space model. It tracks which principal currently controls a region,
distinguishes lifetimes at reused addresses and connects an authorized word
store to the checked `89 37 c3` machine-code profile. The implementation,
operations and proofs are in Lean 4.

This is a proof-level ownership discipline. Tickets and principal IDs are
copyable, constructible Lean data. They do not authenticate callers or add
generation checks to raw machine pointers. Concurrent enforcement, a linear
permission logic, language-object provenance and Linux allocator correctness
remain separate work.
Principals are semantic identities; this layer does not assign or manage
lifetimes for reused native thread IDs.

## State and invariant

An allocation has an owner (`Nat`), transfer epoch (`Nat`) and nonwrapping
`AddressSpace.Region`. A ticket holds the allocation's registry identifier and
epoch. A `World` contains the underlying `Space`, a monotone `frontier` and a
function from identifiers to optional live allocation records.

`WellFormed world` requires:

- Every live identifier is strictly below the frontier.
- Every live region is nonempty, canonical and nonwrapping according to the
  existing region contract, with every byte mapped, including inaccessible cells.
- Distinct live identifiers have disjoint natural-address intervals.

Unregistered mappings are allowed, so existing code, caller stacks and loader
data need not all be owned by the registry. `empty space` starts a valid empty
registry over any supplied space. `Current world owner ticket` identifies a
live record with matching principal and epoch. `current_unique_owner` proves
that one current ticket cannot name two different owners in the same world.

Identifiers and epochs use unbounded naturals. The frontier increases on every
successful registration and never decreases on release. Every transfer advances
the epoch, including transfer to the same owner. There is no finite-handle wrap
or identifier recycling hidden in these operations.

## Checked operations

| API | Success | Rejection |
| --- | --- | --- |
| `allocate` | Fresh zero-filled abstract mapping at a supplied region; fresh identifier/epoch0 | Occupied frontier ID or any underlying mapping failure |
| `adopt` | Register an existing mapped, valid, unclaimed region; exact space unchanged | Occupied frontier ID, invalid range, any hole or overlap with a live region |
| `transfer` | Same region and bytes, new owner and incremented epoch, replacement ticket | Missing ID, stale epoch or wrong owner |
| `release` | Unmap the whole allocation and remove its record; frontier retained | Authorization or underlying unmap failure |
| `protect` | Change permissions of the whole allocation while retaining identity/epoch and contents | Authorization or underlying protection failure |
| `storeWord` | Update four bytes contained in one authorized allocation using the existing checked OS store | Authorization, cross-allocation operand or machine permission/range failure |

All checked operations return `Except`; failure returns no updated world or new
ticket. These are functional abstract contracts, not Linux transactional or
concurrent-atomicity claims. Mapping failure currently covers the existing
byte-cell contract's range, permission and overlap errors, not physical memory
exhaustion. There is no allocator search policy, partial release or region splitting.

`allocate` must find an unmapped interval, so it never overwrites even an
unregistered existing cell. `allocate_initialized` proves zero initialization,
exact permissions and preservation of every previously mapped cell.
`adopt` preserves bytes and mixed per-byte permissions; it may register cells
that are mapped but unreadable. Store permissions remain an independent check.
For ELF images, adopt exact initialized segment ranges; the modeled loader's
page padding is unmapped and cannot be silently adopted as a full region.

Adoption scans IDs in `[0, frontier)`. Its completeness relies on the explicit
well-formedness premise, which puts every live ID in that range. The preservation
theorems require that premise; arbitrary manually constructed malformed worlds
are not advertised as valid inputs. The operations are not a global runtime
well-formedness checker. `allocate_success` and `adopt_success` provide positive
contracts when their stated resource conditions hold.
The `replace` and `install` helpers are pure constructors; they do not check
the invariant. Use the checked operations or establish their premises explicitly.

## Preservation and lifetime proofs

The `*_wellFormed` theorems cover every checked operation. Allocation/adoption
establish a current ticket; transfer establishes the replacement ticket and
invalidates the previous one for every principal. Protection and stores retain
resource metadata. Protection preserves hidden contents; release and protection
have outside-region cell framing rules. Stores retain all mapping permissions
and preserve every byte outside the authorized region.

`Step` includes precisely successful managed allocate, adopt, transfer, release,
protect and store operations. `History` is their arbitrary finite closure.
`History.wellFormed` proves invariant preservation. `Step.advances` and
`History.advances` establish a monotone frontier and nondecreasing epochs for
old identifiers; an absent old identifier cannot be introduced again.

`Invalidated world ticket` means the identifier is below the frontier and any
live record at it has a newer epoch. A removed record satisfies the latter
condition without being live. `release_invalidates` and `transfer_invalidates`
establish this predicate. `Invalidated.persists` proves it through every later
managed history, and `revoked_for_history` excludes current authority for every
principal. This covers release followed by same-address reallocation, self-
transfer and A→B→A transfer, rather than just the immediately following state.

The history excludes unmanaged address-space changes, unchecked machine stores
and arbitrary environmental interference. Those may invalidate the discipline;
a future concurrent execution model must constrain or account for them. The
registry does not prevent an unchecked stale raw address from accessing a new
mapping. A ticket check is not itself a hardware use-after-free detector.

## Connection to exact machine code

`storeWord` checks natural bounds for all four bytes, then calls the existing
`AddressSpace.storeWord`, which preflights mapping, canonicality and write
permissions. Adjacent allocations cannot jointly authorize one operand, even
when both have the same owner and all hardware bytes are writable.

`storeWord_wellFormed` proves the resulting registry invariant, current authority,
exact machine-store projection, little-endian readback, unchanged permissions
and outside-allocation framing. `owned_store32_correct` composes the successful
authority-checked operation with the machine-byte theorem: the store/RET code
produces exactly the updated OS space, returns in two instructions, has a unique
result/count and excludes ordinary user divergence. Executable-byte binding,
code/return-stack disjointness, readable stack and canonical return target remain
explicit premises. The machine instructions do not inspect the registry.

`tests/Ownership.lean` constructs an adopted caller state and proves this
composition for every old 32-bit word and every 64-bit input register value.
It proves well-formedness of the resulting world too, so the bridge has concrete
admitted states rather than only a conditional theorem with assumed authority.
The general certificate CLI still emits its existing function/machine contracts;
it does not automatically invent or certify a resource registry. Clients import
`EDSL.OS.Ownership` and use these checked contracts in their Lean composition.

## Checks and remaining work

```sh
lake build EDSL
lake env lean -DwarningAsError=true tests/Ownership.lean
bash scripts/check-audit.sh
```

Regressions check old-ticket rejection after same-address reuse and A→B→A,
self-transfer revocation, owner mismatch, a writable cross-allocation operand,
the last contained store's readback and neighboring allocation preservation,
inaccessible-cell adoption and restoration, unsupported permissions, final-byte
overlap, the highest live scan ID and an unmapped tail. Expectations concern
resource use and byte behavior rather than assigned fixture metadata. All cases
are owned synthetic inputs; no new native enforcement is claimed.

The [shared read borrowing wrapper](borrowing.md) now adds guarded loan
creation/completion, whole-allocation freezing and arbitrary-history stability
for surviving loan bytes/permissions. `Ownership.Mutation.run_preserves` provides
the reusable frame rule for unrelated live allocations. Raw Ownership operations
remain usable separately and do not acquire borrowing guards automatically.

Next work includes splitting, mutable borrowing, protected invariants and concurrent
adequacy, stack/heap object lifetimes and provenance, allocation failure/cleanup
protocols, an allocator strategy, aliases/backing identity and real OS/runtime
refinement. Thread startup/transfer and join must connect principal identity to
the scheduler and ownership state. This slice supplies the sequential resource
foundation for those proofs; it does not establish thread safety by itself.
