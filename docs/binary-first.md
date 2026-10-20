# Binary-first verification

eDieSeL starts with machine code and an independently written contract. Its
current reusable path proves restricted sequential x86-64 functions, including
read-only memory and loops, with caller-resource and final-ELF composition.
Writable calls, process boundaries and managed concurrency use separate
profiles. [Coverage](coverage.md) lists the implemented limits.

## One machine-code target for many implementation languages

A contract states what the program should do: for example, return a modular
sum, read only permitted input regions, and preserve the caller's resources.
It does not define success by reference to the candidate's instructions or a
successful checker run. The proof connects that contract to execution of the
exact bytes.

The general theorem shape is schematic, not a Lean API:

```text
For every admitted initial state and environment,
every execution covered by the selected machine/OS model
satisfies the independent contract for these exact bytes.
```

The theorem states whether it covers safety, completed calls, termination or
progress. These are different obligations. The current sequential call bridges
prove total execution under their premises; concurrent profiles have their own
schedule and completion contracts.

C and C++ compiler outputs supply current reference artifacts. Code compiled
from other languages can be a candidate when its final instructions, ABI,
runtime dependencies and effects fit an implemented profile. A
source-preservation claim additionally needs a relation to that source
language's semantics.

## What work is shared and what remains

| Reusable layer | Obligation for a candidate |
| --- | --- |
| Exact-byte decoding and machine semantics | Every reached encoding and behavior must fit the selected profile |
| Sound verification-condition generator | Prove the independent result, permissions, invariants and termination conditions |
| Call and resource adapters | Supply present code, arguments, original return stack and current authority |
| Restricted ELF checks and certificate constructors | Bind the complete file, selected function and semantic proof; supply loading/caller premises |
| Specialized OS and concurrency models | Cover the actual resources, interference, memory ordering and progress assumptions |

Assembly listings, symbol tables and hashes help locate or identify code.
Checked byte selection and execution establish the formal connection. A proof
about one selected function in an ELF file does not cover all linked code or
the native loader. Another ISA, or privileged kernel execution, needs its own
semantics and composition proofs.

## Source and IR as assistance

The [CFG importer](cfg.md) proposes a graph for a raw window or restricted ELF
selection. [Named-function import](named-elf-import.md) also proposes metadata
for a requested symbol, including a non-entry function. Kernel-checked facts
bind these proposals to the selected bytes. Import alone proves no functional
result and creates no native resource authority.

Clients use the [reusable checker](reusable-checker.md) with their own contract.
Loops need sparse cutpoint invariants and decreasing ranks. Source structure,
LLVM IR, debug information and optimization remarks can suggest those proofs;
their suggestions must be checked against the machine semantics.

Source eDSLs and IR semantics are longer-term routes for generation and optional
preservation proofs. They are not prerequisites for a direct binary theorem.
The [language plan](languages.md) describes their separate obligations.

<a id="first-implementation-gate"></a>

## Start with a function

Follow [Verify a new function](verify-a-function.md): state the mathematics,
supply exact bytes and a checked CFG, prove generated conditions, then reuse
the call/resource bridge. A [standalone scalar ELF certificate](elf-certificates.md)
can bind that proof to a named function in a complete final file without a new
task registration or command driver.

Security claims likewise name the behavior or resource property proved under
the stated model. A failed proof, timeout or unsupported encoding establishes
no vulnerability. [Verification contracts](verification.md) and
[trust](trust.md) explain how to read the resulting theorem and its limits.
