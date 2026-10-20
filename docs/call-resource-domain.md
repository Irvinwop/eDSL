# Modeled initial callable resources at arbitrary addresses

`EDSL.OS.CallResources.Domain` constructs a new explicit modeled ownership and
borrowing environment over a supplied `AddressSpace.Space`. The code address,
bytes, original caller STACK8 address, return target, code owner, caller owner
and worker are all parameters. There is no fixed 4096 entry, fixed return slot,
byte grammar, decoder result, CFG, execution, desired output or successful
future-call premise.

This is an initial-environment constructor, not transport of an existing loan
or resource world. The selected principal names and initial authority records
are declared model inputs. Readable native memory does not establish native
OS ownership, actual process/thread identity or authority to initialize this
registry. A deployment must justify how its actual environment corresponds to
the declared model. No end-to-end corpus certification count increases merely
because this resource domain is inhabited.

## Inputs and independent obligations

`Initial` contains the complete supplied space, `codeOwner`, `callerOwner`,
`worker`, numeric code address, literal bytes, caller-slot address and expected
return address. `Facts` requires:

- Nonempty valid canonical nonwrapping code and eight-byte caller intervals.
- Disjoint code/caller intervals and readability of every cell in each interval.
- Exact `CodeAt` in the supplied current memory, including execute permission.
- An actual `readWord` of the original caller slot returning the expected target.
- The existing return-canonicality, strict stack-end and post-RET RSP bounds.

`check` is a finite mapping/value preflight proved sound and complete for those
facts. It invokes the existing byte checker and actual `readWord`; it does not
interpret code instructions. A false check establishes no resource-domain
witness through this API and says nothing about a program defect. In particular,
readable-but-nonexecutable code, an inaccessible mapped caller byte, or a wrong
claimed return address does not pass.

`code_readable` derives the finite code-read preflight from exact `CodeAt`
evidence. `allReadable_of_cells` connects semantic region readability to the
existing borrowing preflight. These lemmas allow a caller to use a proved loader
or checked current code evidence without enumerating custom per-program loans.

## Constructed world and actual loans

`codeWorld` and `world` use the existing `Ownership.install` API to register two
allocations in a newly declared empty registry. The code allocation has ticket
`(0,0)` and the caller allocation has ticket `(1,0)`; both retain their separately
declared owner. The world frontier is 2. All original supplied cells and their
permissions survive exactly, including unrelated inaccessible cells; cells
outside these two intervals remain unregistered by this initial model.

`borrow_code` and `borrow_stack` prove that the existing `Borrowing.readBorrow`
operations actually issue loans 0 and 1 to `Threads.principal worker` in that
registry. Their well-formedness follows through the existing borrowing API.
The constructor does not create a new authorization or mutation semantics.
`shared_valid`, `code_held`, `stack_held` and `contract` provide the existing
`Borrowing.WellFormed`, `Threads.HasLoan` and `CallResources.Contract` predicates.

The reverse `contract_facts` theorem retrieves validity/disjointness from the
actual registered allocations and readability from actual code and stored loan
facts. Admission is not defined as the Boolean check. The theorem
`nonempty_iff` establishes that this particular new modeled callable domain is
inhabited exactly when `check` succeeds.

## Callable machine states

`machine` accepts arbitrary register values and flags, installs the supplied
numeric code PC and original caller-slot RSP, and uses exactly the supplied
space's memory projection. `current` proves the existing `CallResources.Current`
predicate. `callable` packages it with the entry-PC and RSP equalities;
`nonempty` and `checked_nonempty` establish domain inhabitants independently of
instruction interpretation.

This supplies resource nonvacuity for later independent contracts, including
unequal min/max arguments chosen through the register parameter. It does not
supply the mathematical result, caller register preservation, termination,
read-only policy, execution trace or instruction count of a candidate body.
It adds no full SysV ABI theorem or stack-alignment rule beyond the existing
CallResources contract. Stable mappings, interference exclusion, CPU features
and any stronger ABI requirements must be stated by the consuming proof.

An ELF consumer can supply its complete modeled loaded space as `Initial.space`,
select a numeric non-entry callable window and obtain `CodeAt` from a checked
full-file/window bridge. It must separately retain the loader/admission and
unchanged-text hypotheses. Resource metadata is newly declared after choosing
that space; an executable mapping is never treated as evidence of a surviving
pre-existing native loan. Dynamic linking, actual Linux mappings, physical CPU
conformance and source-language preservation remain separate obligations.

## Validation

`tests/CallResourcesDomain.lean` uses a non-4096 Clang-shaped callable window with
a different code owner, caller owner and worker. Its original caller loan is
used by an actual modeled final RET for arbitrary caller registers, flags and
AF choice, with the same complete current OS world retained after return.
Negative cases cover overlapping intervals, a missing final caller byte,
mapped-but-inaccessible caller memory, readable code lacking execute permission,
wrong exact code bytes, wrong expected return data and an empty code interval.
An uninterpreted UD2 window still has a modeled resource domain, demonstrating
that domain existence requires no instruction-safety or desired-result premise.
These project-owned synthetic cases establish no native or security finding.
