# A counted loop with an unbounded execution proof

The `increment-loop` function profile returns
`low32(initial RDI) + initial RCX` modulo 2³². It accepts every 64-bit RCX
count, including zero. Its exact user-instruction cost is `2 * count + 3`.
The cost is a natural number and may exceed 2⁶⁴. This is a functional and
termination theorem about the machine model, not a finite unrolling experiment.

The owned assembly entry is:

```asm
mov eax, edi
jrcxz done
body:
lea eax, [rax + 1]
loop body
done:
ret
```

Exact bytes: `89 f8 e3 05 8d 40 01 e2 fb c3`.
The assembly uses RDI for the value and RCX for the count. In a System V native
function call, RCX carries the fourth integer argument; RSI/RDX are unused.
The fixture is authored in assembly and assembled by Clang/GCC. These results
do not establish a C/C++ compiler's loop transformation or source equivalence.

## Machine semantics

The decoder adds only these forms:

- `89 f8`: MOV EAX, EDI, zero-extending the result into RAX.
- `8d 40 ib`: LEA EAX, [RAX + signed disp8], with 64-bit address calculation
  and a 32-bit zero-extended destination. No data access occurs.
- `e3 cb`: JRCXZ with the default 64-bit address size; tests full RCX.
- `e2 cb`: LOOP with the default 64-bit address size; decrements full RCX
  modulo 2⁶⁴, then branches if the result is nonzero.

Both branches measure signed disp8 from the following instruction. A taken
noncanonical target reports `.noncanonicalBranch`; an untaken target is not
checked. LOOP and JRCXZ preserve flags; LOOP neither reads nor modifies ZF.
In particular, executing LOOP with initial RCX zero wraps to 2⁶⁴−1. The entry
guard avoids that behavior in the checked function's zero-count case.
Address-size overrides, LOCK/REX prefixes and other LOOP variants reject rather
than silently using a different counter width or condition.

These rules follow Intel SDM revision 093, volume 2A, Jcc pages 3-502–503 and
LOOP/LOOPcc pages 3-570–572, with MOV/LEA and 32-bit destination rules from the
same architecture reference. The primary
[Intel manual index](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)
links the [revision 093 volume](https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf).
Model adequacy and physical execution remain a reviewed conformance boundary.

The mutex worker additionally uses exact `83 f8 00` (CMP EAX,0) and `75 cb`
(JNE/JNZ rel8). CMP preserves all registers and memory, sets ZF/SF/PF from
the low32 operand, clears CF/AF/OF and preserves other flags. JNZ reads only ZF,
preserves flags/registers/memory and uses the same signed branch target checks.
Only the zero-immediate EAX form is supported; prefixes and other CMP forms
reject. These rules follow the CMP and Jcc entries in
[Intel SDM volume 2A, revision 089, pages 3-161–162 and 3-491–495](https://cdrdv2-public.intel.com/868140/253666-089-sdm-vol-2a.pdf).
`tests/MutexISA.lean` checks independently specified status masks, both branch
directions, operand widths and boundaries, preserved state and rejected forms.

## Proof and composition

`X86.Steps` describes any finite sequence of ordinary `.next` transitions,
including zero steps. `Steps.trans`, `Executes.prepend` and `Invokes.prepend`
compose instruction counts without treating RET or syscalls as ordinary steps.
This infrastructure is independent of the particular loop bytes.

`IncrementLoop.invariantState` describes a zero-extended accumulator, a natural
remaining count represented in RCX, unchanged flags/memory/other registers and
the body or return address selected by whether the remainder is zero.
`body_step` binds the increment instruction to actual executable bytes.
`backedge` proves the decrement/branch transition to the next invariant state,
using canonical executable-address evidence from the same checked code window.

`loop_executes` inducts on the natural remaining count, with bound `remaining <
2^64`. Each iteration adds one modulo 2³² and decreases the variant. Its base
case executes RET. `entry_steps` accounts for MOV and the zero guard;
`actual_bytes_correct` composes them with the loop. No solver certificate,
project axiom or assumed invariant establishes this result.

`terminates_and_all_results_match` proves a finite execution, unique final
state/count, and exclusion of an infinite ordinary-step trace. The final state
has zero-extended modular output in RAX, RCX=0, RSP advanced by eight, RIP equal
to the readable stack return address, and all other registers/flags/memory
preserved. The return target must be canonical. Every byte in the nonwrapping
code window must be executable; the return-stack word must be readable.

These are user-execution claims in the sequential machine model. Unbounded OS
preemption, interrupts and environmental interference are excluded by its
platform contract. There is no wall-clock bound, optimality theorem, memory
ownership/lifetime proof, general loop-invariant inference or arbitrary assembly
validator. The earlier restricted function/syscall lower bounds remain checked
over the expanded supported instruction set.

## Certificates and evidence

```sh
lake build EDSL.All edsl-certify
lake env lean -DwarningAsError=true tests/ControlFlow.lean
lake exe edsl-certify increment-loop FUNCTION.bin artifacts/Loop.lean
lake exe edsl-certify --elf increment-loop FUNCTION.elf artifacts/ELFLoop.lean
bash scripts/verify-loops.sh
```

Raw certificates retain explicit executable-byte binding. Full-file ELF
certificates derive that binding through the modeled loader and retain caller
freshness/stack/return-target conditions. See [ELF scope](elf.md) for the loader
contract; the loop ELF is a function container, not a Linux process entry.

Lean checks independently expected return values, cost, preserved flags and
return-stack behavior. It also checks full-width RCX branch/decrement behavior,
zero-counter underflow, signed backward offsets, taken-target validation and
unsupported address-size prefixes. `every_input_executes` supplies satisfiable
code/stack states for every value/count, including counts too large to execute
in a practical test.

`verify-loops.sh` assembles with Clang/GCC, links, checks both raw and full-file
certificates, then executes only certified owned bytes using bounded native
inputs. The native table independently specifies zero, high-bit input, wraparound
and larger-count outcomes. Changed guard/backedge offsets, an increment by two,
an unsupported prefix, truncation and changed ELF code must reject. Negative
fixtures are never executed. Versions, arguments, disassembly and artifact hashes
are recorded under ignored `artifacts/loop-fixtures/`; CI uploads only those
owned artifacts. Native tests supplement the all-input theorem and do not prove
universal hardware conformance.
