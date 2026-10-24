# Counter contract support

The complete GCC and Clang `c_counter_worker` windows share call, history and
return assertions. These support modules reduce the work needed for their
compiler-specific proofs. They do **not** yet certify either complete function
or add corpus coverage. The checked byte graphs are described in
[mixed instruction graphs](mixed-cfg.md).

Import `EDSL.Corpus.V1.CounterAssertions` for the common assertions, in namespace
`EDSL.Corpus.V1.CounterCommon`:

- `Call` independently names the pointer, unsigned 32-bit iteration count,
  atomic target cell and return address. `Site` fixes the compiler window and
  original worker/resources. `descriptor` reuses the complete checked graph.
- `Pre` requires current loaded code, well-formed resources, running entry PC,
  RDI, low32 RSI, protected caller stack, a canonical return target and the
  scheduler's actual first matching atomic selector linked to the target cell.
  It requires no future execution, initial shared-word value, empty FIFO,
  upper32 RSI value, or initial flag value. Actor and worker index are distinct.
- `LiveData` carries the pointer, caller stack, saved ABI context and current
  selector. `OwnIncrements` authenticates every earlier own RMW with its real
  typed issue and compiler-specific ADD or INC tag, along with unit delta and
  independently named actor, pointer and target.
- `Inv` combines those shared facts with compiler-local register arithmetic,
  parameterized by the exact natural-number count of the full history.
  `Inv.idle` preserves them through authenticated peer issues, FIFO drains and
  unchanged own blocked attempts.
- `Post` requires exactly the requested number of own RMWs, authenticated unit
  increments, actual returned phase and caller PC, callee-saved registers,
  nonarithmetic flags, and the original RSP plus eight in modular Word arithmetic.
  It makes no RAX-result or current shared-memory assertion. `stablePost` allows
  later idle positions; `completed_count` projects to the entire observation
  list of a successful finite returned schedule **given separately proved
  compiler annotations and current Entry**.

The generic current ordinary-step adapter is in
`EDSL.OS.TSO64.EffectSimulation.Mixed.CallerContinuation` and the public
`EDSL.OS.TSO64.EffectSimulation` umbrella. `One.of_callerContinuation` takes CPU
execution, protected reads and a result continuation for every flag choice.
It derives current authority, read/queue readiness and the real ordinary or
returned finish with the existing FIFO. It has no additional byte-window bound.

`EDSL.OS.TSO64.Increment64` specializes an actual arithmetic machine effect to
INC or encoded ADD-imm8(1). It retains the complete effect, current old/new word,
authorized handle/cell, actual instruction length, RIP, and every GPR. It does
not establish the scheduler's first selector by itself. XADD is excluded.

`EDSL.X86.Sequential.CounterArithmetic` supplies unsigned32 Nat laws for SUB2,
signed ADD-imm8(-8), LEA32(base-1) despite arbitrary upper bits, AND7 modulo eight,
and low-byte AND1 modulo two. Arithmetic parity is separate from the CPU parity
flag; ADD and SUB retain their different flag semantics.

Build the support directly with `lake build CounterContractSupport`. These
modules also belong to the complete catalogue and the fresh certificate gate.
Universal Lean proofs check the stated laws; no additional fixed-value tests
are needed for these adapters.

Compiler-specific block proofs, full function annotations, concurrent cohort
accounting, lifecycle/resource release and completion remain separate work.
An inherited FIFO may still drain writes, so the count assertion does not claim
that the call causes no other shared writes. All results retain the existing
long-mode/CET-off, coherent scalar WB RAM, stable translation/no-alias,
ownership and protected-loan assumptions. They add no fairness, termination,
physical CPU/Linux, compiler-preservation or minimum-operation guarantee.
