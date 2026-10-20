# Lean library

For a new proof, [start with the function guide](../docs/verify-a-function.md).
The [module map](../docs/repository-layout.md) explains where extensions belong.

| Import / directory | Role |
| --- | --- |
| `EDSL` | Reusable sequential checker, call contracts and scalar ELF certificates |
| `EDSL.All` | Full proof catalogue for audit/replay and compatibility |
| [`X86/Sequential/`](X86/Sequential/) | Production decoder, execution, CFGs and frames |
| [`X86/VCGen/`](X86/VCGen/) | Shared sound checker, cutpoints and proof tactics |
| [`PureCall/`](PureCall/), [`BufferCall/`](BufferCall/) | Callable mathematical contracts with current OS resources |
| [`OS/`](OS/), [`Concurrency/`](Concurrency/) | Allocation, permissions, ownership, effects, scheduling and histories |
| [`ELF/`](ELF/) | Complete-file identity, named function inputs and caller installation |
| [`Corpus/`](Corpus/) | Registered certificate adapters and frozen clients |
| [`Examples/Verification/`](Examples/Verification/) | Small worked clients of the reusable API |
| [`Corpus/V1/`](Corpus/V1/) | Specific frozen compiler outputs and their proofs |
| [`Grading/`](Grading/) | Fixed contract registration and kernel proof-packet validation |

Other named program directories are existing specialized clients. Their paths
and theorem namespaces remain stable; [reference documentation](../docs/README.md)
states each profile's scope. New programs should reuse the shared layers above.
