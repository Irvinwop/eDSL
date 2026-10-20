/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.State

namespace EDSL.X86

/-- Userspace request boundary, before privileged execution. This is not the
kernel register state or a model of MSRs, privilege entry, RCX/R11 or SYSRET. -/
structure SyscallRequest where
  user : State
  continuation : Word

/-- Linux x86-64 syscall dispatch uses the low 32 bits of RAX. -/
def SyscallRequest.number (request : SyscallRequest) : BitVec 32 :=
  (request.user.registers .rax).setWidth 32

inductive SyscallArgument where
  | first | second | third | fourth | fifth | sixth
  deriving DecidableEq, Repr

def SyscallRequest.argument (request : SyscallRequest) : SyscallArgument → Word
  | .first => request.user.registers .rdi
  | .second => request.user.registers .rsi
  | .third => request.user.registers .rdx
  | .fourth => request.user.registers .r10
  | .fifth => request.user.registers .r8
  | .sixth => request.user.registers .r9

end EDSL.X86
