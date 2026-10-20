/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.Policy

set_option warningAsError true

namespace EDSL.PureCall
open X86 X86.Sequential

/-- A low32 binding deliberately leaves the upper argument half arbitrary. -/
inductive Argument where
  | word64 (value : Word)
  | low32 (value : BitVec 32)

def Argument.Holds : Argument → Word → Prop
  | .word64 value, actual => actual = value
  | .low32 value, actual => actual.setWidth 32 = value

def argumentRegister (index : Fin 6) : Register :=
  match index.val with
  | 0 => .rdi
  | 1 => .rsi
  | 2 => .rdx
  | 3 => .rcx
  | 4 => .r8
  | _ => .r9

/-- Trusted registration selects this entire specification. Submissions must
not select a weaker grading contract. Arbitrary Input/Prop fields cannot enforce
noncircular mathematics by type: concrete registry specs require independent
review of their inputs, domain, result and usefulness. -/
structure Spec where
  Input : Type
  arguments : Input → Fin 6 → Option Argument
  domain : Input → Prop
  result : Input → Word → Prop
  useful : Input → Prop

structure Invocation (spec : Spec) where
  value : spec.Input
  returnAddress : Word

def Bound (spec : Spec) (value : spec.Input) (state : State) : Prop :=
  ∀ index argument, spec.arguments value index = some argument →
    argument.Holds (state.registers (argumentRegister index))

/-- Present arguments, executable bytes and original caller slot only. No
decode, graph, fuel, desired result or future execution is an input premise.
Full native stack alignment and CPU/OS feature state are not encoded here. -/
structure Pre (spec : Spec) (bytes : List Byte)
    (input : Invocation spec) (initial : State) : Prop where
  domain : spec.domain input.value
  arguments : Bound spec input.value initial
  code : CodeAt initial.memory initial.rip bytes
  stack : readWord initial.memory (initial.registers .rsp) = .ok input.returnAddress
  returnCanonical : canonical input.returnAddress = true
  stackBound : (initial.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : canonical (initial.registers .rsp + 8) = true

def calleeSaved : List Register := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Mathematical return, complete RAM/permission equality, actual caller
return, SysV callee-saved GPRs and all nonarithmetic flags. Stronger observations
such as exact counts, read order or arithmetic flags belong in separate proofs. -/
structure Post (spec : Spec) (input : Invocation spec)
    (initial final : State) : Prop where
  result : spec.result input.value (final.registers .rax)
  memory : final.memory = initial.memory
  returnAddress : final.rip = input.returnAddress
  stackPointer : final.registers .rsp = initial.registers .rsp + 8
  preserved : ∀ register ∈ calleeSaved, final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

/-- Permission is tied to the original slot, regardless of a later RSP. -/
def RawRead (initial : State) (read : Read) : Prop :=
  read.kind = .stack ∧ read.address = initial.registers .rsp ∧ read.bytes = 8

/-- Proved execution policy, separate from the present-only input domain.
Stable ordinary RAM, the sequential target profile and no asynchronous
interference remain environmental assumptions of the production semantics. -/
def RawPolicy (initial : State) : Prop :=
  Grading.ReadOnlyPolicy initial (fun before => before.memory = initial.memory)
    (fun _ read => RawRead initial read)

end EDSL.PureCall
