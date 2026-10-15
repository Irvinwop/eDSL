/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.Invocation

namespace EDSL.X86

/-- Finite ordinary user steps. RET and syscall requests are boundaries rather
than silent steps; zero steps allow sequential proof composition. -/
inductive Steps : State → State → Nat → Prop where
  | refl {state} : Steps state state 0
  | next {initial middle final count}
      (transition : step initial = .ok (.next middle))
      (tail : Steps middle final count) : Steps initial final (count + 1)

theorem Steps.trans {initial middle final : State} {firstCount lastCount : Nat}
    (first : Steps initial middle firstCount) (last : Steps middle final lastCount) :
    Steps initial final (firstCount + lastCount) := by
  induction first with
  | refl => simpa using last
  | next transition _ induction =>
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.next transition (induction last)

theorem Executes.prepend {initial middle final : State} {firstCount lastCount : Nat}
    (prefixSteps : Steps initial middle firstCount) (tail : Executes middle final lastCount) :
    Executes initial final (firstCount + lastCount) := by
  induction prefixSteps with
  | refl => simpa using tail
  | next transition _ induction =>
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Executes.next transition (induction tail)

theorem Invokes.prepend {initial middle : State} {request : SyscallRequest} {firstCount lastCount : Nat}
    (prefixSteps : Steps initial middle firstCount) (tail : Invokes middle request lastCount) :
    Invokes initial request (firstCount + lastCount) := by
  induction prefixSteps with
  | refl => simpa using tail
  | next transition _ induction =>
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Invokes.next transition (induction tail)

theorem fetch_canonical {memory : Memory} {address : Word} {byte : Byte}
    (fetched : fetchByte memory address = .ok byte) : canonical address = true := by
  unfold fetchByte at fetched
  split at fetched
  next allowed => exact (Bool.and_eq_true_iff.mp allowed).1
  next => cases fetched

end EDSL.X86
