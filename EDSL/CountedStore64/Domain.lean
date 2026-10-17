/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Contract
import EDSL.Grading.StoreReturnValue64.Domain

set_option warningAsError true

namespace EDSL.CountedStore64.Domain
open EDSL X86 X86.Sequential

namespace Base
export EDSL.Grading.StoreReturnValue64.Domain (resource initial resource_pre)
end Base

/-- Candidate-independent current resources; no loop, decode or mutation
success is required by this constructor. -/
def resource (bytes : List Byte) (argument count : Word) : Resources :=
  ⟨Base.resource bytes argument, count⟩

def initial (bytes : List Byte) (argument count : Word)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) : State :=
  Base.initial bytes argument (fun register => if register = .rdx then count else registers register) flags

/-- All full64 counts, arbitrary other volatile registers and flags have
present raw/current admissions for every bounded nonempty candidate window. -/
theorem resource_pre (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (argument count : Word)
    (registers : Register → Word := fun _ => 0xfedcba9876543210)
    (flags : Word := 0x602) :
    ResourcePre bytes (resource bytes argument count) (initial bytes argument count registers flags) :=
  ⟨Base.resource_pre bytes positive bound argument
    (fun register => if register = .rdx then count else registers register) flags, rfl⟩

structure CandidateWitness (bytes : List Byte) where
  resource : Resources
  initial : State
  pre : ResourcePre bytes resource initial
  useful : Useful (resourceInput resource)

def candidate (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) : CandidateWitness bytes where
  resource := resource bytes 0 1
  initial := initial bytes 0 1
  pre := resource_pre bytes positive bound 0 1
  useful := by
    change (0 : Word) ≠ 1
    decide

/-- A useful full64 change need not change the low32 target bits. -/
def upperOnly (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) : CandidateWitness bytes where
  resource := resource bytes 0xffffffff 1
  initial := initial bytes 0xffffffff 1
  pre := resource_pre bytes positive bound 0xffffffff 1
  useful := by
    change (0 : Word) ≠ 0x100000000
    decide

def unsupported : CandidateWitness [0xff] := candidate [0xff] (by decide) (by decide)

theorem unsupported_rejected :
    Sequential.decodeAt unsupported.initial = .error (.unsupportedOpcode 0xff) := rfl

end EDSL.CountedStore64.Domain
