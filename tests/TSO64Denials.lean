/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64Fixtures
import EDSL.Audit

namespace EDSL.Tests.TSO64
open X86 OS.TSO64

def withSpace (world : Managed) (space : OS.AddressSpace.Space) : Managed :=
  { world with legacy := { world.legacy with shared :=
    { world.legacy.shared with resources := { world.legacy.shared.resources with space := space } } } }

/-- Synthetic invalid input states test the present preflight. These are not
external mutation actions admitted by the fixed-world scheduler. -/
def missingByte (world : Managed) (address : Word) : Managed :=
  let space := world.legacy.shared.resources.space
  withSpace world { cells := fun query => if query = address then none else space.cells query }

def readonlyByte (world : Managed) (address : Word) : Managed :=
  let space := world.legacy.shared.resources.space
  let cells query := (space.cells query).map fun cell => if query = address then
    { cell with permissions := OS.AddressSpace.readOnly } else cell
  withSpace world ⟨cells⟩

def stale (world : Managed) (id : Nat) : Managed :=
  let resources := world.legacy.shared.resources
  let allocations query := (resources.allocations query).map fun allocation =>
    if query = id then { allocation with epoch := allocation.epoch + 1 } else allocation
  { world with legacy := { world.legacy with shared := { world.legacy.shared with resources :=
    { resources with allocations := allocations } } } }

def noLoan (world : Managed) (id : Nat) : Managed :=
  { world with legacy := { world.legacy with shared := { world.legacy.shared with
    loans := fun query => if query = id then none else world.legacy.shared.loans query } } }

def deny (changeWorld : Ready → Managed) (first second : Word) (actions : List Action) := do
  let ready ← (fixture first second 0x11223344ffffffff).mapError OS.TSO64.Fault.os
  let state ← start ready 0 1 0
  let state := { state with world := changeWorld ready }
  let result ← schedule state actions
  pure (events result.2)

-- The low four bytes remain mapped, but a full64 XADD (even delta zero)
-- requires byte7. Missing/read-only upper bytes cannot be DWORD-coerced.
example : deny (fun ready => missingByte ready.checked.world 65543)
    0x07c10f48f0f08948 0x90909090909090c3 [.issue 0 false, .issue 0 false] =
    .error .noAtomicGrant := by rfl
example : deny (fun ready => readonlyByte ready.checked.world 65543)
    0x07c10f48f0f08948 0x90909090909090c3 [.issue 0 false, .issue 0 false] =
    .error .noAtomicGrant := by rfl

-- The actual registered allocation epoch is checked anew at the RMW.
example : deny (fun ready => stale ready.checked.world 0)
    0x07c10f48f0f08948 0x90909090909090c3 [.issue 0 false, .issue 0 false] =
    .error .noAtomicGrant := by rfl

-- Code/caller loans are mandatory NOW, and their lending ticket epoch and
-- complete readable extent are rechecked before instruction issue.
example : deny (fun ready => noLoan ready.checked.world ready.codeA)
    0x07c10f48f0f08948 0x90909090909090c3 [.issue 0 false] = .error .resource := by rfl
example : deny (fun ready => stale ready.checked.world 5)
    0x07c10f48f0f08948 0x90909090909090c3 [.issue 0 false] = .error .resource := by rfl
example : deny (fun ready => missingByte ready.checked.world 262151)
    0x07c10f48f0f08948 0x90909090909090c3 [.issue 0 false] = .error .resource := by rfl

-- A qword ordinary store cannot use mapped low bytes to cover byte7.
example : deny (fun ready => missingByte ready.checked.world 131079)
    0x48f0f08948328948 0x90909090c307c10f [.issue 0 false] = .error .noGrant := by rfl
example : deny (fun ready => readonlyByte ready.checked.world 131079)
    0x48f0f08948328948 0x90909090c307c10f [.issue 0 false] = .error .noGrant := by rfl
example : deny (fun ready => stale ready.checked.world 1)
    0x48f0f08948328948 0x90909090c307c10f [.issue 0 false] = .error .noGrant := by rfl

def staleDrain := do
  let ready ← (fixture 0x48f0f08948328948 0x90909090c307c10f 19).mapError OS.TSO64.Fault.os
  let state ← start ready 1 2 0
  let queued ← issue state 0 false
  let result ← drain { queued.1 with world := stale queued.1.world 1 } 0
  pure result.2.retired

-- Queueing does not waive the CURRENT epoch check at publication. This
-- synthetic invalid input is outside the fixed-world run operations.
example : staleDrain = .error .resource := by rfl

def overlayNoAuthority := do
  let ready ← (fixture 0x90c31a8b48328948 0x9090909090909090 19).mapError OS.TSO64.Fault.os
  let state ← start ready 1 2 0
  let queued ← issue state 0 false
  let broken := { queued.1 with world := missingByte queued.1.world 131079 }
  let result ← issue broken 0 false
  pure result.2.retired

-- All eight bytes are forwarded, so the raw local load would succeed. A
-- missing CURRENT published byte still denies authority; overlay is no grant.
example : overlayNoAuthority = .error .noGrant := by rfl

def wrongHandle (identifier : OS.Atomics64.HandleId64) := do
  let ready ← (fixture 0x07c10f48f0f08948 0x90909090909090c3 19).mapError OS.TSO64.Fault.os
  let state ← start ready 1 2 0
  let some worker := state.workers[0]? | throw OS.TSO64.Fault.missingWorker
  let resources : OS.TSO64.Resources := ⟨worker.resources.actor, worker.resources.code,
    worker.resources.caller, worker.resources.callerAddress, worker.resources.grants, [identifier]⟩
  let replacement : OS.TSO64.Worker := ⟨worker.context, resources, worker.phase, worker.pending⟩
  let state := OS.TSO64.install state 0 state.world replacement
  let result ← schedule state [.issue 0 false, .issue 0 false]
  pure (events result.2)

-- Handle1 belongs to actor12, and handle99 is absent. A matching raw address
-- and readable/writable RAM do not confer actor authority.
example : wrongHandle ⟨1⟩ = .error .noAtomicGrant := by rfl
example : wrongHandle ⟨99⟩ = .error .noAtomicGrant := by rfl

def wrongBorrower := do
  let ready ← (fixture 0x07c10f48f0f08948 0x90909090909090c3 19).mapError OS.TSO64.Fault.os
  let worker ← makeWorker ready.checked.world 12 (context 262144 131072 1 0)
    ready.codeA ready.callerA [ready.dataA] [ready.atomicA]
  pure worker.phase

example : wrongBorrower = .error (.loan .wrongBorrower) := by rfl

-- Source RSP is supported by the generic locked family. The returned old
-- value is a mapped replacement slot, but RET still requires the original.
example : (run 0x9090c327c10f48f0 0x9090909090909090 131072 1 2 0
    [.issue 0 false, .issue 0 false]).map (fun result => events result.2) = .error .callerSlot := by rfl

def blockedAllocation (kind : Nat) := do
  let ready ← (fixture 0x48f0f08948328948 0x90909090c307c10f 19).mapError OS.TSO64.Fault.os
  let world ← if kind = 0 then do
    let borrowed ← (OS.Atomics64.readBorrow ready.checked.world 11 ready.dataA 99 ⟨131080,4⟩).mapError OS.TSO64.Fault.os
    pure borrowed.1
  else do
    let reserved ← (OS.Atomics64.issue32 ready.checked.world 11 ready.dataA 99 131072).mapError OS.TSO64.Fault.os
    pure reserved.1
  let state ← start ready 1 2 0
  let result ← issue { state with world := world } 0 false
  pure result.2.retired

-- A disjoint subregion's read loan still freezes the ENTIRE allocation.
example : blockedAllocation 0 = .error .noGrant := by rfl
-- Legacy32 reservations are also allocation-wide, despite qword execution.
example : blockedAllocation 1 = .error .noGrant := by rfl

def reserved64 := do
  let ready ← fixture 0x48f0f08948328948 0x90909090c307c10f 19
  let resources : Resources := ⟨7, ⟨0, ⟨⟨0,0⟩,7,7,⟨0,1⟩⟩⟩,
    ⟨0, ⟨⟨0,0⟩,7,7,⟨0,1⟩⟩⟩,0,[⟨0,0⟩],[]⟩
  pure (grantFor ready.checked.world resources ⟨65544,.qword 1⟩)

-- The neighbor qword is ordinary RW data inside the registered allocation,
-- but the persistent 64-bit cell reservation excludes the entire allocation.
example : reserved64 = .ok none := by rfl

def unaligned := do
  let ready ← (fixture 0x48f0f08948328948 0x90909090c307c10f 19).mapError OS.TSO64.Fault.os
  let state ← start ready 1 2 0
  let some worker := state.workers[0]? | throw OS.TSO64.Fault.missingWorker
  let registers (register : Register) : Word :=
    if register = X86.Register.rdx then 131073 else worker.context.registers register
  let context : OS.TSO64.Context := ⟨registers, worker.context.rip, worker.context.flags⟩
  let replacement : OS.TSO64.Worker := ⟨context, worker.resources, worker.phase, worker.pending⟩
  let result ← issue (install state 0 state.world replacement) 0 false
  pure result.2.retired

example : unaligned = .error .noGrant := by rfl

end EDSL.Tests.TSO64

#audit_edsl
