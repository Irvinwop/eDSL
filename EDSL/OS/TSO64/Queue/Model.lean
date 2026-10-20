/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Resources
import EDSL.OS.AtomicAccess64

namespace EDSL.OS.TSO64.Queue
open X86

/-- Admit the original store without publishing it. Prefer the existing ordinary
grant; only an exact-address qword may fall back to current managed authority.
The supplied occurrence is retained, not allocated from queue length or value. -/
def admit (world : World) (resources : Resources) (store : Store) (occurrence : Nat)
    (profile : Profile := .ownedOnly) : Except Fault Entry :=
  match grantFor world resources store with
  | some ticket => .ok (.ordinary ticket store)
  | none =>
      match profile, store.value with
      | .sharedCell, .qword value =>
          match atomicFor world resources store.address with
          | none => .error .noAtomicGrant
          | some (identifier, handle, cell) =>
              .ok (.managed ⟨identifier, handle, cell⟩ value occurrence)
      | _, _ => .error .noGrant

/-- Recheck the retained authority at the current world before publication.
The default policy rejects a managed entry even in an arbitrary initial queue.
This policy operation performs no instruction execution or implicit drain. -/
def publish (world : World) (resources : Resources) (entry : Entry)
    (profile : Profile := .ownedOnly) : Except Fault (World × Option Atomics64.StoreEvent64) := do
  if ¬Valid world resources entry profile then throw .resource
  match entry with
  | .ordinary ticket store =>
      let result ← (Atomics64.mutate world (operation resources.actor ticket store)).mapError Fault.os
      return (result.1, none)
  | .managed reference value _ =>
      let result ← (Atomics64.publishStore world resources.actor reference.identifier value).mapError Fault.os
      return (result.1, some result.2)

/-- Publish exactly the oldest retained entry. The returned tail is literal;
no peer queue, return instruction or partial overlay causes publication. -/
def publishHead (world : World) (resources : Resources) (entries : List Entry)
    (profile : Profile := .ownedOnly) :
    Except Fault (World × List Entry × Option Atomics64.StoreEvent64) := do
  let head :: tail := entries | throw .emptyBuffer
  let result ← publish world resources head profile
  return (result.1, tail, result.2)

end EDSL.OS.TSO64.Queue
