/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.AtomicMethods

/-!
Reusable ordinary-instruction rules for the production resource-checked TSO64
scheduler. Both authority profiles and nonempty valid mixed FIFOs are supported.
Instruction decoding comes from checked bytes; operand admission, queue effects,
and computation come from the existing semantics. These rules introduce no
instruction interpreter, source-order inference, or scheduler oracle.
-/

set_option autoImplicit false

namespace EDSL.X86.VCGen.ManagedRules
open OS OS.TSO64 AtomicMethods

/-- Current valid own-buffer stores cannot shadow a protected code loan. Thus
the local data projection still decodes the current published code, including
after a buffered store and before its drain. No empty-queue premise is needed. -/
theorem local_code {state : OS.TSO64.State} {worker : Worker} {profile : Profile}
    {base : Word} {bytes : List Byte}
    (valid : WellFormed state profile) (workerValid : WorkerValid state.world worker profile)
    (code : CodeAt (published state.world) base bytes)
    (fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region) :
    CodeAt (localCPU state worker).memory base bytes := by
  refine ⟨code.1, ?_⟩
  intro offset byte present
  have bound := (List.getElem_of_getElem? present).1
  have small : offset < 2^64 := by have := code.1; omega
  have sum : base.toNat + offset < 2^64 := by have := code.1; omega
  have natural : (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
      Nat.mod_eq_of_lt sum]
  have inside : (⟨base, bytes.length⟩ : AddressSpace.Region).Contains
      (base + BitVec.ofNat 64 offset) := by
    constructor <;> simp only [natural] <;> omega
  have loanInside := Borrowing.subregion_inside fits inside
  have listed := AddressSpace.contains_mem_addresses worker.resources.code.loan.region
    (base + BitVec.ofNat 64 offset) loanInside
  obtain ⟨loanOffset, loanBound, address⟩ := List.mem_map.mp listed
  have agreement := local_loan_agrees valid workerValid workerValid.1.1.1
  have read : (localCPU state worker).memory.read (base + BitVec.ofNat 64 offset) =
      (published state.world).read (base + BitVec.ofNat 64 offset) := by
    rw [← address]
    exact agreement loanOffset (List.mem_range.mp loanBound)
  have executable : (localCPU state worker).memory.executable =
      (published state.world).executable := StoreBuffer.Mixed.view_executable _ _
  have fetched := code.2 offset byte present
  unfold fetchByte
  rw [executable, read]
  exact fetched

/-- The queue-effect contract is executable admission, not an oracle for a
desired poststate. This converse keeps ordinary-grant priority and the managed
profile/width/identity checks in the production admission function. -/
theorem queue_checked {state : OS.TSO64.State} {worker : Worker}
    {instruction : Sequential.Instruction} {update : Queue.Cursor} {profile : Profile}
    (effect : QueueEffect state worker instruction update profile) :
    prepareQueue state worker instruction profile = .ok update := by
  cases effect with
  | unchanged intent => simp only [prepareQueue, intent, pure_ok]
  | enqueued intent admission =>
      cases admission with
      | ordinary ticket selected =>
          simp only [prepareQueue, intent, Queue.Cursor.enqueue, Queue.admit, selected,
            ok_bind, pure_ok, Queue.Cursor.enqueueOrdinary]
      | managed reference value ordinaryAbsent shared qword selected =>
          simp only [prepareQueue, intent, Queue.Cursor.enqueue, Queue.admit,
            ordinaryAbsent, shared, qword, selected, ok_bind, pure_ok,
            Queue.Cursor.enqueueManaged]

/-- A checked node and independent execution/admission conditions derive the
actual production issue. A pending FIFO is retained, and an admitted store
appends through the real queue cursor rather than publishing early. -/
theorem issue_ordinary {bytes : List Byte} {offset : Nat} {instruction : Sequential.Instruction}
    (node : Node bytes offset (.ordinary instruction)) (size : bytes.length ≤ 64)
    {state : OS.TSO64.State} {worker : Worker} {tid : Nat} {base : Word} {profile : Profile}
    (valid : WellFormed state profile) (live : state.workers[tid]? = some worker)
    (running : worker.phase = .running)
    (code : CodeAt (published state.world) base bytes)
    (fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region)
    (pc : worker.context.rip = base + BitVec.ofNat 64 offset)
    (admitted : supported instruction = true)
    (reads : ∃ units, (instruction.operandReads (localCPU state worker)).mapM
      (fun read => checkRead state worker read profile) = .ok units)
    {update : Queue.Cursor} (queue : QueueEffect state worker instruction update profile)
    {observation : Sequential.Observation} {af : Bool}
    (executed : Sequential.execute (localCPU state worker) instruction af = .ok observation) :
    issue state tid af profile =
      finishOrdinary state tid worker update.pending observation update.nextStore := by
  have workerValid := valid.2 worker (List.mem_of_getElem? live)
  have resource := workerValid.1
  have fetched := node.decoded size (guarded_code code fits) (fetchCPU state worker) rfl pc
  have localDecoded : Sequential.decodeAt (localCPU state worker) = .ok instruction :=
    decode_ordinary (node.decoded size (local_code valid workerValid code fits)
      (localCPU state worker) rfl pc)
  have bounds : codeFits worker instruction.length := node.codeFits code fits pc
  obtain ⟨units, checked⟩ := reads
  simp [issue, live, running, resource.1, resource.2.1, fetched, OS.TSO64.ordinary,
    admitted, bounds, localDecoded, checked, queue_checked queue, executed, Except.mapError]

theorem finish_checked {state : OS.TSO64.State} {tid : Nat} {worker : Worker}
    {pending : List Pending} {observation : Sequential.Observation}
    {result : OS.TSO64.State × Observation} {nextStore : Nat}
    (effect : FinishEffect state tid worker pending observation result nextStore) :
    finishOrdinary state tid worker pending observation nextStore = .ok result := by
  cases effect with
  | next outcome => simp only [finishOrdinary, outcome, pure_ok]
  | returned outcome => simp only [finishOrdinary, outcome, pure_ok]

/-- Compose the reusable instruction rule with a semantic finish effect to
derive an actual successful scheduler step. All intermediate facts concern the
current instruction and existing machine/resource semantics. -/
theorem step_ordinary {bytes : List Byte} {offset : Nat} {instruction : Sequential.Instruction}
    (node : Node bytes offset (.ordinary instruction)) (size : bytes.length ≤ 64)
    {state : OS.TSO64.State} {worker : Worker} {tid : Nat} {base : Word} {profile : Profile}
    (valid : WellFormed state profile) (live : state.workers[tid]? = some worker)
    (running : worker.phase = .running)
    (code : CodeAt (published state.world) base bytes)
    (fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region)
    (pc : worker.context.rip = base + BitVec.ofNat 64 offset)
    (admitted : supported instruction = true)
    (reads : ∃ units, (instruction.operandReads (localCPU state worker)).mapM
      (fun read => checkRead state worker read profile) = .ok units)
    {update : Queue.Cursor} (queue : QueueEffect state worker instruction update profile)
    {observation : Sequential.Observation} {af : Bool}
    (executed : Sequential.execute (localCPU state worker) instruction af = .ok observation)
    {result : OS.TSO64.State × Observation}
    (finish : FinishEffect state tid worker update.pending observation result update.nextStore) :
    OS.TSO64.step state (.issue tid af) profile = .ok result := by
  change issue state tid af profile = .ok result
  rw [issue_ordinary node size valid live running code fits pc admitted reads queue executed]
  exact finish_checked finish

end EDSL.X86.VCGen.ManagedRules
