/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.ManagedRules
import EDSL.OS.TSO64.Return

/-!
Constructive RET rules for the actual resource-checked scheduler. Current code,
the original caller read and a canonical target derive a successful return under
either authority profile, including valid nonempty mixed queues. No store is
published and no future successful step or desired history is a premise.
-/

set_option autoImplicit false

namespace EDSL.X86.VCGen.ManagedReturn
open OS OS.TSO64 AtomicMethods

/-- Only RET's specified register, PC and phase updates. This is a proof-side
postcondition record; the production scheduler still executes the instruction. -/
def returnedWorker (worker : Worker) (target : Word) : Worker :=
  { worker with
    context := ⟨written worker.context.registers .rsp (worker.context.registers .rsp + 8),
      target, worker.context.flags⟩
    phase := .returned }

/-- Protected original caller reads survive actual issues and publications
under either profile. Shared-data values are not covered by this loan frame. -/
theorem loan_read_preserved {before : OS.TSO64.State} {action : Action}
    {result : OS.TSO64.State × Observation} {profile : Profile}
    (valid : WellFormed before profile)
    (success : OS.TSO64.step before action profile = .ok result)
    {borrower identifier : Nat} {address value : Word}
    (read : Borrowing.loadWord64 before.world.legacy.shared borrower identifier address = .ok value) :
    Borrowing.loadWord64 result.1.world.legacy.shared borrower identifier address = .ok value := by
  obtain ⟨loan, authority, fits, observed⟩ := Borrowing.loadWord64_ok _ _ _ _ _ read
  obtain ⟨live, owns⟩ := Borrowing.authorize_ok _ _ _ _ authority
  have stable := step_stable success
  have finalAuthority : Borrowing.authorize result.1.world.legacy.shared borrower identifier = .ok loan := by
    simp [Borrowing.authorize, stable.loans, live, owns]
  apply Borrowing.loadWord64_success _ _ _ _ _ loan finalAuthority fits
  apply (loadQWord_congr _ _ _ ?_).trans observed
  intro offset bound
  have loanValid := (valid.1.legacy.shared.2 identifier loan live).2
  obtain ⟨_, _, _, _, _, regionValid, _⟩ := loanValid
  exact (AddressSpace.toMemory_agrees_at _ _ _
    (step_loan_contents valid success live _
      (Borrowing.qword_inside loan regionValid address fits offset bound))).1

/-- Derive actual RET enabledness and its exact worker/world/FIFO/counter
result from current admission. Stack addition retains the modeled modular
word semantics; stronger ABI nonwrapping claims need their separate bounds. -/
theorem step_ret {bytes : List Byte} {offset : Nat}
    (node : Node bytes offset (.ordinary (.legacy .ret))) (size : bytes.length ≤ 64)
    {state : OS.TSO64.State} {worker : Worker} {tid : Nat} {base target : Word}
    {profile : Profile} (valid : WellFormed state profile)
    (live : state.workers[tid]? = some worker) (running : worker.phase = .running)
    (code : CodeAt (published state.world) base bytes)
    (fits : Borrowing.Subregion ⟨base, bytes.length⟩ worker.resources.code.loan.region)
    (pc : worker.context.rip = base + BitVec.ofNat 64 offset)
    (stack : worker.context.registers .rsp = worker.resources.callerAddress)
    (caller : Borrowing.loadWord64 state.world.legacy.shared worker.resources.actor
      worker.resources.caller.identifier worker.resources.callerAddress = .ok target)
    (canonicalTarget : canonical target = true) (af : Bool) :
    OS.TSO64.step state (.issue tid af) profile =
      .ok (install state tid state.world (returnedWorker worker target), .returned tid) := by
  have workerValid := valid.2 worker (List.mem_of_getElem? live)
  have word := (Borrowing.loadWord64_ok _ _ _ _ _ caller).choose_spec.2.2
  have localRead : readWord (localCPU state worker).memory (worker.context.registers .rsp) =
      .ok target := by
    rw [stack, local_original_caller valid workerValid]
    exact readWord_of_loadQWord _ _ _ word
  have stackGate : checkRead state worker ⟨.stack, worker.context.registers .rsp, 8⟩ profile =
      .ok () := by
    simp [checkRead, stack, caller, Except.mapError]
  let output : X86.State := { (localCPU state worker).writeRegister .rsp
    (worker.context.registers .rsp + 8) with rip := target }
  let observation : Sequential.Observation :=
    ⟨.returned output, [⟨.stack, worker.context.registers .rsp, 8⟩]⟩
  have executed : Sequential.execute (localCPU state worker) (.legacy .ret) af =
      .ok observation := by
    change readWord (localCPU state worker).memory ((localCPU state worker).registers .rsp) =
      .ok target at localRead
    simp only [Sequential.execute, Sequential.Instruction.operandReads, X86.executeInstruction,
      executeRet, localRead, canonicalTarget, ↓reduceIte, ok_bind, pure_ok]
    rfl
  have reads : ∃ units, ((Sequential.Instruction.legacy .ret).operandReads
      (localCPU state worker)).mapM (fun read => checkRead state worker read profile) = .ok units := by
    change checkRead state worker ⟨.stack, (localCPU state worker).registers .rsp, 8⟩ profile =
      .ok () at stackGate
    exact ⟨[()], by simp only [Sequential.Instruction.operandReads, List.mapM_cons,
      stackGate, ok_bind, List.mapM_nil, pure_ok]⟩
  have queue : QueueEffect state worker (.legacy .ret)
      ⟨worker.pending, worker.nextStore⟩ profile := .unchanged rfl
  have finish : FinishEffect state tid worker worker.pending observation
      (install state tid state.world (returnedWorker worker target), .returned tid)
      worker.nextStore := by
    change FinishEffect state tid worker worker.pending observation
      (install state tid state.world
        { worker with
          context := .ofCPU output
          phase := .returned
          pending := worker.pending
          nextStore := worker.nextStore }, .returned tid)
      worker.nextStore
    exact .returned rfl
  exact ManagedRules.step_ordinary node size valid live running code fits pc rfl
    reads queue executed finish

/-- A live installed RET returns the original full-width RAX. In particular,
later publication is not consulted to reconstruct a response. -/
theorem response {state : OS.TSO64.State} {worker : Worker} {tid : Nat} {target : Word}
    (live : state.workers[tid]? = some worker) :
    Return.returnValue
      (install state tid state.world (returnedWorker worker target), .returned tid) =
        some (tid, worker.context.registers .rax) := by
  have installed : (install state tid state.world (returnedWorker worker target)).workers[tid]? =
      some (returnedWorker worker target) :=
    List.getElem?_set_self (List.getElem_of_getElem? live).1
  change Option.map (fun current : Worker => (tid, current.context.registers .rax))
    (install state tid state.world (returnedWorker worker target)).workers[tid]? = _
  rw [installed]
  change some (tid, written worker.context.registers .rsp
    (worker.context.registers .rsp + 8) .rax) = _
  rw [written_other _ _ _ _ (by decide : Register.rax ≠ .rsp)]

end EDSL.X86.VCGen.ManagedReturn
