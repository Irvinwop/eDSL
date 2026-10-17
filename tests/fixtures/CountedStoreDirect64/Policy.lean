/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CountedStoreDirect64.Raw
import EDSL.Grading.StoreReturnValue64.StackOnly

set_option warningAsError true

namespace EDSL.CountedStoreDirect64
open EDSL X86 X86.Sequential CountedStore64 Grading.Trace

/-- Actual continuing states of the two complete compiler windows. The
positive path reaches one store; the zero path retains the original RAM. -/
inductive Prefix (input : Input) (initial : State) : Variant → State → Prop where
  | entry (variant) : Prefix input initial variant initial
  | copy : Prefix input initial .clang (move initial)
  | ready (variant) : Prefix input initial variant (ready variant initial)
  | guard (variant) (af) : Prefix input initial variant (guard variant initial af)
  | store (variant) (af) (nonzero : input.count ≠ 0) :
      Prefix input initial variant (atStore variant initial af)
  | retZero (variant) (af) (zero : input.count = 0) :
      Prefix input initial variant (atRet variant initial af)
  | retPositive (variant) (af) (nonzero : input.count ≠ 0) :
      Prefix input initial variant (store (atStore variant initial af))

/-- Every permitted prefix fetches inside the actual complete byte window.
All successful operand reads use the original complete caller slot. -/
theorem stack_policy {variant input initial} (pre : Pre (bytes variant) input initial) :
    Grading.StoreReturnValue64.StackPolicy (bytes variant) input.toInput initial := by
  refine ⟨fun _ state => Prefix input initial variant state, Prefix.entry variant, ?_⟩
  intro _ before inside
  refine ⟨True.intro, ?_⟩
  cases inside with
  | entry variant =>
    refine ⟨entryInstruction variant, decode_entry pre.memory.code rfl, ?_⟩
    intro af
    cases variant with
    | gcc =>
      have actual := (step_eq_execute af (decode_entry pre.memory.code rfl)).trans
        (execute_lea initial af)
      exact ⟨⟨.next (ready .gcc initial),[]⟩,(),actual,by simp,
        ⟨fetch_entry pre.memory.code rfl,.readOnly rfl⟩,Prefix.ready .gcc⟩
    | clang =>
      have actual := (step_eq_execute af (decode_entry pre.memory.code rfl)).trans
        (execute_move initial af)
      exact ⟨⟨.next (move initial),[]⟩,(),actual,by simp,
        ⟨fetch_entry pre.memory.code rfl,.readOnly rfl⟩,Prefix.copy⟩
  | copy =>
    have frame := (Common.Frame.initial pre).move
    have decoded := decode_add frame.code rfl
    refine ⟨.addReg64 .rax .rdx,decoded,?_⟩
    intro af
    exact ⟨⟨.next (ready .clang initial),[]⟩,(),
      (step_eq_execute af decoded).trans (execute_add (move initial) af),by simp,
      ⟨fetch_add frame.code rfl,.readOnly rfl⟩,Prefix.ready .clang⟩
  | ready variant =>
    have frame := ready_frame pre
    refine ⟨instruction .test,decode frame.code .test (ready_pc variant initial),?_⟩
    intro af
    exact ⟨⟨.next (guard variant initial af),[]⟩,(),test_step pre af,by simp,
      ⟨fetch_at frame.code .test (ready_pc variant initial),.readOnly rfl⟩,
      Prefix.guard variant af⟩
  | guard variant prior =>
    have frame := guard_frame pre prior
    refine ⟨instruction .guard,decode frame.code .guard (guard_pc variant initial prior),?_⟩
    intro af
    have fetch := fetch_at frame.code .guard (guard_pc variant initial prior)
    by_cases zero : input.count = 0
    · exact ⟨⟨.next (atRet variant initial prior),[]⟩,(),guard_zero_step pre zero prior af,
        by simp,⟨fetch,.readOnly rfl⟩,Prefix.retZero variant prior zero⟩
    · exact ⟨⟨.next (atStore variant initial prior),[]⟩,(),guard_positive_step pre zero prior af,
        by simp,⟨fetch,.readOnly rfl⟩,Prefix.store variant prior zero⟩
  | store variant prior nonzero =>
    have frame := atStore_frame pre prior
    refine ⟨instruction .store,decode frame.code .store rfl,?_⟩
    intro af
    have intent : (instruction .store).storeIntent64 (atStore variant initial prior) =
        some (input.address,(atStore variant initial prior).registers .rax) := by
      rw [store_intent,frame.pointer pre]
    exact ⟨⟨.next (store (atStore variant initial prior)),[]⟩,(),store_step pre prior af,
      by simp,⟨fetch_at frame.code .store rfl,.store64 intent⟩,
      Prefix.retPositive variant prior nonzero⟩
  | retZero variant prior _ =>
    have frame := atRet_frame pre prior
    refine ⟨instruction .ret,decode frame.code .ret rfl,?_⟩
    intro af
    refine ⟨⟨.returned (finish (atRet variant initial prior) input.returnAddress),
      [⟨.stack,initial.registers .rsp,8⟩]⟩,(),ret_step pre frame rfl af,?_,
      ⟨fetch_at frame.code .ret rfl,.readOnly rfl⟩,True.intro⟩
    intro read member
    simp only [List.mem_singleton] at member
    subst read
    exact ⟨⟨rfl,rfl,rfl⟩,rfl,input.returnAddress,frame.stackRead⟩
  | retPositive variant prior _ =>
    have frame := stored_frame pre prior
    have pc := stored_pc variant initial prior
    refine ⟨instruction .ret,decode frame.code .ret pc,?_⟩
    intro af
    refine ⟨⟨.returned (finish (store (atStore variant initial prior)) input.returnAddress),
      [⟨.stack,initial.registers .rsp,8⟩]⟩,(),ret_step pre frame pc af,?_,
      ⟨fetch_at frame.code .ret pc,.readOnly rfl⟩,True.intro⟩
    intro read member
    simp only [List.mem_singleton] at member
    subst read
    exact ⟨⟨rfl,rfl,rfl⟩,rfl,input.returnAddress,frame.stackRead⟩

theorem raw_policy {variant input initial} (pre : Pre (bytes variant) input initial) :
    RawPolicy (bytes variant) input initial :=
  (stack_policy pre).raw

/-- Present current resources lift the same exact machine paths. Every store
is an actual checked mutation in the evolved world, derived from ownership. -/
theorem resource_policy {variant resource initial}
    (pre : ResourcePre (bytes variant) resource initial) : ResourcePolicy resource initial :=
  (stack_policy pre.machine).resources pre.memory

theorem resource_semantics {variant resource initial}
    (pre : ResourcePre (bytes variant) resource initial) :
    AllExecutions initial (fun result =>
      Post (resourceInput resource) initial result.state ∧ ResourceReturn resource initial result ∧
      result.instructions = cost variant resource.count ∧
      result.reads = [⟨.stack,initial.registers .rsp,8⟩]) ∧ ResourcePolicy resource initial := by
  have policy := resource_policy pre
  refine ⟨?_,policy⟩
  intro choices
  obtain ⟨result,actual,post,count,reads⟩ := raw_semantics pre.machine choices
  exact ⟨result,actual,post,
    Grading.StoreReturnValue64.ResourcePolicy.returned pre.memory policy,count,reads⟩

end EDSL.CountedStoreDirect64
