/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.FutexClientCertificate
import EDSL.Examples.FutexClient
import EDSL.Audit

namespace EDSL.Tests.FutexClientCertificate
open X86 OS OS.Futex OS.Futex.Clients
open Examples.FutexClient

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Independently assembled publication ABI, including the actual RET. -/
def candidate : List Byte :=
  [0xb8, 0x44, 0x33, 0x22, 0x11, 0x89, 0x06,
   0xb8, 1, 0, 0, 0, 0x87, 0x07,
   0xb8, 202, 0, 0, 0, 0xbe, 129, 0, 0, 0,
   0xba, 1, 0, 0, 0, 0x0f, 0x05, 0xc3]

-- This exercises the artifact-to-current-member binding in a nonempty owned
-- cohort, rather than pairing irrelevant equality with a runtime theorem.
theorem initial_certificate :
    EDSL.FutexClientCertificate.Specification candidate cohort initial 1 publisher := by
  apply EDSL.FutexClientCertificate.sound candidate (by decide) initial_admitted rfl rfl
  exact (initial_protection 1 publisher rfl).2.2.1

def physicalActions : List Runtime.Action := [.issue 1, .issue 1, .issue 1, .issue 1, .drain 1]

def physicalObservations : List Runtime.Observation :=
  [.physical (.machine (.retired 1 none)), .physical (.machine (.retired 1 none)),
   .physical (.machine (.retired 1 none)), .physical (.machine (.blocked 1)),
   .physical (.machine (.drained 1 ⟨262144, 0x11223344⟩))]

def physicalBeforeExchange : Suspend.State × List Suspend.Observation :=
  Examples.Futex.checked (Suspend.schedule initial.suspended
    [.issue 1, .issue 1, .issue 1, .issue 1, .drain 1]) (by rfl)

-- Only actual unadapted machine steps are supplied to this prefix lift. It
-- derives the successful managed prefix and retains the exact literal binding.
theorem physical_trace :
    MachineTrace initial.suspended physicalActions physicalObservations physicalBeforeExchange.1 := by
  apply MachineTrace.issue (by rfl)
  apply MachineTrace.issue (by rfl)
  apply MachineTrace.issue (by rfl)
  apply MachineTrace.issue (by rfl)
  apply MachineTrace.drain (by rfl)
  exact .nil

def exchanged : Suspend.State × Suspend.Observation :=
  Examples.Futex.checked (Suspend.issue physicalBeforeExchange.1 1) (by rfl)

-- The byte-bound member's actual XCHG establishes its own P and W, and its
-- managed success is a conclusion. No successful adapter schedule is supplied.
theorem exact_artifact_publishes :
    ∃ before after : Futex.State,
      Runtime.Trace cohort.profile initial physicalActions physicalObservations before ∧
      EDSL.FutexClientCertificate.Specification candidate cohort before 1 publisher ∧
      Physical.issue cohort.profile before 1 = .ok (after, .machine (.retired 1 (some ⟨65536, 0, 1⟩))) ∧
      after.suspended = exchanged.1 ∧
      loadDWord before.suspended.machine.memory 262144 = .ok 0x11223344 ∧
      loadDWord after.suspended.machine.memory 262144 = .ok 0x11223344 ∧
      loadDWord after.suspended.machine.memory 65536 = .ok 1 ∧ Admitted cohort after := by
  obtain ⟨before, lifted, physical, certificate⟩ := initial_certificate.lift_prefix physical_trace
  have actual : Suspend.issue before.suspended 1 =
      .ok (exchanged.1, .machine (.retired 1 (some ⟨65536, 0, 1⟩))) := by rw [physical]; rfl
  obtain ⟨_, _, beforePayload, after, issued, afterPhysical, afterPayload, word, afterAd⟩ :=
    certificate.publication exchanged.1 ⟨65536, 0, 1⟩ actual
  exact ⟨before, after, lifted, certificate, issued, afterPhysical, beforePayload, afterPayload, word, afterAd⟩

/-- A real prefix reaches an actual typed empty-WAKE result. Its own STORE
queues before XCHG, the first XCHG blocks, and an actual drain enables it.
The subsequent resume and RET are positive conclusions, not schedule premises. -/
def readyActions : List Runtime.Action :=
  [.issue 1, .issue 1, .issue 1, .issue 1, .drain 1,
   .issue 1, .issue 1, .issue 1, .issue 1, .issue 1,
   .service (.wake 0 none)]

def wakeReady : Futex.State × List Runtime.Observation :=
  Examples.Futex.checked (Runtime.schedule profile initial readyActions) (by rfl)

theorem ready_admitted : Admitted cohort wakeReady.1 :=
  initial_admitted.schedule (Examples.Futex.checked_ok _ _)

def wakeCall : Call := ⟨1, .wakeOne, 2, .ready .wakeZero .emptyWake⟩

theorem ready_certificate :
    EDSL.FutexClientCertificate.Specification candidate cohort wakeReady.1 1 publisher := by
  apply EDSL.FutexClientCertificate.sound candidate (by decide) ready_admitted rfl rfl
  exact (ready_admitted.protected 1 publisher rfl).2.2.1

-- A raw-zero WAKE completion must RET through the bound publisher's protected
-- target with full arbitrary clobbers and current published payload, without
-- altering any peer worker/pending slot. The kernel-ready call is actual.
theorem exact_client_ready_returns (flags rcx r11 : Word) :
    ∃ resumed after returned,
      resumeReady profile.service wakeReady.1 0 flags rcx r11 = .ok resumed ∧
      Physical.issue profile resumed 1 = .ok (after, .machine (.retired 1 none)) ∧
      after.suspended.machine.workers[1]? = some returned ∧
      returned.returned = true ∧ returned.context.registers .rax = 0 ∧
      returned.context.rip = 0x6100 ∧ returned.context.registers .rsp = 32808 ∧
      returned.context.flags = flags ∧ returned.context.registers .rcx = rcx ∧
      returned.context.registers .r11 = r11 ∧
      loadDWord after.suspended.machine.memory 262144 = .ok 0x11223344 ∧
      loadDWord after.suspended.machine.memory 65536 = .ok 1 ∧
      (∀ query, query ≠ 1 →
        after.suspended.machine.workers[query]? = wakeReady.1.suspended.machine.workers[query]? ∧
        after.suspended.pending query = wakeReady.1.suspended.pending query) ∧
      Admitted cohort resumed ∧ Admitted cohort after := by
  have found : wakeReady.1.calls 0 = some wakeCall := rfl
  obtain ⟨resumed, after, returned, resume, issue, live, done, empty, raw, target, stack,
    privateFlags, privateRcx, privateR11, memory, peers, resumedAd, afterAd⟩ :=
    ready_certificate.returns 0 wakeCall .wakeZero .emptyWake found rfl rfl flags rcx r11
  refine ⟨resumed, after, returned, resume, issue, live, done, raw, target, stack,
    privateFlags, privateRcx, privateR11, ?_, ?_, peers, resumedAd, afterAd⟩
  · rw [memory]; rfl
  · rw [memory]; rfl

-- These different same-length instructions violate independent destination,
-- count and protected continuation requirements. No mutant is executed.
example : EDSL.FutexClientCertificate.accepts (candidate.set 6 0x07) = false := by decide
example : EDSL.FutexClientCertificate.accepts (candidate.set 13 0x06) = false := by decide
example : EDSL.FutexClientCertificate.accepts (candidate.set 25 2) = false := by decide
example : EDSL.FutexClientCertificate.accepts (candidate.set 31 0x90) = false := by decide
example : EDSL.FutexClientCertificate.accepts (candidate.take 31) = false := by decide

-- The old WAKE-only invocation artifact cannot be certified as a complete
-- publishing client, although the original invocation profile still admits it.
example : EDSL.FutexClientCertificate.accepts Examples.FutexStubs.Profile.wakeOne.bytes = false := by decide

end EDSL.Tests.FutexClientCertificate

#audit_edsl
