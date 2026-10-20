import EDSL.OS.Futex.Predicate.Model

namespace EDSL.OS.Futex.Predicate
open X86

theorem decode_at (client : Client) (point : Point) (context : Threads.Context) (memory : Memory)
    (rip : context.rip = client.entry.rip + BitVec.ofNat 64 point.offset)
    (code : CodeAt memory client.entry.rip bytes) :
    decodeAt (MachineThreads.contextState context memory) = .ok point.instruction := by
  cases point with
  | load =>
    have first := code.2 0 0x8b (by decide)
    have second := code.2 1 0x07 (by decide)
    simp only [BitVec.add_zero] at first
    simp [Point.offset, Point.instruction, MachineThreads.contextState, rip, decodeAt, first, second]
  | compare observed =>
    have first := code.2 2 0x83 (by decide)
    have second := code.2 3 0xf8 (by decide)
    have third := code.2 4 0 (by decide)
    simp [Point.offset, Point.instruction, MachineThreads.contextState, rip, decodeAt,
      BitVec.add_assoc, first, second, third]
  | branch observed =>
    have first := code.2 5 0x75 (by decide)
    have second := code.2 6 0x16 (by decide)
    simp [Point.offset, Point.instruction, MachineThreads.contextState, rip, decodeAt,
      BitVec.add_assoc, first, second]
  | number =>
    have first := code.2 7 0xb8 (by decide)
    have second := code.2 8 0xca (by decide)
    have third := code.2 9 0 (by decide)
    have fourth := code.2 10 0 (by decide)
    have fifth := code.2 11 0 (by decide)
    simp [Point.offset, Point.instruction, MachineThreads.contextState, rip, decodeAt,
      BitVec.add_assoc, first, second, third, fourth, fifth, joinDWord]
  | operation =>
    have first := code.2 12 0xbe (by decide)
    have second := code.2 13 0x80 (by decide)
    have third := code.2 14 0 (by decide)
    have fourth := code.2 15 0 (by decide)
    have fifth := code.2 16 0 (by decide)
    simp [Point.offset, Point.instruction, MachineThreads.contextState, rip, decodeAt,
      BitVec.add_assoc, first, second, third, fourth, fifth, joinDWord]
  | syscall =>
    have first := code.2 17 0x0f (by decide)
    have second := code.2 18 0x05 (by decide)
    simp [Point.offset, Point.instruction, MachineThreads.contextState, rip, decodeAt,
      BitVec.add_assoc, first, second]
  | resumed raw =>
    have first := code.2 19 0xb8 (by decide)
    have second := code.2 20 1 (by decide)
    have third := code.2 21 0 (by decide)
    have fourth := code.2 22 0 (by decide)
    have fifth := code.2 23 0 (by decide)
    simp [Point.offset, Point.instruction, MachineThreads.contextState, rip, decodeAt,
      BitVec.add_assoc, first, second, third, fourth, fifth, joinDWord]
  | retryCompare =>
    have first := code.2 24 0x83 (by decide)
    have second := code.2 25 0xf8 (by decide)
    have third := code.2 26 0 (by decide)
    simp [Point.offset, Point.instruction, MachineThreads.contextState, rip, decodeAt,
      BitVec.add_assoc, first, second, third]
  | retryBranch =>
    have first := code.2 27 0x75 (by decide)
    have second := code.2 28 0xe3 (by decide)
    simp [Point.offset, Point.instruction, MachineThreads.contextState, rip, decodeAt,
      BitVec.add_assoc, first, second]
  | done observed =>
    have first := code.2 29 0xc3 (by decide)
    simp [Point.offset, Point.instruction, MachineThreads.contextState, rip, decodeAt, first]

theorem decode_point {client : Client} {point : Point} {context : Threads.Context} {memory : Memory}
    (current : Running client point context) (code : CodeAt memory client.entry.rip bytes) :
    decodeAt (MachineThreads.contextState context memory) = .ok point.instruction :=
  decode_at client point context memory current.rip code

theorem Point.no_store (point : Point) (context : Threads.Context) :
    TSO.pendingStore context point.instruction = none := by
  cases point <;> rfl

theorem Point.unlocked (point : Point) : TSO.locked point.instruction = false := by
  cases point <;> rfl

theorem Point.syscall_only {point : Point} (decoded : point.instruction = .syscall) :
    point = .syscall := by
  cases point <;> simp_all [Point.instruction]

end EDSL.OS.Futex.Predicate
