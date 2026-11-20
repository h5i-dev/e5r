/-
  Non-vacuity of the repaired Some-point interface (after the 3ecd81b audit), on the pinned RMK
  image.

  Original e5r code, Apache-2.0.

  PROVED here:
  * `someAt_real`: a concrete machine at the layout observed on QEMU virt (RynkService 0x8002a4c0 at
    [0x8002a780], RX Uart16550 0x8002a1c0 at [0x8002a784], TX 0x8002a1e4 at [0x8002a788] with base
    0x10000000 and stride 1, flag pointer 0x8002a7c9 at sp+0x24, sp = 0x80fffe10, s9 = msgA,
    s10 = 0x8002a7f0, a 3-byte message at bufA with a non-negative header) satisfies `SomeAt`, so the
    strengthened invariant is not empty;
  * `dispEnv_real`: the matching dispatch entry (the future as the caller builds it) satisfies the
    repaired `DispEnv`;
  * `svc_zero_not_someAt`, `svc_zero_not_dispEnv`: a service pointer word 0, the audit's
    counterexample to the 07a17e5 contracts, is now excluded by both.

  NOT shown: that `DispatchContract W` holds for any `W`, which `W` the real state satisfies, or
  that `SessInv` holds at the first loop entry (initialization).
-/
import Projects.rmk.Deframer.SomeRound

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.SomeW
open E5R E5R.Rmk E5R.Rmk.Deframer.Session E5R.Rmk.Deframer.SessionI E5R.Rmk.Deframer.SomeP

def memT (t : List (Nat × Nat)) (a : Word) : BitVec 8 :=
  match t.find? (fun p => p.1 == a.toNat) with
  | some p => BitVec.ofNat 8 p.2
  | none => 0

def mkCore (pc : Word) (rs : List (Nat × Word)) : Core where
  pc := pc
  x := fun r => match rs.find? (fun p => p.1 == r.val) with | some p => p.2 | none => 0
  mie_ := false
  mpie := false
  mpp := 3
  mieReg := 0
  mtvec := 0x800000f8
  mepc := 0
  mcause := 0
  mscratch := 0
  resv := false

theorem mkCore_quiet (pc : Word) (rs : List (Nat × Word)) : Quiet (mkCore pc rs) :=
  fun code => by simp [irqEnabled, mkCore]

/-- The observed session cells, and a message at msgA (data bufA, len 3, frame 3, header 0x0202). -/
def tR : List (Nat × Nat) :=
  [(0x8002a780, 0xc0), (0x8002a781, 0xa4), (0x8002a782, 0x02), (0x8002a783, 0x80),
   (0x8002a784, 0xc0), (0x8002a785, 0xa1), (0x8002a786, 0x02), (0x8002a787, 0x80),
   (0x8002a788, 0xe4), (0x8002a789, 0xa1), (0x8002a78a, 0x02), (0x8002a78b, 0x80),
   (0x8002a1df, 0x10), (0x8002a1e0, 1), (0x8002a203, 0x10), (0x8002a204, 1),
   (0x80fffe34, 0xc9), (0x80fffe35, 0xa7), (0x80fffe36, 0x02), (0x80fffe37, 0x80),
   (0x8002a580, 0x90), (0x8002a581, 0xa5), (0x8002a582, 0x02), (0x8002a583, 0x80),
   (0x8002a584, 3), (0x8002a58c, 3), (0x8002a588, 2), (0x8002a589, 2)]

def mR : Machine :=
  ⟨mkCore 0x80003e70 [(2, 0x80fffe10), (9, 0x8002a580), (22, s6v), (23, s7v), (26, 0x8002a7f0)], memT tR⟩

theorem extras_real : Extras mR := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, by decide, by decide, ?_, by decide,
    by decide, by decide, by decide, by decide, ⟨by decide, by decide⟩⟩
  · intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;>
      (refine ⟨?_, by decide⟩; unfold SW; decide)
  · intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> decide

/-- **The strengthened `SomeAt` is satisfiable** at the real layout. -/
theorem someAt_real : SomeAt mR :=
  ⟨rfl, mkCore_quiet _ _, by decide, by decide, by decide, by decide,
    ⟨by decide, by decide, by decide, by decide, by decide⟩,
    ⟨by unfold consumed word; decide, by unfold filled word; decide⟩, by decide, by decide, by decide,
    extras_real⟩

/-- The dispatch entry from `mR`: the future at 0x8002a7b0 (service word, sp+0x20 word, msgA), state 0. -/
def tD : List (Nat × Nat) :=
  tR ++ [(0x8002a7b0, 0xc0), (0x8002a7b1, 0xa4), (0x8002a7b2, 0x02), (0x8002a7b3, 0x80),
    (0x8002a7b8, 0x80), (0x8002a7b9, 0xa5), (0x8002a7ba, 0x02), (0x8002a7bb, 0x80)]

def mDR : Machine :=
  ⟨mkCore 0x800001f2 [(1, 0x80003e9e), (2, 0x80fffe10), (9, 0x8002a580), (10, 0x8002a7b0), (22, s6v), (23, s7v),
    (26, 0x8002a7f0)], memT tD⟩

/-- **The repaired `DispEnv` is satisfiable** at the real layout. -/
theorem dispEnv_real : DispEnv mDR :=
  ⟨rfl, mkCore_quiet _ _, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, ⟨by decide, by decide, by decide, by decide, by decide⟩,
    by decide⟩

/-- The audit's counterexample shape (service pointer word 0) is excluded by `SomeAt` ... -/
theorem svc_zero_not_someAt (m : Machine) (h0 : ramRead m.ram 0x8002a780 .w = 0) : ¬ SomeAt m :=
  fun h => absurd (h0.symm.trans h.ext.svc) (by decide)

/-- ... and by `DispEnv`. -/
theorem svc_zero_not_dispEnv (m : Machine) (h0 : ramRead m.ram 0x8002a780 .w = 0) : ¬ DispEnv m :=
  fun h => absurd (h0.symm.trans h.svc) (by decide)

end E5R.Rmk.Deframer.SomeW
