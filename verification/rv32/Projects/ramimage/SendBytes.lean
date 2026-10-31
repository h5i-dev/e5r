/-
  RMK `Uart16550<MmioBackend>::send_bytes` (0x800098a6), main's proof (support-lean4 5bf94a2,
  `Projects/rmk/Uart/SendBytes.lean`), on the image the job runner generates
  (`jobs/rmk/rmk-uart-send-bytes.json`). Original e5r code, Apache-2.0.

  Main's statement has no callee contract: `send_bytes : SendEnv m₀ → Lands B img (SendPost m₀) m₀`.
  This wrapper:
  * restates it with its type written out;
  * pins `SendEnv` and `SendPost` field by field (`env_iff`, `post_iff`), so a weakened precondition or
    postcondition fails this job instead of being audited silently;
  * gives NON-VACUITY WITNESSES: concrete machines `w0` (len 0) and `w16` (a 16-byte RAM buffer) that
    satisfy `SendEnv`, checked by `decide`. So the theorem is not an implication from an unsatisfiable
    environment (the failure peer audit 3ecd81b found in 07a17e5's DispatchContract/EncodeContract).

  What `SendEnv` assumes, and who must establish it at the real call (0x800042f8 in the poll): the
  struct pointer a0 with base 0x10000000 at +0x1c and stride 1 at +0x20 (session `Extras` carries
  these for the struct at [0x8002a784]), the buffer in RAM, 0x50 bytes of stack, `Quiet`. Connecting
  the poll's send loop (0x8000429e) to this contract is NOT done here. `SessionSafe` is NOT proved.
-/
import Projects.ramimage.Deframer
import Projects.rmk.Uart.SendBytes

namespace E5R.RmkUart
open E5R E5R.Rmk.Deframer
open E5R.Rmk (Lands Quiet)
open E5R.Rmk.Uart (SendEnv SendPost)

theorem send_bytes (m₀ : Machine) (E : SendEnv m₀) : Lands B img (SendPost m₀) m₀ :=
  E5R.Rmk.Uart.send_bytes m₀ E

/-- `SendEnv`, every field. -/
theorem env_iff (m : Machine) : SendEnv m ↔
    (m.core.pc = 0x800098a6 ∧ Quiet m.core ∧ (m.core.get 1).getLsbD 0 = false ∧
      (m.core.get 2).toNat % 4 = 0 ∧
      (0x80029bc8 + 0x50 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat ≤ 0x81000000) ∧
      ramRead m.ram (m.core.get 10 + 0x0000001c#32) .w = 0x10000000 ∧
      (m.ram (m.core.get 10 + 0x00000020#32)).toNat = 1 ∧
      (m.core.get 10 + 0x0000001c#32).toNat % 4 = 0 ∧
      (0x80029bc8 ≤ (m.core.get 10).toNat ∧ (m.core.get 10).toNat + 0x21 ≤ 0x81000000) ∧
      ((m.core.get 10).toNat + 0x21 ≤ (m.core.get 2).toNat - 0x50 ∨ (m.core.get 2).toNat ≤ (m.core.get 10).toNat) ∧
      ((m.core.get 12).toNat = 0 ∨ B.inRam (m.core.get 11) (m.core.get 12).toNat = true)) :=
  ⟨fun E => ⟨E.pc, E.quiet, E.ra, E.spAl, E.sp, E.base, E.stride, E.selfAl, E.selfIn, E.selfSep, E.buf⟩,
   fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩⟩

/-- `SendPost`, every field: return to ra, quiet, ABI frame, RAM changed only in [sp-0x50, sp),
    count 0 or 1..min(len, 16). -/
theorem post_iff (m₀ m : Machine) : SendPost m₀ m ↔
    (m.core.pc = m₀.core.get 1 ∧ Quiet m.core ∧ m.core.get 2 = m₀.core.get 2 ∧
      (∀ r : Reg, r.val ∉ callerSaved → m.core.get r = m₀.core.get r) ∧
      (∀ x, ¬ ((m₀.core.get 2).toNat - 0x50 ≤ x.toNat ∧ x.toNat < (m₀.core.get 2).toNat) → m.ram x = m₀.ram x) ∧
      ((m.core.get 10).toNat = 0 ∨
        (1 ≤ (m.core.get 10).toNat ∧ (m.core.get 10).toNat ≤ (m₀.core.get 12).toNat ∧ (m.core.get 10).toNat ≤ 16))) :=
  ⟨fun P => ⟨P.pc, P.quiet, P.sp, P.saved, P.ram, P.count⟩,
   fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩⟩

/-! ## Non-vacuity: `SendEnv` is satisfiable -/

/-- A core with interrupts off and the given registers (others 0). -/
def wCore (rs : List (Nat × Word)) : Core where
  pc := 0x800098a6
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

/-- RAM: the struct at 0x80090000 with base 0x10000000 (+0x1c, little-endian) and stride 1 (+0x20). -/
def wRam (a : Word) : BitVec 8 :=
  if a = 0x8009001f then 0x10 else if a = 0x80090020 then 1 else 0

/-- ra 0x80004300, sp 0x80100000, a0 the struct, a1 0x80080000, a2 len. -/
def wm (len : Word) : Machine :=
  ⟨wCore [(1, 0x80004300), (2, 0x80100000), (10, 0x80090000), (11, 0x80080000), (12, len)], wRam⟩

theorem wQuiet (len : Word) : Quiet (wm len).core := fun code => by simp [irqEnabled, wm, wCore]

theorem w0 : SendEnv (wm 0) :=
  (env_iff _).2 ⟨rfl, wQuiet 0, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, .inl (by decide)⟩

theorem w16 : SendEnv (wm 16) :=
  (env_iff _).2 ⟨rfl, wQuiet 16, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, .inr (by decide)⟩

/-- So the theorem has content: on `w16`, every behaviour returns to 0x80004300 having sent at most
    16 bytes, with the struct and the buffer unchanged. -/
theorem w16_lands : Lands B img (SendPost (wm 16)) (wm 16) := send_bytes _ w16

end E5R.RmkUart
