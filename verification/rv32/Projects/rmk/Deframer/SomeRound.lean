/-
  The session's Some path after `RynkService::dispatch`, on the pinned RMK image, against two
  NAMED callee contracts that are NOT proved here or anywhere: `DispatchContract` (the dispatch
  closure 0x800001f2, polled at 0x80003e9a) and `EncodeContract` (`encode_frame` 0x80008d5c, called
  at 0x80003f1a). Every theorem that uses them takes them as hypotheses `hD` / `hE`.

  Original e5r code, Apache-2.0.

  AUDIT CAVEAT (peer, 3ecd81b, review/SomeAudit.lean on 07a17e5): the 07a17e5 statements of both
  contracts are FALSE (kernel-checked counterexample runs), so `some_round` as stated there was
  vacuous. Repaired here: `DispEnv` now fixes the RynkService pointer, s9 = msgA, the message and
  the header (the dispatch counterexample had service pointer 0), and `DispatchContract W` takes an
  explicit world predicate `W` for what dispatch dereferences (open). `EncEnv` is NOT repaired yet:
  its refutation (the `Kept` UART bytes may alias the output buffer) still applies, so `some_round`
  remains vacuous until the repaired `EncEnv` agreed with the peer (rmk/some-interfaces.md) lands.
  Non-vacuity of the repaired `SomeAt` / `DispEnv`: Deframer/SomeWitness.lean.

  Both contracts are `Lands` statements (every behaviour of the callee, any device values and any
  events, returns), with the ABI frame (sp and the callee-saved registers), `Quiet` on return, and a
  RAM frame stated as what the callee leaves alone: `Kept`, the session cells the caller reads
  afterwards (0x8002a780..0x8002a7a8: the service and UART struct pointers, the deframer, the parked
  count; the flag pointer word at sp+0x24; the Uart16550 struct's base and stride bytes).
  `EncodeContract` also gives the result: tag byte at sp+0x40 is 1, or 0 with length (sp+0x44) ≤ 7,
  the capacity of the 7-byte frame buffer at 0x8002a7b1 that the caller passes.

  PROVED here (conditional on `hD : DispatchContract W`, `hE` and `WAt W m₀`):
  * `some_pos`: from `SomeAt` with a non-negative header, every behaviour reaches one of
    * the loop head 0x80003e1a with `SessInv`: the empty response (encode_frame's error, or length 0)
      sets the flag byte [s10] and goes to the unpark site, then `unpark_round`;
    * 0x80004204: dispatch's poll returned 0xfe (Pending); the task poll sets a0 = 3 and jumps to
      its exit 0x800043b8, back to the EXECUTOR. A boundary, not proved;
    * 0x80003fa6: dispatch returned 0xff; that path calls 0x8001c3fc and 0x80003328. Not proved;
    * 0x8000429e: a non-empty response; the UART send loop (calls at 0x800042f8 -> 0x800098a6 and
      0x80004320 -> 0x8001e14a, and yields). Not proved.
    The slice check after encode_frame (panic 0x80004210) is shown not taken.
  * `some_round`: the same for every header (the negative one by `some_neg`).

  The poll's own writes on this path (`PW`) are inside `SessionI.SW`, which was widened for it
  (0x8002a7b0..0x8002a7f4 and sp+0x140..sp+0x148), and `Extras.spTop` now covers sp+0x148.

  s10 = 0x8002a7f0 (the flag byte address, x26 = s6+0x333, set at 0x80003b38 before the loop) comes
  from `Extras.s10`, which every proved step keeps (x26 is callee-saved and no segment writes it).
  Whether it holds when the task first reaches the loop head is part of the open initialization.
-/
import Projects.rmk.Deframer.SomePath

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.SomeP
open E5R E5R.Rmk E5R.Rmk.Deframer.Tail E5R.Rmk.Deframer.Session E5R.Rmk.Deframer.SessionI

/-! ## The two callee contracts (NOT proved) -/

/-- The session cells a callee must leave alone, at its entry state. -/
def Kept (m₀ : Machine) (x : Word) : Prop :=
  (0x8002a780 ≤ x.toNat ∧ x.toNat < 0x8002a7a8) ∨
  ((m₀.core.get 2).toNat + 0x24 ≤ x.toNat ∧ x.toNat < (m₀.core.get 2).toNat + 0x28) ∨
  (∃ k < 5, x = ramRead m₀.ram uPtr .w + 0x0000001c#32 + BitVec.ofNat 32 k) ∨
  (0x8002a200 ≤ x.toNat ∧ x.toNat < 0x8002a205)

/-- A callee's return: at `ret`, quiet, the ABI frame, `Kept` unchanged. -/
structure CallPost (ret : Word) (m₀ m : Machine) : Prop where
  pc : m.core.pc = ret
  quiet : Quiet m.core
  sp : m.core.get 2 = m₀.core.get 2
  saved : ∀ r : Reg, r.val ∉ callerSaved → m.core.get r = m₀.core.get r
  kept : ∀ x, Kept m₀ x → m.ram x = m₀.ram x

/-- The poll of the dispatch future at 0x80003e9a, as the caller sets it up. -/
structure DispEnv (m : Machine) : Prop where
  pc : m.core.pc = 0x800001f2
  quiet : Quiet m.core
  ra : m.core.get 1 = 0x80003e9e
  fut : m.core.get 10 = 0x8002a7b0
  s6 : m.core.get 22 = s6v
  s7 : m.core.get 23 = s7v
  spAl : (m.core.get 2).toNat % 4 = 0
  sp : 0x8002a798 + 0x70 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat + 0x148 ≤ 0x81000000
  /-- the future: unresumed (state byte 0), its three captured words -/
  futState : m.ram 0x8002a7bc = 0
  futSvc : ramRead m.ram 0x8002a7b0 .w = ramRead m.ram 0x8002a780 .w
  futArg : ramRead m.ram 0x8002a7b4 .w = ramRead m.ram (m.core.get 2 + 0x00000020#32) .w
  futMsg : ramRead m.ram 0x8002a7b8 .w = m.core.get 9
  /-- (repair after the 3ecd81b audit) the RynkService pointer, the message pointer, the message as
      recv_step leaves it, and the non-negative header that selected this path -/
  svc : ramRead m.ram 0x8002a780 .w = 0x8002a4c0
  s9 : m.core.get 9 = msgA
  msg : ramRead m.ram msgA .w = bufA ∧
    3 ≤ (ramRead m.ram (msgA + 4) .w).toNat ∧ (ramRead m.ram (msgA + 4) .w).toNat ≤ bufLen ∧
    2 < (ramRead m.ram (msgA + 0xc) .w).toNat ∧ (ramRead m.ram (msgA + 0xc) .w).toNat ≤ bufLen
  hdr : (m.ram 0x8002a589).toNat < 0x80

/-- NOT PROVED: polling `RynkService::dispatch`'s future returns, whatever it does, from `DispEnv`
and `W`. `W` is an explicit world predicate on RAM for everything dispatch dereferences beyond the
cells `DispEnv` fixes (the service struct at 0x8002a4c0 and what it points to: keymap, the
executor-stack object, .rodata tables). Which `W` makes this true is OPEN; no `W` is assumed here. -/
def DispatchContract (W : (Word → BitVec 8) → Prop) : Prop :=
  ∀ m₀, DispEnv m₀ → W m₀.ram → Lands B img (CallPost 0x80003e9e m₀) m₀

/-- The call of `encode_frame` at 0x80003f1a: out = sp+0x40, the 7-byte buffer 0x8002a7b1, and the
    response byte at sp+0x140. -/
structure EncEnv (m : Machine) : Prop where
  pc : m.core.pc = 0x80008d5c
  quiet : Quiet m.core
  ra : m.core.get 1 = 0x80003f1e
  out : m.core.get 10 = m.core.get 2 + 0x00000040#32
  buf : m.core.get 11 = 0x8002a7b1
  cap : m.core.get 12 = 7
  arg : m.core.get 15 = m.core.get 2 + 0x00000140#32
  spAl : (m.core.get 2).toNat % 4 = 0
  sp : 0x8002a798 + 0x70 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat + 0x148 ≤ 0x81000000

/-- encode_frame's result: error (tag 1), or a length within the buffer. -/
def EncRes (m₀ m : Machine) : Prop :=
  (m.ram (m₀.core.get 2 + 0x00000040#32)).toNat = 1 ∨
    ((m.ram (m₀.core.get 2 + 0x00000040#32)).toNat = 0 ∧
      (ramRead m.ram (m₀.core.get 2 + 0x00000044#32) .w).toNat ≤ 7)

/-- NOT PROVED: `encode_frame` returns, with `EncRes`. -/
def EncodeContract : Prop :=
  ∀ m₀, EncEnv m₀ → Lands B img (fun m => CallPost 0x80003f1e m₀ m ∧ EncRes m₀ m) m₀

/-- Where the Some path stops. -/
def SomeQ (m : Machine) : Prop :=
  (m.core.pc = 0x80003e1a ∧ SessInv m) ∨ m.core.pc = 0x80004204 ∨ m.core.pc = 0x80003fa6 ∨
    m.core.pc = 0x8000429e

/-! ## Helpers -/

theorem pos_h (x y : BitVec 8) (h : y.toNat < 0x80) :
    taken .lt (extend .h true (BitVec.ofNat 32 (x.toNat + 256 * y.toNat))) 0 = false := by
  have hx := x.isLt
  have hm : ((BitVec.ofNat 32 (x.toNat + 256 * y.toNat)).setWidth 16).msb = false := by
    rw [← Bool.not_eq_true, BitVec.msb_eq_true_iff_two_mul_ge]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  simp only [taken, extend]
  generalize (BitVec.ofNat 32 (x.toNat + 256 * y.toNat)).setWidth 16 = z at hm
  rw [Bool.eq_false_iff, ne_eq, BitVec.slt_iff_toInt_lt, BitVec.toInt_signExtend_of_le (by decide)]
  rw [BitVec.toInt_eq_msb_cond, hm]
  simp

theorem wr_other (M : Word → BitVec 8) (a v x : Word) (wd : Width) (ha : a.toNat + 4 ≤ 2 ^ 32)
    (h : x.toNat < a.toNat ∨ a.toNat + 4 ≤ x.toNat) : ramWrite M a v wd x = M x := by
  have n0 : x ≠ a := fun e => by subst e; omega
  have n1 : x ≠ a + 1 := fun e => by
    have := congrArg BitVec.toNat e; rw [BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl] at this; omega
  cases wd with
  | w => exact wr_byte_other M a v x ha h
  | b => simp [ramWrite, ramPut, n0]
  | h => simp [ramWrite, ramPut, n0]; intro e; exact absurd e n1

theorem slice_ok (t : BitVec 8) (len : Word) (h : t.toNat = 1 ∨ (t.toNat = 0 ∧ len.toNat ≤ 7)) :
    taken .ltu 7 (alu .and len (alu .add (extend .b false (BitVec.ofNat 32 t.toNat)) 0xffffffff#32)) = false := by
  rcases h with h | ⟨h, hl⟩
  · rw [h]; simp only [taken, alu, extend]
    show (7#32).ult (len &&& ((1#32 &&& 0xff#32) + 0xffffffff#32)) = false
    rw [show ((1#32 &&& 0xff#32) + 0xffffffff#32 : Word) = 0#32 by decide]; simp [BitVec.ult]
  · rw [h]; simp only [taken, alu, extend]
    show (7#32).ult (len &&& ((0#32 &&& 0xff#32) + 0xffffffff#32)) = false
    rw [show ((0#32 &&& 0xff#32) + 0xffffffff#32 : Word) = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp only [BitVec.ult, decide_eq_false_iff_not]; show ¬ 7 < len.toNat; omega

theorem spIn (sp : Word) (o n : Nat) (h1 : 0x80029bc8 ≤ sp.toNat) (h2 : sp.toNat + o + n ≤ 0x81000000) :
    B.inRam (sp + BitVec.ofNat 32 o) n = true :=
  (E5R.Rmk.B_ram _ _).mpr (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

theorem spOff (sp : Word) (o : Nat) (h : sp.toNat + o < 2 ^ 32) :
    (sp + BitVec.ofNat 32 o).toNat = sp.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- What the poll's own Some-path segments write. -/
def PW (sp x : Word) : Prop :=
  (0x8002a7a8 ≤ x.toNat ∧ x.toNat < 0x8002a7f4) ∨ (sp.toNat + 0x140 ≤ x.toNat ∧ x.toNat < sp.toNat + 0x148)

theorem wr_pw (sp x : Word) (hx : ¬ PW sp x) (M : Word → BitVec 8) (a v : Word) (wd : Width)
    (hw : (0x8002a7a8 ≤ a.toNat ∧ a.toNat + 4 ≤ 0x8002a7f4) ∨
      (sp.toNat + 0x140 ≤ a.toNat ∧ a.toNat + 4 ≤ sp.toNat + 0x148)) (ha : a.toNat + 4 ≤ 2 ^ 32) :
    ramWrite M a v wd x = M x := by
  apply wr_other _ _ _ _ _ ha
  unfold PW at hx
  omega

/-- `W` at the Some point, robust to the poll's own writes before the call (`PW`). -/
def WAt (W : (Word → BitVec 8) → Prop) (m₀ : Machine) : Prop :=
  ∀ M : Word → BitVec 8, (∀ x, ¬ PW (m₀.core.get 2) x → M x = m₀.ram x) → W M

/-- The state carried along the Some path, relative to the Some point `m₀`. -/
structure Ctx (m₀ m : Machine) : Prop where
  quiet : Quiet m.core
  sp : m.core.get 2 = m₀.core.get 2
  s6 : m.core.get 22 = s6v
  s7 : m.core.get 23 = s7v
  s10 : m.core.get 26 = 0x8002a7f0
  kept : ∀ x, Kept m₀ x → m.ram x = m₀.ram x

theorem kept_uPtr (m₀ m : Machine) (h : ∀ x, Kept m₀ x → m.ram x = m₀.ram x) :
    ramRead m.ram uPtr .w = ramRead m₀.ram uPtr .w := by
  refine ramRead_w_congr _ fun k hk => h _ (.inl ?_)
  rw [spOff _ _ (by rw [show uPtr.toNat = 0x8002a784 from rfl]; omega), show uPtr.toNat = 0x8002a784 from rfl]
  omega

theorem kept_mono (m₀ m : Machine) (c : Ctx m₀ m) (x : Word) (hx : Kept m₀ x) : Kept m x := by
  unfold Kept at hx ⊢
  rw [c.sp, kept_uPtr m₀ m c.kept]; exact hx

theorem kept_pw (m₀ : Machine) (h : SomeAt m₀) (x : Word) (hx : Kept m₀ x) : ¬ PW (m₀.core.get 2) x := by
  have h1 := h.sp
  have h2 := h.ext.spTop
  rcases hx with hx | hx | ⟨k, hk, rfl⟩ | hx
  · unfold PW; omega
  · unfold PW; omega
  · intro hp; apply (h.ext.uSep k hk).1; unfold PW at hp; unfold SW; omega
  · unfold PW; omega

theorem ctx_call (m₀ m m' : Machine) {ret : Word} (c : Ctx m₀ m) (p : CallPost ret m m') : Ctx m₀ m' :=
  ⟨p.quiet, p.sp.trans c.sp, (p.saved 22 (by decide)).trans c.s6, (p.saved 23 (by decide)).trans c.s7,
    (p.saved 26 (by decide)).trans c.s10,
    fun x hx => (p.kept x (kept_mono m₀ m c x hx)).trans (c.kept x hx)⟩

theorem ctx_seg (m₀ : Machine) (h : SomeAt m₀) (e e' : Core) (M R : Word → BitVec 8) (c : Ctx m₀ ⟨e, M⟩)
    (hq : Quiet e') (g2 : e'.get 2 = e.get 2) (g22 : e'.get 22 = e.get 22) (g23 : e'.get 23 = e.get 23)
    (g26 : e'.get 26 = e.get 26) (hR : ∀ x, ¬ PW (m₀.core.get 2) x → R x = M x) : Ctx m₀ ⟨e', R⟩ :=
  ⟨hq, g2.trans c.sp, g22.trans c.s6, g23.trans c.s7, g26.trans c.s10,
    fun x hx => (hR x (kept_pw m₀ h x hx)).trans (c.kept x hx)⟩

/-- `Extras` from the kept cells. -/
theorem extras_ctx (m₀ x : Machine) (h : SomeAt m₀) (c : Ctx m₀ x) : Extras x := by
  have E := h.ext
  have h1 := h.sp
  have h2 := E.spTop
  have hk := c.kept
  have hU : ramRead x.ram uPtr .w = ramRead m₀.ram uPtr .w := kept_uPtr m₀ x hk
  have hF : ramRead x.ram (x.core.get 2 + 0x00000024#32) .w = ramRead m₀.ram (m₀.core.get 2 + 0x00000024#32) .w := by
    rw [c.sp]
    refine ramRead_w_congr _ fun k hk' => hk _ (.inr (.inl ?_))
    rw [spOff _ _ (by rw [spOff _ _ (by omega)]; omega), spOff _ _ (by omega)]; omega
  have st : ∀ k < 5, x.ram (ramRead m₀.ram uPtr .w + 0x0000001c#32 + BitVec.ofNat 32 k) =
      m₀.ram (ramRead m₀.ram uPtr .w + 0x0000001c#32 + BitVec.ofNat 32 k) :=
    fun k hk' => hk _ (.inr (.inr (.inl ⟨k, hk', rfl⟩)))
  have s20 : ramRead m₀.ram uPtr .w + 0x00000020#32 = ramRead m₀.ram uPtr .w + 0x0000001c#32 + BitVec.ofNat 32 4 := by
    rw [BitVec.add_assoc]; rfl
  refine ⟨by rw [c.sp]; exact E.spTop, ?_, by rw [hU]; exact E.uBaseIn, ?_, by rw [hU]; exact E.uStrideIn,
    by rw [hU, hF, c.sp]; exact E.uSep, by rw [hF]; exact E.flagIn, by rw [hF]; exact E.flagSep,
    by rw [hF, c.sp]; exact E.flagNot, c.s10, ?_, ?_, ?_, ?_, by rw [hF]; exact E.fixNot⟩
  · rw [hU, ← E.uBase]; exact ramRead_w_congr _ fun k hk' => st k (by omega)
  · rw [hU, s20, st 4 (by decide), ← s20]; exact E.uStride
  · rw [← E.svc]; refine ramRead_w_congr _ fun k hk' => hk _ (.inl ?_)
    bv_omega
  · rw [← E.tx]; refine ramRead_w_congr _ fun k hk' => hk _ (.inl ?_)
    bv_omega
  · rw [← E.txBase]; refine ramRead_w_congr _ fun k hk' => hk _ (.inr (.inr (.inr ?_)))
    bv_omega
  · rw [hk _ (.inr (.inr (.inr (by decide))))]; exact E.txStride

/-! ## After encode_frame -/

theorem post_enc (m₀ : Machine) (h : SomeAt m₀) (m : Machine) (c : Ctx m₀ m) (hpc : m.core.pc = 0x80003f1e)
    (h9 : m.core.get 9 = 7)
    (hres : (m.ram (m₀.core.get 2 + 0x00000040#32)).toNat = 1 ∨
      ((m.ram (m₀.core.get 2 + 0x00000040#32)).toNat = 0 ∧
        (ramRead m.ram (m₀.core.get 2 + 0x00000044#32) .w).toNat ≤ 7)) :
    Lands B img SomeQ m := by
  obtain ⟨e, M⟩ := m
  have h1 : 0x8002a798 + 0x70 ≤ (m₀.core.get 2).toNat ∧ (m₀.core.get 2).toNat ≤ 0x81000000 := h.sp
  have h2 : (m₀.core.get 2).toNat + 0x148 ≤ 0x81000000 := h.ext.spTop
  have spA : (m₀.core.get 2).toNat % 4 = 0 := h.spAl
  have e2 : e.get 2 = m₀.core.get 2 := c.sp
  have e22 : e.get 22 = s6v := c.s6
  have hq : Quiet e := c.quiet
  have hpc' : e.pc = 0x80003f1e := hpc
  have a40 : (e.get 2 + 0x00000040#32).toNat % 1 = 0 := by omega
  have i40 : B.inRam (e.get 2 + 0x00000040#32) 1 = true := by rw [e2]; exact spIn _ _ _ (by omega) (by omega)
  have a44 : (e.get 2 + 0x00000044#32).toNat % 4 = 0 := by rw [e2, spOff _ _ (by omega)]; omega
  have i44 : B.inRam (e.get 2 + 0x00000044#32) 4 = true := by rw [e2]; exact spIn _ _ _ (by omega) (by omega)
  have w28 : taken .ltu (e.get 9) (alu .and (ramRead M (e.get 2 + 0x00000044#32) .w)
      (alu .add (extend .b false (ramRead M (e.get 2 + 0x00000040#32) .b)) 0xffffffff#32)) = false := by
    rw [h9, e2]; exact slice_ok _ _ hres
  -- the slice check, then the send state
  have r1 := sPost e M hpc' hq a40 i40 a44 i44 w28
  let P := sPostCore e M
  have csP : P.sameCsr e := by unfold P sPostCore; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_))
  have gP : ∀ r : Reg, r ≠ 10 → r ≠ 11 → P.get r = e.get r := fun r a b => by
    simp [P, sPostCore, Core.wr_get_ne, a, b]
  have qP : Quiet P := Quiet.of_sameCsr csP hq
  have p22 : P.get 22 = s6v := (gP 22 (by decide) (by decide)).trans e22
  have r2 := sState P M rfl qP (by rw [p22]; decide) (by rw [p22]; decide)
      (by rw [p22]; decide) (by rw [p22]; decide) (by rw [p22]; decide) (by rw [p22]; decide)
      (by rw [p22]; decide) (by rw [p22]; decide) (by rw [p22]; decide) (by rw [p22]; decide)
      (by rw [p22]; decide) (by rw [p22]; decide) (by rw [p22]; decide) (by rw [p22]; decide)
      (by rw [p22]; decide) (by rw [p22]; decide)
  let S := sStateCore P M
  let RS := sStateRam P M
  have csS : S.sameCsr P := by unfold S sStateCore; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_))
  have gS : ∀ r : Reg, r ≠ 10 → S.get r = P.get r := fun r a => by
    simp [S, sStateCore, Core.wr_get_ne, a]
  have qS : Quiet S := Quiet.of_sameCsr csS qP
  have CP : Ctx m₀ ⟨P, M⟩ := ctx_seg m₀ h e P M M c qP (gP 2 (by decide) (by decide))
      (gP 22 (by decide) (by decide)) (gP 23 (by decide) (by decide)) (gP 26 (by decide) (by decide))
      fun _ _ => rfl
  have hRS : ∀ x, ¬ PW (m₀.core.get 2) x → RS x = M x := by
    intro x hx
    simp only [RS, sStateRam, p22]
    simp (disch := (simp only [s6v]; bv_omega)) only [wr_pw (m₀.core.get 2) x hx]
  have CS : Ctx m₀ ⟨S, RS⟩ := ctx_seg m₀ h P S M RS CP qS (gS 2 (by decide)) (gS 22 (by decide))
    (gS 23 (by decide)) (gS 26 (by decide)) hRS
  have s26 : S.get 26 = 0x8002a7f0 := CS.s10
  cases hs : taken .ne (S.get 11) 0 with
  | true =>
    have r3 := sSend S RS rfl qS hs
    exact lands_of_qrun (r1.trans (r2.trans r3)) (.inr (.inr (.inr rfl)))
  | false =>
    have r3 := sEmpty S RS rfl qS hs (by rw [s26]; decide) (by rw [s26]; decide)
    let K := sEmptyCore S RS
    let R := sEmptyRam S RS
    have csK : K.sameCsr S := by unfold K sEmptyCore; (repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_))
    have gK : ∀ r : Reg, r ≠ 10 → K.get r = S.get r := fun r a => by
      simp [K, sEmptyCore, Core.wr_get_ne, a]
    have hR : ∀ x, ¬ PW (m₀.core.get 2) x → R x = RS x := by
      intro x hx
      simp only [R, sEmptyRam, s26]
      exact wr_pw _ x hx _ _ _ _ (.inl (by decide)) (by decide)
    have C : Ctx m₀ ⟨K, R⟩ := ctx_seg m₀ h S K RS R CS (Quiet.of_sameCsr csK qS) (gK 2 (by decide))
      (gK 22 (by decide)) (gK 23 (by decide)) (gK 26 (by decide)) hR
    have kd : ∀ x : Word, 0x8002a780 ≤ x.toNat → x.toNat < 0x8002a7a8 → R x = m₀.ram x :=
      fun x a b => C.kept x (.inl ⟨a, b⟩)
    have UA : UnparkAt ⟨K, R⟩ := by
      refine ⟨rfl, C.quiet, C.s6, C.s7, by show (K.get 2).toNat % 4 = 0; rw [C.sp]; exact spA,
        by show _ ∧ _; rw [C.sp]; exact h.sp, ?_, ?_⟩
      · show (ramRead R 0x8002a798 .w).toNat ≤ bufLen
        rw [rd_congr (ram := m₀.ram) (0x8002a798 : Word) (by decide) fun x a b => kd x
          (by rw [show (0x8002a798 : Word).toNat = 0x8002a798 from rfl] at a; omega)
          (by rw [show (0x8002a798 : Word).toNat = 0x8002a798 from rfl] at b; omega)]
        have := h.parked; omega
      · show (R (dfr + 8)).toNat ≤ 1
        rw [kd _ (by decide) (by decide)]; exact h.disc
    obtain ⟨k, m', r4, hpc2, hI⟩ := unpark_round ⟨K, R⟩ UA (extras_ctx m₀ ⟨K, R⟩ h C)
    exact lands_of_qrun_lands (r1.trans (r2.trans r3)) (lands_of_qrun r4 (.inl ⟨hpc2, hI⟩))

/-! ## After dispatch

Segment results are generalized to fresh variables right after their facts are read off, so no
later step unfolds them. -/

/-- From the frame-buffer set-up 0x80003ee0: encode_frame's call, then `post_enc`. -/
theorem enc_tail (hE : EncodeContract) (m₀ : Machine) (h : SomeAt m₀) (X : Core) (RX : Word → BitVec 8)
    (xpc : X.pc = 0x80003ee0) (CX : Ctx m₀ ⟨X, RX⟩) : Lands B img SomeQ ⟨X, RX⟩ := by
  have h1 : 0x8002a798 + 0x70 ≤ (m₀.core.get 2).toNat ∧ (m₀.core.get 2).toNat ≤ 0x81000000 := h.sp
  have h2 : (m₀.core.get 2).toNat + 0x148 ≤ 0x81000000 := h.ext.spTop
  have spA : (m₀.core.get 2).toNat % 4 = 0 := h.spAl
  have x23 : X.get 23 = s7v := CX.s7
  have r1 := sEnc1 X RX xpc CX.quiet (by rw [x23]; decide) (by rw [x23]; decide)
    (by rw [CX.s6]; decide) (by rw [CX.s6]; decide) (by rw [CX.s6]; decide) (by rw [CX.s6]; decide)
  have cs1 := sEnc1Csr X RX
  have p1 : (sEnc1Core X RX).pc = 0x80003ef0 := rfl
  have gY : ∀ r : Reg, r ≠ 8 → r ≠ 13 → r ≠ 14 → (sEnc1Core X RX).get r = X.get r := fun r a b d => by
    simp [sEnc1Core, Core.wr_get_ne, a, b, d]
  have y8 : (sEnc1Core X RX).get 8 = 0x8002a7b1 := by
    simp [sEnc1Core, Core.wr_get_ne, Core.wr_get_self, alu_add, x23]; rfl
  have hRY : ∀ x, ¬ PW (m₀.core.get 2) x → sEnc1Ram X RX x = RX x := by
    intro x hx
    simp only [sEnc1Ram, x23]
    exact wr_pw _ x hx _ _ _ _ (.inl (by decide)) (by decide)
  generalize sEnc1Core X RX = Y at r1 cs1 p1 gY y8
  generalize sEnc1Ram X RX = RY at r1 hRY
  have CY : Ctx m₀ ⟨Y, RY⟩ := ctx_seg m₀ h X Y RX RY CX (Quiet.of_sameCsr cs1 CX.quiet)
    (gY 2 (by decide) (by decide) (by decide)) (gY 22 (by decide) (by decide) (by decide))
    (gY 23 (by decide) (by decide) (by decide)) (gY 26 (by decide) (by decide) (by decide)) hRY
  have y2 : Y.get 2 = m₀.core.get 2 := CY.sp
  have r2 := sEnc2 Y RY p1 CY.quiet (by rw [y8]; decide) (by rw [y8]; decide) (by rw [y8]; decide)
    (by rw [y8]; decide) (by rw [y8]; decide) (by rw [y8]; decide) (by rw [y8]; decide)
    (by rw [y8]; decide) (by rw [y8]; decide) (by rw [y8]; decide) (by rw [y8]; decide)
    (by rw [y8]; decide) (by omega) (by rw [y2]; exact spIn _ _ _ (by omega) (by omega))
  have cs2 := sEnc2Csr Y RY
  have p2 : (sEnc2Core Y RY).pc = 0x80008d5c := rfl
  have gZ : ∀ r : Reg, r ≠ 1 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 15 → (sEnc2Core Y RY).get r = Y.get r :=
    fun r a b d f g i => by simp [sEnc2Core, Core.wr_get_ne, a, b, d, f, g, i]
  have z1 : (sEnc2Core Y RY).get 1 = 0x80003f1e := by simp [sEnc2Core, Core.wr_get_self]
  have z9 : (sEnc2Core Y RY).get 9 = 7 := by simp [sEnc2Core, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have z10 : (sEnc2Core Y RY).get 10 = Y.get 2 + 0x00000040#32 := by
    simp [sEnc2Core, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have z11 : (sEnc2Core Y RY).get 11 = 0x8002a7b1 := by
    simp [sEnc2Core, Core.wr_get_ne, Core.wr_get_self, alu_add, y8]
  have z12 : (sEnc2Core Y RY).get 12 = 7 := by
    simp [sEnc2Core, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have z15 : (sEnc2Core Y RY).get 15 = Y.get 2 + 0x00000140#32 := by
    simp [sEnc2Core, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have hRZ : ∀ x, ¬ PW (m₀.core.get 2) x → sEnc2Ram Y RY x = RY x := by
    intro x hx
    simp only [sEnc2Ram, y8, y2]
    simp (disch := (first | bv_omega | (simp only [s6v, s7v]; bv_omega))) only [wr_pw (m₀.core.get 2) x hx]
  generalize sEnc2Core Y RY = Z at r2 cs2 p2 gZ z1 z9 z10 z11 z12 z15
  generalize sEnc2Ram Y RY = RZ at r2 hRZ
  have CZ : Ctx m₀ ⟨Z, RZ⟩ := ctx_seg m₀ h Y Z RY RZ CY (Quiet.of_sameCsr cs2 CY.quiet)
    (gZ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (gZ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (gZ 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (gZ 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hRZ
  have z2 : Z.get 2 = Y.get 2 := gZ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have env : EncEnv ⟨Z, RZ⟩ := ⟨p2, CZ.quiet, z1, by show Z.get 10 = Z.get 2 + _; rw [z10, z2], z11, z12,
    by show Z.get 15 = Z.get 2 + _; rw [z15, z2], by show (Z.get 2).toNat % 4 = 0; rw [CZ.sp]; exact spA,
    by show _ ∧ _; rw [CZ.sp]; exact ⟨h1.1, h2⟩⟩
  refine lands_of_qrun_lands (r1.trans r2) (lands_seq ?_ (hE _ env))
  rintro m' ⟨P, res⟩
  have zsp : (⟨Z, RZ⟩ : Machine).core.get 2 = m₀.core.get 2 := CZ.sp
  unfold EncRes at res
  rw [zsp] at res
  exact post_enc m₀ h m' (ctx_call m₀ ⟨Z, RZ⟩ m' CZ P) P.pc ((P.saved 9 (by decide)).trans z9) res

/-- At 0x80003ec6: the response byte (two ways), then `enc_tail`. -/
theorem post_hdr (hE : EncodeContract) (m₀ : Machine) (h : SomeAt m₀) (H : Core) (RH : Word → BitVec 8)
    (hpc : H.pc = 0x80003ec6) (CH : Ctx m₀ ⟨H, RH⟩) : Lands B img SomeQ ⟨H, RH⟩ := by
  have x22 : H.get 22 = s6v := CH.s6
  cases ha : taken .ne (alu .and (alu .sltu (0) (ramRead RH (H.get 22 + 0x000002db#32) .w))
      (alu .sltu (alu .add (H.get 11) 0xfffffffd#32) 0x00000001#32)) (0) with
  | true =>
    have rA := sEncA H RH hpc CH.quiet (by rw [x22]; decide) (by rw [x22]; decide) (by rw [x22]; decide)
      (by rw [x22]; decide) ha
    have cs := sEncACsr H RH
    have pA : (sEncACore H RH).pc = 0x80003ee0 := rfl
    have gA : ∀ r : Reg, r ≠ 11 → r ≠ 12 → (sEncACore H RH).get r = H.get r := fun r a b => by
      simp [sEncACore, Core.wr_get_ne, a, b]
    have hRA : ∀ x, ¬ PW (m₀.core.get 2) x → sEncARam H RH x = RH x := by
      intro x hx
      simp only [sEncARam, x22]
      exact wr_pw _ x hx _ _ _ _ (.inl (by decide)) (by decide)
    generalize sEncACore H RH = A at rA cs pA gA
    generalize sEncARam H RH = RA at rA hRA
    exact lands_of_qrun_lands rA (enc_tail hE m₀ h A RA pA (ctx_seg m₀ h H A RH RA CH
      (Quiet.of_sameCsr cs CH.quiet) (gA 2 (by decide) (by decide)) (gA 22 (by decide) (by decide))
      (gA 23 (by decide) (by decide)) (gA 26 (by decide) (by decide)) hRA))
  | false =>
    have rA := sEncB H RH hpc CH.quiet (by rw [x22]; decide) (by rw [x22]; decide) (by rw [x22]; decide)
      (by rw [x22]; decide) ha
    have cs := sEncBCsr H RH
    have pA : (sEncBCore H RH).pc = 0x80003ee0 := rfl
    have gA : ∀ r : Reg, r ≠ 11 → r ≠ 12 → (sEncBCore H RH).get r = H.get r := fun r a b => by
      simp [sEncBCore, Core.wr_get_ne, a, b]
    have hRA : ∀ x, ¬ PW (m₀.core.get 2) x → sEncBRam H RH x = RH x := by
      intro x hx
      simp only [sEncBRam, x22]
      exact wr_pw _ x hx _ _ _ _ (.inl (by decide)) (by decide)
    generalize sEncBCore H RH = A at rA cs pA gA
    generalize sEncBRam H RH = RA at rA hRA
    exact lands_of_qrun_lands rA (enc_tail hE m₀ h A RA pA (ctx_seg m₀ h H A RH RA CH
      (Quiet.of_sameCsr cs CH.quiet) (gA 2 (by decide) (by decide)) (gA 22 (by decide) (by decide))
      (gA 23 (by decide) (by decide)) (gA 26 (by decide) (by decide)) hRA))

/-- Back from dispatch at 0x80003e9e: Pending, 0xff, or the header update and `post_hdr`. -/
theorem post_disp (hE : EncodeContract) (m₀ : Machine) (h : SomeAt m₀) (e : Core) (M : Word → BitVec 8)
    (hpc : e.pc = 0x80003e9e) (c : Ctx m₀ ⟨e, M⟩) : Lands B img SomeQ ⟨e, M⟩ := by
  have e22 : e.get 22 = s6v := c.s6
  cases hp : taken .eq (alu .and (e.get 10) 0x000000ff#32) (alu .add (0) 0x000000fe#32) with
  | true => exact lands_of_qrun (sPend e M hpc c.quiet hp) (.inr (.inl rfl))
  | false =>
    cases hf : taken .eq (alu .and (e.get 10) 0x000000ff#32) (alu .add (0) 0x000000ff#32) with
    | true =>
      exact lands_of_qrun (sFF e M hpc c.quiet hp (by rw [e22]; decide) (by rw [e22]; decide)
        (by rw [e22]; decide) (by rw [e22]; decide) (by rw [e22]; decide) (by rw [e22]; decide) hf)
        (.inr (.inr (.inl rfl)))
    | false =>
      have rH := sHdr e M hpc c.quiet hp (by rw [e22]; decide) (by rw [e22]; decide) (by rw [e22]; decide)
        (by rw [e22]; decide) (by rw [e22]; decide) (by rw [e22]; decide) hf
      have cs := sHdrCsr e M
      have pH : (sHdrCore e M).pc = 0x80003ec6 := rfl
      have gH : ∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → (sHdrCore e M).get r = e.get r := fun r a b d => by
        simp [sHdrCore, Core.wr_get_ne, a, b, d]
      have hRH : ∀ x, ¬ PW (m₀.core.get 2) x → sHdrRam e M x = M x := by
        intro x hx
        simp only [sHdrRam, e22]
        exact wr_pw _ x hx _ _ _ _ (.inl (by decide)) (by decide)
      generalize sHdrCore e M = H at rH cs pH gH
      generalize sHdrRam e M = RH at rH hRH
      exact lands_of_qrun_lands rH (post_hdr hE m₀ h H RH pH (ctx_seg m₀ h e H M RH c
        (Quiet.of_sameCsr cs c.quiet) (gH 2 (by decide) (by decide) (by decide))
        (gH 22 (by decide) (by decide) (by decide)) (gH 23 (by decide) (by decide) (by decide))
        (gH 26 (by decide) (by decide) (by decide)) hRH))

/-! ## The Some point -/

theorem rd_wr_same (X : Word → BitVec 8) (a b v : Word) (h : a = b) : ramRead (ramWrite X a v .w) b .w = v := by
  subst h; exact ramRead_ramWrite_w X a v

theorem wr_b_same (X : Word → BitVec 8) (a b v : Word) (h : a = b) : ramWrite X a v .b b = byteOf v 0 := by
  subst h; simp [ramWrite, ramPut]

/-- **The Some path for a non-negative header**, against the two named contracts. -/
theorem some_pos (W : (Word → BitVec 8) → Prop) (hD : DispatchContract W) (hE : EncodeContract)
    (m₀ : Machine) (h : SomeAt m₀) (hW : WAt W m₀) (hpos : (m₀.ram 0x8002a589).toNat < 0x80) :
    Lands B img SomeQ m₀ := by
  have C0 : Ctx m₀ m₀ := ⟨h.quiet, rfl, h.s6, h.s7, h.ext.s10, fun _ _ => rfl⟩
  have h1 : 0x8002a798 + 0x70 ≤ (m₀.core.get 2).toNat ∧ (m₀.core.get 2).toNat ≤ 0x81000000 := h.sp
  have h2 : (m₀.core.get 2).toNat + 0x148 ≤ 0x81000000 := h.ext.spTop
  have spA : (m₀.core.get 2).toNat % 4 = 0 := h.spAl
  obtain ⟨c, M⟩ := m₀
  have h22 : c.get 22 = s6v := h.s6
  have hc2 : (c.get 2).toNat + 0x148 ≤ 0x81000000 := h2
  have hc1 : 0x8002a798 + 0x70 ≤ (c.get 2).toNat := h1.1
  have hcA : (c.get 2).toNat % 4 = 0 := spA
  have r := sCall c M h.pc h.quiet (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide)
    (by rw [h22]; decide)
    (by rw [h22]
        show taken .lt (extend .h true (BitVec.ofNat 32 ((M 0x8002a588).toNat + 256 * (M 0x8002a589).toNat))) 0 = false
        exact pos_h _ _ hpos)
    (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide)
    (by rw [spOff _ _ (by omega)]; omega) (spIn _ _ _ (by omega) (by omega))
    (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide)
    (by rw [h22]; decide) (by rw [h22]; decide)
  have cs := sCallCsr c M
  have pD : (sCallCore c M).pc = 0x800001f2 := rfl
  have gD : ∀ r : Reg, r ≠ 1 → r ≠ 10 → (sCallCore c M).get r = c.get r := fun r a b => by
    simp [sCallCore, Core.wr_get_ne, a, b]
  have d1 : (sCallCore c M).get 1 = 0x80003e9e := by simp [sCallCore, Core.wr_get_self]
  have d10 : (sCallCore c M).get 10 = 0x8002a7b0 := by
    simp [sCallCore, Core.wr_get_ne, Core.wr_get_self, alu_add, h22]; rfl
  have d2 : (sCallCore c M).get 2 = c.get 2 := gD 2 (by decide) (by decide)
  have hRD : ∀ x, ¬ PW (c.get 2) x → sCallRam c M x = M x := by
    intro x hx
    simp only [sCallRam, h22]
    simp (disch := (simp only [s6v]; bv_omega)) only [wr_pw (c.get 2) x hx]
  have fS : sCallRam c M 0x8002a7bc = 0 := by
    simp only [sCallRam, h22]; rw [wr_b_same _ _ _ _ (by decide)]; decide
  have fV : ramRead (sCallRam c M) 0x8002a7b0 .w = ramRead (sCallRam c M) 0x8002a780 .w := by
    simp only [sCallRam, h22]
    simp (disch := decide) only [rd_wr_far, rd_wr_same]
    rfl
  have e20 : ∀ R' : Word → BitVec 8, (∀ x, ¬ PW (c.get 2) x → R' x = M x) →
      ramRead R' (c.get 2 + 0x00000020#32) .w = ramRead M (c.get 2 + 0x00000020#32) .w := by
    intro R' hR'
    refine ramRead_w_congr _ fun k hk => hR' _ ?_
    unfold PW
    rw [spOff _ _ (by rw [spOff _ _ (by omega)]; omega), spOff _ _ (by omega)]
    omega
  have fA : ramRead (sCallRam c M) 0x8002a7b4 .w = ramRead (sCallRam c M) (c.get 2 + 0x00000020#32) .w := by
    rw [e20 _ hRD]
    simp only [sCallRam, h22]
    simp (disch := decide) only [rd_wr_far, rd_wr_same]
    refine e20 _ fun x hx => ?_
    simp (disch := (simp only [s6v]; bv_omega)) only [wr_pw (c.get 2) x hx]
  have fM : ramRead (sCallRam c M) 0x8002a7b8 .w = c.get 9 := by
    simp only [sCallRam, h22]
    simp (disch := decide) only [rd_wr_far, rd_wr_same]
  have lowR : ∀ a : Word, a.toNat + 4 ≤ 0x8002a7a8 → ramRead (sCallRam c M) a .w = ramRead M a .w :=
    fun a ha => ramRead_w_congr _ fun k hk => hRD _ (by
      have : (a + BitVec.ofNat 32 k).toNat = a.toNat + k := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      unfold PW; rw [this]; omega)
  have hm := h.msg
  have env : DispEnv ⟨sCallCore c M, sCallRam c M⟩ :=
    ⟨pD, Quiet.of_sameCsr cs h.quiet, d1, d10, (gD 22 (by decide) (by decide)).trans h22,
      (gD 23 (by decide) (by decide)).trans h.s7, by show (_ : Word).toNat % 4 = 0; rw [d2]; exact hcA,
      by show _ ∧ _; rw [d2]; exact ⟨hc1, hc2⟩, fS, fV, by show _ = ramRead _ ((sCallCore c M).get 2 + _) .w; rw [d2]; exact fA,
      by show _ = (sCallCore c M).get 9; rw [gD 9 (by decide) (by decide)]; exact fM,
      by show ramRead (sCallRam c M) _ .w = _; rw [lowR _ (by decide)]; exact h.ext.svc,
      by show (sCallCore c M).get 9 = _; rw [gD 9 (by decide) (by decide)]; exact h.s9,
      by show ramRead (sCallRam c M) msgA .w = bufA ∧ _
         rw [lowR msgA (by decide), lowR (msgA + 4) (by decide), lowR (msgA + 0xc) (by decide)]; exact hm,
      by show (sCallRam c M 0x8002a589).toNat < 0x80
         rw [hRD _ (by unfold PW; rw [show (0x8002a589 : Word).toNat = 0x8002a589 from rfl]; omega)]; exact hpos⟩
  generalize sCallCore c M = D at r cs gD env
  generalize sCallRam c M = RD at r hRD env
  have CD : Ctx ⟨c, M⟩ ⟨D, RD⟩ := ctx_seg ⟨c, M⟩ h c D M RD C0 (Quiet.of_sameCsr cs h.quiet)
    (gD 2 (by decide) (by decide)) (gD 22 (by decide) (by decide)) (gD 23 (by decide) (by decide))
    (gD 26 (by decide) (by decide)) hRD
  refine lands_of_qrun_lands r (lands_seq ?_ (hD _ env (hW _ hRD)))
  rintro ⟨e', M'⟩ P
  exact post_disp hE ⟨c, M⟩ h e' M' P.pc (ctx_call _ _ _ CD P)

/-- **The Some path, every header**: back to the loop head with `SessInv`, or one of the explicit
boundaries (Pending to the executor, the 0xff path, the send loop). Conditional on the two named
contracts. -/
theorem some_round (W : (Word → BitVec 8) → Prop) (hD : DispatchContract W) (hE : EncodeContract)
    (m₀ : Machine) (h : SomeAt m₀) (hW : WAt W m₀) :
    Lands B img SomeQ m₀ := by
  by_cases hn : 0x80 ≤ (m₀.ram 0x8002a589).toNat
  · obtain ⟨k, m', r, hpc, hI⟩ := some_neg m₀ h hn
    exact lands_of_qrun r (.inl ⟨hpc, hI⟩)
  · exact some_pos W hD hE m₀ h hW (by omega)

end E5R.Rmk.Deframer.SomeP
