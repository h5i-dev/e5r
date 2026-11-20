/-
  The firmware ring-head summary (Ring.lean) between abstract states of the
  certificate checker, ready for `E5R.AI.check_sound_hybrid` on the Embassy
  firmware: a certificate may delegate pc 0x20010698 to region
  `Hybrid.regionOf`, and `hentry` follows from `adapter` for every delegated
  node whose state `enterOk` accepts, once the analyzer covers `post` of it.

  Original e5r code, Apache-2.0.

  `enterOk` asks for: the exact pc, a main-thread state, MIE known clear
  (the critical section entered at 0x20010638), the head `a0` in 0..3, the
  channel `s1` an exact address whose head word (+0x14) is aligned RAM and
  whose four buffer bytes (+0x1d..+0x20) are RAM. `post` gives back: the new
  head in 0..3 in `a0` and in the head word, the buffer byte in `a1`, the
  intermediate values in `a2`/`a3`, and everything else as at entry (the
  store invalidates only facts it overlaps, by `storeStrong`).
-/
import Projects.hifive1.hybrid.Ring
import Theories.Hybrid.AIBridge
import Projects.hifive1.Config

set_option maxRecDepth 100000

namespace E5R.Hifive1.Hybrid.RingAI
open E5R E5R.AI E5R.Hybrid E5R.Hifive1.Hybrid.Ring

abbrev cfg := E5R.Hifive1.Job.cfg

def headAV : AV := .vals [0, 1, 2, 3]
def byteAV : AV := .rng 0 255
def a2AV : AV := .vals [1, 2, 3, 4]
def a3AV : AV := .vals [0, 0xfffffffd, 0xfffffffe, 0xffffffff]

/-- The channel address the entry state holds in `s1`. -/
def chan (s : AState) : Nat := match s.get 9 with | .vals [c] => c | _ => 0

def enterOk (s : AState) : Bool :=
  s.pc == 0x20010698 && !s.hnd && s.mie == .no && s.wf cfg && noSym s &&
  (s.get 10).leq (.rng 0 3) &&
  match s.get 9 with
  | .vals [c] => c + 0x20 < M32 && (c + 0x14) % 4 == 0 && cfg.board.inRam (w (c + 0x14)) 4 &&
      cfg.board.inRam (w (c + 0x1d)) 4
  | _ => false

def post (s : AState) : AState :=
  { ((((s.set 10 headAV).set 11 byteAV).set 12 a2AV).set 13 a3AV) with
    pc := 0x200106b0
    mem := storeStrong s.mem .abs (chan s + 0x14) .w headAV }

theorem sameCsr_parts {c d : Core} (h : c.sameCsr d) :
    c.mie_ = d.mie_ ∧ c.mpie = d.mpie ∧ c.mpp = d.mpp ∧ c.mieReg = d.mieReg ∧ c.mtvec = d.mtvec ∧
      c.mepc = d.mepc ∧ c.mcause = d.mcause ∧ c.mscratch = d.mscratch := by
  simp only [Core.sameCsr, Core.ctl, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

theorem w_add (c k : Nat) : w c + BitVec.ofNat 32 k = w (c + k) := by
  apply BitVec.eq_of_toNat_eq; simp [w, BitVec.toNat_add]

/-- From every machine an accepted abstract entry state describes, the
    region's masked run ends in a machine `post` of that state describes. -/
theorem adapter {s : AState} {m : Machine} (ha : enterOk s = true) (hs : StateHolds ρM s m) :
    ∃ m', MRun B img 8 m m' ∧ StateHolds ρM (post s) m' := by
  unfold enterOk at ha
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at ha
  obtain ⟨⟨⟨⟨⟨⟨hpc, hnd⟩, hmie⟩, hwf⟩, _⟩, h10⟩, h9⟩ := ha
  split at h9
  · rename_i c hc9
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h9
    obtain ⟨⟨⟨hlt, hal⟩, hcell⟩, hbuf⟩ := h9
    have hS : m.core.get 9 = w c := by
      have := hs.regs 9; rw [hc9] at this
      simp only [AV.gam, List.mem_singleton] at this
      rw [← this]; simp [w]
    have hH : (m.core.get 10).toNat < 4 := by
      have := leq_sound h10 (hs.regs 10); simp only [AV.gam] at this; omega
    have hmk : m.core.mie_ = false := by
      have := hs.mie; revert this hmie; cases s.mie <;> cases m.core.mie_ <;> simp [Tri.mayBe]
    have e14 : m.core.get 9 + 0x14 = w (c + 0x14) := by rw [hS]; exact w_add c 0x14
    have hw14 : (w (c + 0x14)).toNat = c + 0x14 := by simp [w]; unfold M32 at hlt; omega
    have hbyte : B.inRam (m.core.get 10 + m.core.get 9 + 0x1d) 1 = true := by
      have hb := (Board.inRam_iff (B := B) _ _).mp hbuf
      have hw : (w (c + 0x1d)).toNat = c + 0x1d := by simp [w]; unfold M32 at hlt; omega
      rw [hw] at hb
      rw [Board.inRam_iff, hS]
      have : (m.core.get 10 + w c + 0x1d).toNat = (m.core.get 10).toNat + c + 0x1d := by
        simp [w, BitVec.toNat_add]; unfold M32 at hlt; omega
      rw [this]; omega
    have pre : Pre m := ⟨by rw [hs.pc, hpc]; rfl, hH, hmk, by rw [e14, hw14]; exact hal,
      by rw [e14]; exact hcell, hbyte⟩
    obtain ⟨m', hr, sp⟩ := contract m pre
    refine ⟨m', hr, ?_⟩
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := sameCsr_parts sp.csr
    have hlen : s.regs.length = 31 := by
      unfold AState.wf at hwf; simp only [Bool.and_eq_true, beq_iff_eq] at hwf; exact hwf.1.1.1
    have l1 : (s.set 10 headAV).regs.length = 31 := by simp [AState.set, hlen]
    have l2 : ((s.set 10 headAV).set 11 byteAV).regs.length = 31 := by simp [AState.set, hlen]
    have l3 : (((s.set 10 headAV).set 11 byteAV).set 12 a2AV).regs.length = 31 := by
      simp [AState.set, hlen]
    have pg : ∀ r, (post s).get r = ((((s.set 10 headAV).set 11 byteAV).set 12 a2AV).set 13 a3AV).get r :=
      fun _ => rfl
    have cases4' := cases4 hH
    refine ⟨?pc, fun r => ?regs, ?mem, ?mie, ?mpie, ?mpp, ?mieReg, ?mtvec, ?mepc, ?mcause, ?msc⟩
    case pc => rw [sp.pc]; rfl
    case regs =>
      rw [pg]
      by_cases r13 : r = 13
      · subst r13; rw [AState.get_set_self _ _ _ (by decide) l3, sp.a3]
        rcases cases4' with h | h | h | h <;> rw [h] <;> simp only [a3AV, AV.gam] <;> decide
      rw [AState.get_set_ne _ _ _ _ r13]
      by_cases r12 : r = 12
      · subst r12; rw [AState.get_set_self _ _ _ (by decide) l2, sp.a2]
        rcases cases4' with h | h | h | h <;> rw [h] <;> simp only [a2AV, AV.gam] <;> decide
      rw [AState.get_set_ne _ _ _ _ r12]
      by_cases r11 : r = 11
      · subst r11; rw [AState.get_set_self _ _ _ (by decide) l1, sp.byte]
        show 0 ≤ (extend .b false _).toNat ∧ (extend .b false _).toNat ≤ 255
        simp only [extend, BitVec.toNat_and]
        exact ⟨Nat.zero_le _, Nat.le_trans Nat.and_le_right (by decide)⟩
      rw [AState.get_set_ne _ _ _ _ r11]
      by_cases r10 : r = 10
      · subst r10; rw [AState.get_set_self _ _ _ (by decide) hlen, sp.head]
        have := next_lt hH
        simp only [headAV, AV.gam, List.mem_cons, List.not_mem_nil, or_false]; omega
      rw [AState.get_set_ne _ _ _ _ r10, sp.frame r r10 r11 r12 r13]; exact hs.regs r
    case mem =>
      show MemHolds ρM m'.ram (storeStrong s.mem .abs (chan s + 0x14) .w headAV)
      have hch : chan s = c := by simp [chan, hc9]
      rw [hch, sp.ram, e14]
      have hwfm : ∀ c ∈ s.mem, c.wf cfg = true ∧ c.base = .abs := by
        unfold AState.wf at hwf
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true, hnd,
          Bool.false_or] at hwf
        exact fun c hc => ⟨hwf.1.1.2 c hc, hwf.1.2 c hc⟩
      refine storeStrong_sound (base := .abs) hs.mem ?_
        (storeSep_abs (cfg := cfg) (by decide) (fun c hc => (hwfm c hc).1) (by omega) hcell
          (fun c hc hb => by rw [(hwfm c hc).2] at hb; cases hb))
      have := next_lt hH
      simp only [headAV, stored, AV.gam, List.mem_cons, List.not_mem_nil, or_false]; omega
    case mie => show s.mie.mayBe m'.core.mie_ = true; rw [e1]; exact hs.mie
    case mpie => show s.mpie.mayBe m'.core.mpie = true; rw [e2]; exact hs.mpie
    case mpp => show m'.core.mpp.toNat ∈ s.mpp; rw [e3]; exact hs.mpp
    case mieReg => show s.mieReg.gam ρM m'.core.mieReg; rw [e4]; exact hs.mieReg
    case mtvec => show s.mtvec.gam ρM m'.core.mtvec; rw [e5]; exact hs.mtvec
    case mepc => show s.mepc.gam ρM m'.core.mepc; rw [e6]; exact hs.mepc
    case mcause => show s.mcause.gam ρM m'.core.mcause; rw [e7]; exact hs.mcause
    case msc => show s.mscratch.gam ρM m'.core.mscratch; rw [e8]; exact hs.mscratch
  · simp at h9

/-- What `check_sound_hybrid`'s `hentry` needs for this region, for any
    certificate: every delegated node at 0x20010698 is accepted and `post`
    of it is covered by a main-thread node. The certificate-specific part
    is the Boolean hypothesis, which the kernel evaluates. -/
theorem hentry_of {cert : Cert}
    (hok : cert.nodes.all (fun n => !(n.s.pc == 0x20010698) || n.s.hnd ||
      (enterOk n.s && cert.nodes.any fun n' => !n'.s.hnd && (post n.s).leq n'.s)) = true)
    (n : Node) (hn : n ∈ cert.nodes) (hpc : n.s.pc = 0x20010698) (hnd : n.s.hnd = false)
    (m : Machine) (hs : StateHolds ρM n.s m) :
    (regionOf { cfg with hkeep := cert.hkeep } cert).R m := by
  have h := List.all_eq_true.mp hok n hn
  simp only [hpc, beq_self_eq_true, Bool.not_true, hnd, Bool.false_or, Bool.and_eq_true,
    List.any_eq_true, Bool.not_eq_true'] at h
  obtain ⟨ha, n', hn', hnd', hleq⟩ := h
  obtain ⟨m', hr, hpost⟩ := adapter ha hs
  exact regionOf_entry hr (mainInv_of_cover hn' hnd' hleq hpost)

/-- The summary as the checker's data: the analyzer follows it, `summarized`
    checks a node against it (support-lean4 34fadf2). -/
def spec : SumSpec := { pc := 0x20010698, accepts := enterOk, post := post }

/-- **The ring-head summary is sound** in the checker's sense, for any kept
    intervals: `check_sound_hybrid`'s `hsums` for `spec`. -/
theorem spec_sound (keep : List (Nat × Nat)) : SumSound { cfg with hkeep := keep } spec := by
  intro s m _ ha _ hs
  obtain ⟨m', hr, hpost⟩ := adapter ha hs
  exact safeStep_of_mrun (cfg := { cfg with hkeep := keep }) (n := 7) hr hpost

end E5R.Hifive1.Hybrid.RingAI
