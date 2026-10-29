/-
  The firmware ring-tail summary (Tail.lean) between abstract states of the
  certificate checker: `spec : SumSpec` at pc 0x20010482 and `spec_sound`
  for `E5R.AI.check_sound_hybrid`'s `hsums`, next to the ring-head summary
  (RingAI.lean).

  Original e5r code, Apache-2.0.

  `enterOk` asks for: the exact pc, a main-thread state, MIE known clear,
  the channel `s1` an exact address whose head and tail words (+0x14,
  +0x18) are aligned RAM and whose four buffer bytes (+0x1d..+0x20) are
  RAM, and a fact in the abstract memory that the tail word is in 0..3.
  The tail bound is read from the checker's own memory facts (`lookup`,
  the function the checker's loads use); an unknown tail is not accepted.

  `post` gives back: `a1` the buffer address (channel + 0..3), `a2` the
  head word as the abstract memory knows it (the load the region does),
  `a3` the new tail in 0..3, `a4` the wrap mask, the tail word 0..3
  (`storeStrong`), and every fact about the four buffer bytes, or guarded
  by them, dropped (`forget`): the sample byte is not tracked.
-/
import Projects.hifive1.hybrid.Tail
import Projects.hifive1.hybrid.RingAI

set_option maxRecDepth 100000

namespace E5R.Hifive1.Hybrid.TailAI
open E5R E5R.AI E5R.Hybrid E5R.Hifive1.Hybrid.Tail
open E5R.Hifive1.Hybrid.RingAI (cfg chan sameCsr_parts w_add)

def tailAV : AV := .vals [0, 1, 2, 3]
def maskAV : AV := .vals [0, 0xffffffff]
def bufAV (c : Nat) : AV := .vals [c, c + 1, c + 2, c + 3]

/-- Drop every fact about the word at `a` (four bytes from `a`), or guarded
    by bytes it overlaps: what the checker's `storeStrong` keeps, without the
    new fact. -/
def forget (mem : List Cell) (a : Nat) : List Cell :=
  mem.filter fun c => !c.staleAfter .abs a .w .top

/-- The abstract memory knows the tail word of channel `c` is in 0..3. -/
def tailOk (s : AState) (c : Nat) : Bool :=
  match lookup s.mem .abs (c + 0x18) .w with
  | some v => v.leq (.rng 0 3)
  | none => false

def enterOk (s : AState) : Bool :=
  s.pc == 0x20010482 && !s.hnd && s.mie == .no && s.wf cfg && noSym s &&
  match s.get 9 with
  | .vals [c] => c + 0x20 < M32 && (c + 0x14) % 4 == 0 && cfg.board.inRam (w (c + 0x14)) 4 &&
      cfg.board.inRam (w (c + 0x18)) 4 && cfg.board.inRam (w (c + 0x1d)) 4 && tailOk s c
  | _ => false

def post (s : AState) : AState :=
  { ((((s.set 11 (bufAV (chan s))).set 12 (loadCell s.mem .abs (chan s + 0x14) .w)).set 13 tailAV).set
      14 maskAV) with
    pc := 0x2001049e
    mem := storeStrong (forget s.mem (chan s + 0x1d)) .abs (chan s + 0x18) .w tailAV }

theorem w_add_k (A k : Nat) : w (A + k) = w A + w k := by
  apply BitVec.eq_of_toNat_eq; simp [w, BitVec.toNat_add, Nat.add_mod]

/-- A byte write anywhere in the word at `A` keeps the facts `forget` keeps. -/
theorem forget_holds {ρ : Nat → Word} {ram : Word → BitVec 8} {mem : List Cell} {A k : Nat} {v : Word}
    (hm : MemHolds ρ ram mem) (hsep : StoreSep ρ mem .abs A .w .top) (hk : k < 4) :
    MemHolds ρ (ramWrite ram (w (A + k)) v .b) (forget mem A) := by
  intro c hc
  obtain ⟨hc, hns⟩ := List.mem_filter.mp hc
  simp only [Bool.not_eq_true'] at hns
  obtain ⟨hd, hg⟩ := hsep c hc hns
  have sub : ∀ x, Touches (addrOf ρ .abs (A + k)) .b x → Touches (addrOf ρ .abs A) .w x := by
    rintro x ⟨j, hj, rfl⟩
    have : j = 0 := by simp only [Width.bytes] at hj; omega
    subst this
    exact ⟨k, by simp only [Width.bytes]; omega, by simp only [addrOf, w0]; rw [w_add_k]; exact BitVec.add_zero _⟩
  refine kept_holds (base := .abs) (a := A + k) (V := .top) (hm c hc) trivial
    (fun x h1 h2 => hd x h1 (sub x h2)) ?_
  intro g hgc
  rcases hg g hgc with h | ⟨_, _, _, h⟩
  · exact .inl fun x h1 h2 => h x h1 (sub x h2)
  · cases h

/-- From every machine an accepted abstract entry state describes, the
    region's masked run ends in a machine `post` of that state describes. -/
theorem adapter {s : AState} {m : Machine} (ha : enterOk s = true) (hs : StateHolds ρM s m) :
    ∃ m', MRun B img 10 m m' ∧ StateHolds ρM (post s) m' := by
  unfold enterOk at ha
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at ha
  obtain ⟨⟨⟨⟨⟨hpc, hnd⟩, hmie⟩, hwf⟩, _⟩, h9⟩ := ha
  split at h9
  · rename_i c hc9
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h9
    obtain ⟨⟨⟨⟨⟨hlt, hal⟩, h14⟩, h18⟩, h1d⟩, htok⟩ := h9
    have hM : c + 0x20 < 2 ^ 32 := hlt
    have hS : m.core.get 9 = w c := by
      have := hs.regs 9; rw [hc9] at this
      simp only [AV.gam, List.mem_singleton] at this
      rw [← this]; simp [w]
    have e14 : m.core.get 9 + 0x14 = w (c + 0x14) := by rw [hS]; exact w_add c 0x14
    have e18 : m.core.get 9 + 0x18 = w (c + 0x18) := by rw [hS]; exact w_add c 0x18
    have n14 : (w (c + 0x14)).toNat = c + 0x14 := by simp [w]; omega
    have n18 : (w (c + 0x18)).toNat = c + 0x18 := by simp [w]; omega
    -- The tail word, from the abstract memory.
    have hT : (tail m).toNat < 4 := by
      unfold tailOk at htok
      split at htok
      · rename_i v hv
        have := leq_sound htok (lookup_sound hs.mem hv)
        simp only [AV.gam] at this
        unfold tail; rw [e18]; show _ < 4
        have h' : (ramRead m.ram (addrOf ρM .abs (c + 0x18)) .w).toNat ≤ 3 := this.2
        exact Nat.lt_succ_of_le h'
      · simp at htok
    have eT : tail m + m.core.get 9 + 0x1d = w (c + 0x1d + (tail m).toNat) := by
      rw [hS]; apply BitVec.eq_of_toNat_eq; simp [w, BitVec.toNat_add]; omega
    have hbuf : B.inRam (tail m + m.core.get 9 + 0x1d) 1 = true := by
      have hb := (Board.inRam_iff (B := B) _ _).mp h1d
      have hw : (w (c + 0x1d)).toNat = c + 0x1d := by simp [w]; omega
      rw [hw] at hb
      rw [Board.inRam_iff, eT]
      have : (w (c + 0x1d + (tail m).toNat)).toNat = c + 0x1d + (tail m).toNat := by simp [w]; omega
      rw [this]; omega
    have hmk : m.core.mie_ = false := by
      have := hs.mie; revert this hmie; cases s.mie <;> cases m.core.mie_ <;> simp [Tri.mayBe]
    have pre : Pre m := ⟨by rw [hs.pc, hpc]; rfl, hmk, by rw [e14, n14]; exact hal,
      by rw [e14]; exact h14, by rw [e18, n18]; omega, by rw [e18]; exact h18, hT, hbuf⟩
    obtain ⟨m', hr, sp⟩ := contract m pre
    refine ⟨m', hr, ?_⟩
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := sameCsr_parts sp.csr
    have hlen : s.regs.length = 31 := by
      unfold AState.wf at hwf; simp only [Bool.and_eq_true, beq_iff_eq] at hwf; exact hwf.1.1.1
    have hch : chan s = c := by simp [chan, hc9]
    let s1 := s.set 11 (bufAV c)
    let s2 := s1.set 12 (loadCell s.mem .abs (c + 0x14) .w)
    let s3 := s2.set 13 tailAV
    have l1 : s1.regs.length = 31 := by simp [s1, AState.set, hlen]
    have l2 : s2.regs.length = 31 := by simp [s2, s1, AState.set, hlen]
    have pg : ∀ r, (post s).get r = (s3.set 14 maskAV).get r := fun _ => by rw [post, hch]; rfl
    have cT := cases4 hT
    refine ⟨?pc, fun r => ?regs, ?mem, ?mie, ?mpie, ?mpp, ?mieReg, ?mtvec, ?mepc, ?mcause, ?msc⟩
    case pc => rw [sp.pc]; rfl
    case regs =>
      rw [pg]
      by_cases r14 : r = 14
      · subst r14
        rw [AState.get_set_self _ _ _ (by decide) (by simp [s3, AState.set, l2]), sp.a4]
        rcases cT with h | h | h | h <;> rw [h] <;> simp only [maskAV, AV.gam] <;> decide
      rw [AState.get_set_ne _ _ _ _ r14]
      by_cases r13 : r = 13
      · subst r13; rw [AState.get_set_self _ _ _ (by decide) l2, sp.a3]
        have := next_lt hT
        simp only [tailAV, AV.gam, List.mem_cons, List.not_mem_nil, or_false]; omega
      rw [AState.get_set_ne _ _ _ _ r13]
      by_cases r12 : r = 12
      · subst r12; rw [AState.get_set_self _ _ _ (by decide) l1, sp.a2, e14]
        exact loadCell_sound (base := .abs) hs.mem
      rw [AState.get_set_ne _ _ _ _ r12]
      by_cases r11 : r = 11
      · subst r11; rw [AState.get_set_self _ _ _ (by decide) hlen, sp.a1, hS]
        have : (tail m + w c).toNat = (tail m).toNat + c := by simp [w, BitVec.toNat_add]; omega
        simp only [bufAV, AV.gam, List.mem_cons, List.not_mem_nil, or_false, this]; omega
      rw [AState.get_set_ne _ _ _ _ r11, sp.frame r r11 r12 r13 r14]; exact hs.regs r
    case mem =>
      show MemHolds ρM m'.ram (storeStrong (forget s.mem (chan s + 0x1d)) .abs (chan s + 0x18) .w tailAV)
      rw [hch, sp.ram, eT, e18]
      have hwfm : ∀ c ∈ s.mem, c.wf cfg = true ∧ c.base = .abs := by
        unfold AState.wf at hwf
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true, hnd,
          Bool.false_or] at hwf
        exact fun c hc => ⟨hwf.1.1.2 c hc, hwf.1.2 c hc⟩
      have hwff : ∀ d ∈ forget s.mem (c + 0x1d), d.wf cfg = true ∧ d.base = .abs :=
        fun d hd => hwfm d (List.mem_filter.mp hd).1
      have hf : MemHolds ρM (ramWrite m.ram (w (c + 0x1d + (tail m).toNat)) (m.core.get 10) .b)
          (forget s.mem (c + 0x1d)) :=
        forget_holds hs.mem
          (storeSep_abs (cfg := cfg) (by decide) (fun d hd => (hwfm d hd).1) (by omega) h1d
            (fun d hd hb => by rw [(hwfm d hd).2] at hb; cases hb)) hT
      refine storeStrong_sound (base := .abs) hf ?_
        (storeSep_abs (cfg := cfg) (by decide) (fun d hd => (hwff d hd).1) (by omega) h18
          (fun d hd hb => by rw [(hwff d hd).2] at hb; cases hb))
      have := next_lt hT
      simp only [tailAV, stored, AV.gam, List.mem_cons, List.not_mem_nil, or_false]; omega
    case mie => show s.mie.mayBe m'.core.mie_ = true; rw [e1]; exact hs.mie
    case mpie => show s.mpie.mayBe m'.core.mpie = true; rw [e2]; exact hs.mpie
    case mpp => show m'.core.mpp.toNat ∈ s.mpp; rw [e3]; exact hs.mpp
    case mieReg => show s.mieReg.gam ρM m'.core.mieReg; rw [e4]; exact hs.mieReg
    case mtvec => show s.mtvec.gam ρM m'.core.mtvec; rw [e5]; exact hs.mtvec
    case mepc => show s.mepc.gam ρM m'.core.mepc; rw [e6]; exact hs.mepc
    case mcause => show s.mcause.gam ρM m'.core.mcause; rw [e7]; exact hs.mcause
    case msc => show s.mscratch.gam ρM m'.core.mscratch; rw [e8]; exact hs.mscratch
  · simp at h9

/-- `hentry` for delegating pc 0x20010482 to `Hybrid.regionOf`, for any
    certificate; the certificate-specific part is a kernel-evaluable Bool. -/
theorem hentry_of {cert : Cert}
    (hok : cert.nodes.all (fun n => !(n.s.pc == 0x20010482) || n.s.hnd ||
      (enterOk n.s && cert.nodes.any fun n' => !n'.s.hnd && (post n.s).leq n'.s)) = true)
    (n : Node) (hn : n ∈ cert.nodes) (hpc : n.s.pc = 0x20010482) (hnd : n.s.hnd = false)
    (m : Machine) (hs : StateHolds ρM n.s m) :
    (regionOf { cfg with hkeep := cert.hkeep } cert).R m := by
  have h := List.all_eq_true.mp hok n hn
  simp only [hpc, beq_self_eq_true, Bool.not_true, hnd, Bool.false_or, Bool.and_eq_true,
    List.any_eq_true, Bool.not_eq_true'] at h
  obtain ⟨ha, n', hn', hnd', hleq⟩ := h
  obtain ⟨m', hr, hpost⟩ := adapter ha hs
  exact regionOf_entry hr (mainInv_of_cover hn' hnd' hleq hpost)

/-- The summary as the checker's data. -/
def spec : SumSpec := { pc := 0x20010482, accepts := enterOk, post := post }

/-- **The ring-tail summary is sound** in the checker's sense, for any kept
    intervals: `check_sound_hybrid`'s `hsums` for `spec`. -/
theorem spec_sound (keep : List (Nat × Nat)) : SumSound { cfg with hkeep := keep } spec := by
  intro s m _ ha _ hs
  obtain ⟨m', hr, hpost⟩ := adapter ha hs
  exact safeStep_of_mrun (cfg := { cfg with hkeep := keep }) (n := 9) hr hpost

end E5R.Hifive1.Hybrid.TailAI
