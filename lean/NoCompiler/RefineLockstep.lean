import NoCompiler.RefineRegion

/-
Refinement by a checked lockstep certificate (docs/isa/refine.md).

The certificate pairs program points: an entry `(pb, pa, live)` says B at
`pb` runs in step with A at `pa`, the two states agreeing on the registers
`live`, on memory, on the trace and on the exit status. `check` decides, in
the kernel, that

* each pair holds the SAME instruction on both sides, inside the two code
  regions, and it does not write `ra`;
* every successor of a pair is a pair, and the live sets satisfy the
  congruence rule's inclusion (`Instr.transfer`), at each successor;
* a return (`jalr zero, 0(ra)`) is reached with ra, a0, a1 and the
  preserved registers live;
* B's entry and A's entry are a pair.

`Refines.of_lockstep` is its soundness: such a certificate proves
`Refines sp A B` for every specification `sp`. This covers B = A relinked at
another address, and B = A with dead caller-saved computations changed
nothing else: the instructions must be the same, the registers they compute
into need not be live. It is the base case of the paired execution (item 3),
whose other cases add pairs of different instructions with a straight-line
equivalence obligation each.

Leaf functions only: a call writes ra. The pc relation is the table, so the
two functions may sit at different addresses but must have the same relative
layout between paired branches and their targets.
-/
namespace NoCompiler
namespace Lockstep

/-- B at `pb` and A at `pa`, agreeing on `live`. -/
structure Pair where
  pb : Word
  pa : Word
  live : List Reg
  deriving DecidableEq, Repr

/-- A certificate: pairs of identical instructions, and regions (changed
    intervals, each proved separately by `RRegion.Ok`). -/
structure Cert where
  pairs : List Pair
  regions : List RRegion := []

/-- The program points: every pair, and every region's entry with its live set. -/
def Cert.points (k : Cert) : List Pair :=
  k.pairs ++ k.regions.map fun r => ⟨r.pb, r.pa, r.liveIn⟩

def Cert.find (k : Cert) (pb pa : Word) : Option Pair :=
  k.points.find? fun e => e.pb == pb && e.pa == pa

theorem Cert.find_some {k : Cert} {pb pa : Word} {e : Pair} (h : k.find pb pa = some e) :
    e ∈ k.points ∧ e.pb = pb ∧ e.pa = pa := by
  unfold Cert.find at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨hm, hp.1, hp.2⟩

/-- The registers a caller observes at a return, and ra. -/
def obsRegs : List Reg := 1 :: retRegs ++ preservedRegs

def transferB (i : Instr) (L L' : List Reg) : Bool :=
  i.uses.all (fun r => L'.contains r) && L.all (fun r => i.defs.contains r || L'.contains r)

theorem transferB_sound {i : Instr} {L L' : List Reg} (h : transferB i L L' = true) :
    i.transfer L L' := by
  unfold transferB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, Bool.or_eq_true] at h
  exact ⟨h.1, fun r hr hd => (h.2 r hr).resolve_left hd⟩

/-- The successor `(pb, pa)` of a pair with live set `L` running `i` is a
    pair, whose live set `i` maps into `L`. -/
def succOk (k : Cert) (i : Instr) (L : List Reg) (pb pa : Word) : Bool :=
  match k.find pb pa with
  | some e => transferB i e.live L
  | none => false

theorem succOk_sound {k : Cert} {i : Instr} {L : List Reg} {pb pa : Word}
    (h : succOk k i L pb pa = true) : ∃ e ∈ k.points, e.pb = pb ∧ e.pa = pa ∧ i.transfer e.live L := by
  unfold succOk at h
  split at h
  · rename_i e he
    obtain ⟨hm, h1, h2⟩ := Cert.find_some he
    exact ⟨e, hm, h1, h2, transferB_sound h⟩
  · simp at h

/-- What a pair needs, by the kind of its instruction `i`. -/
def kindOk (k : Cert) (e : Pair) (i : Instr) : Bool :=
  match i with
  | .branch _ _ _ off =>
    i.uses.all e.live.contains &&
    succOk k i e.live (e.pb + 4) (e.pa + 4) &&
    decide (aligned (e.pb + off.signExtend 64) 4) && decide (aligned (e.pa + off.signExtend 64) 4) &&
    succOk k i e.live (e.pb + off.signExtend 64) (e.pa + off.signExtend 64)
  | .jal rd off =>
    rd == 0 &&
    decide (aligned (e.pb + off.signExtend 64) 4) && decide (aligned (e.pa + off.signExtend 64) 4) &&
    succOk k i e.live (e.pb + off.signExtend 64) (e.pa + off.signExtend 64)
  | .jalr rd rs1 off => rd == 0 && rs1 == 1 && off == 0 && obsRegs.all e.live.contains
  | .auipc .. => false
  | .ecall | .lui .. | .load .. | .store .. | .iop .. | .addiw .. | .shift .. | .shiftw ..
  | .rop .. | .rwop .. | .uop .. => succOk k i e.live (e.pb + 4) (e.pa + 4)

/-- A jump pair: the same branch (or `jal zero`) on both sides, but with its own
    offset on each, so the two layouts may differ (an instruction inserted
    before a branch target moves it). Each side's target is its own; the two
    targets must be a pair. -/
def jumpOk (k : Cert) (e : Pair) : Instr → Instr → Bool
  | .branch op a b offA, .branch op' a' b' offB =>
    op == op' && a == a' && b == b' && [a, b].all e.live.contains &&
    succOk k (.branch op a b offA) e.live (e.pb + 4) (e.pa + 4) &&
    decide (aligned (e.pb + offB.signExtend 64) 4) && decide (aligned (e.pa + offA.signExtend 64) 4) &&
    succOk k (.branch op a b offA) e.live (e.pb + offB.signExtend 64) (e.pa + offA.signExtend 64)
  | .jal rdA offA, .jal rdB offB =>
    rdA == 0 && rdB == 0 &&
    decide (aligned (e.pb + offB.signExtend 64) 4) && decide (aligned (e.pa + offA.signExtend 64) 4) &&
    succOk k (.jal 0 offA) e.live (e.pb + offB.signExtend 64) (e.pa + offA.signExtend 64)
  | _, _ => false

/-- What the kernel decides at one pair: the same word on both sides (cheaper
    for the kernel than comparing instructions), or a jump pair. -/
def pairOk (cA cB : Code) (DA DB : Dom) (k : Cert) (e : Pair) : Bool :=
  decide (DB.mem e.pb) && decide (DA.mem e.pa) &&
  ((cA.fetch e.pa == cB.fetch e.pb &&
    match cA.instr e.pa with
    | some ia => !(ia.defs.contains 1) && kindOk k e ia
    | none => false) ||
   match cA.instr e.pa, cB.instr e.pb with
   | some ia, some ib => jumpOk k e ia ib
   | _, _ => false)

/-- What the kernel decides of a region: its shape, and that its exit is a
    point whose live set its `liveOut` covers. -/
def regionOk (DA DB : Dom) (k : Cert) (r : RRegion) : Bool :=
  r.shapeOk DA DB &&
  match k.find r.pbExit r.paExit with
  | some e => e.live.all r.liveOut.contains
  | none => false

/-- The certificate check. -/
def check (cA cB : Code) (DA DB : Dom) (eA eB : Word) (k : Cert) : Bool :=
  k.pairs.all (pairOk cA cB DA DB k) && k.regions.all (regionOk DA DB k) && (k.find eB eA).isSome

/-! ## Soundness -/

section
variable {cA cB : Code} {DA DB : Dom} {k : Cert}

/-- The relation the certificate is a simulation for, from entry state `s0`:
    running in step at a pair, both returned to `s0`'s ra, or both exited. -/
def Rel (k : Cert) (s0 sa sb : State) : Prop :=
  (sa.exit = none ∧ sa.reg 1 = s0.reg 1 ∧ ∃ e ∈ k.points, sb.pc = e.pb ∧ sa.pc = e.pa ∧ Agree e.live sa sb) ∨
  (sa.exit = none ∧ sa.pc = s0.reg 1 ∧ sb.pc = s0.reg 1 ∧ Agree obsRegs sa sb) ∨
  (sa.exit ≠ none ∧ Agree [] sa sb)

/-- What `pairOk` gives, unpacked. -/
structure PairFacts (cA cB : Code) (DA DB : Dom) (k : Cert) (e : Pair) (i : Instr) : Prop where
  memB : DB.mem e.pb
  memA : DA.mem e.pa
  instrA : cA.instr e.pa = some i
  instrB : cB.instr e.pb = some i
  noRa : 1 ∉ i.defs
  kind : kindOk k e i = true

/-- What a jump pair gives. -/
structure JumpFacts (cA cB : Code) (DA DB : Dom) (k : Cert) (e : Pair) (ia ib : Instr) : Prop where
  memB : DB.mem e.pb
  memA : DA.mem e.pa
  instrA : cA.instr e.pa = some ia
  instrB : cB.instr e.pb = some ib
  kind : jumpOk k e ia ib = true

theorem pairOk_facts {e : Pair} (h : pairOk cA cB DA DB k e = true) :
    (∃ i, PairFacts cA cB DA DB k e i) ∨ ∃ ia ib, JumpFacts cA cB DA DB k e ia ib := by
  unfold pairOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hb, ha⟩, h | h⟩ := h
  · obtain ⟨hw, h⟩ := h
    split at h
    · rename_i ia hia
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hra, hk⟩ := h
      have hib : cB.instr e.pb = some ia := by
        unfold Code.instr at hia ⊢; rw [← hw]; exact hia
      exact .inl ⟨ia, hb, ha, hia, hib, by simpa using hra, hk⟩
    · simp at h
  · split at h
    · rename_i ia ib hia hib
      exact .inr ⟨ia, ib, hb, ha, hia, hib, h⟩
    · simp at h

theorem exec_exit {i : Instr} {s s' : State} (h : exec i s = some s') : s'.exit = s.exit := by
  cases i <;> simp only [exec, jumpTo] at h <;> (try split at h) <;> (try split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp

theorem exec_reg_of_not_def {i : Instr} {s s' : State} {r : Reg} (hr : r ∉ i.defs)
    (h : exec i s = some s') : s'.reg r = s.reg r := by
  cases i <;> simp only [Instr.defs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    simp only [exec, jumpTo] at h <;> (try split at h) <;> (try split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [hr]

theorem sys_reg_ra {s t : State} (h : Sys s t) : t.reg 1 = s.reg 1 := by
  cases h <;> simp [State.sysRet, show ¬ (1 : Reg) = Reg.a0 by decide]

theorem sys_exit_or {s t : State} (h : Sys s t) : t.exit = s.exit ∨ t.exit ≠ none := by
  cases h <;> simp [State.sysRet]

/-- `x &&& ~~~1` of a 4-aligned `x` is `x` (as in NoCompiler/Shift.lean). -/
theorem and_not_one_of_aligned {x : Word} (h : aligned x 4) : x &&& ~~~(1 : Word) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  by_cases h0 : i = 0
  · subst h0
    have : x.getLsbD 0 = false := by
      rw [BitVec.getLsbD, Nat.testBit_zero]; unfold aligned at h; simp; omega
    simpa [BitVec.getLsbD_eq_getElem] using this
  · have : (1#64).getLsbD i = false := by simp [BitVec.getLsbD_one, h0]
    simp [this]

/-- Agreement on x0 is free: it reads as zero in every state. -/
theorem _root_.NoCompiler.Agree.mono0 {L L' : List Reg} {sa sb : State} (h : Agree L' sa sb)
    (hs : ∀ r ∈ L, r ≠ 0 → r ∈ L') : Agree L sa sb := by
  refine ⟨fun r hr => ?_, h.mem, h.trace, h.exit⟩
  by_cases h0 : r = 0
  · subst h0; simp
  · exact h.regs r (hs r hr h0)

theorem _root_.NoCompiler.Agree.symm {L : List Reg} {sa sb : State} (h : Agree L sa sb) : Agree L sb sa :=
  ⟨fun r hr => (h.regs r hr).symm, h.mem.symm, h.trace.symm, h.exit.symm⟩

/-- At every pair, the instruction's operands are live. -/
theorem uses_live {e : Pair} {i : Instr} (hf : PairFacts cA cB DA DB k e i) :
    ∀ r ∈ i.uses, r ∈ e.live := by
  have hk := hf.kind
  cases i with
  | branch op a b off =>
    simp only [kindOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hk
    exact hk.1.1.1.1
  | jal => simp [Instr.uses]
  | jalr rd rs1 off =>
    simp only [kindOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at hk
    obtain ⟨⟨⟨_, rfl⟩, _⟩, h⟩ := hk
    intro r hr; simp only [Instr.uses, List.mem_singleton] at hr; subst hr
    exact h 1 (by simp [obsRegs])
  | auipc => simp [kindOk] at hk
  | _ =>
    simp only [kindOk] at hk
    obtain ⟨_, _, _, _, ht⟩ := succOk_sound hk; exact ht.1

/-- One B step from a pair is matched by one A step, into the relation. -/
theorem step_pair {P : Perm} {s0 : State} (hral : aligned (s0.reg 1) 4) {e : Pair} {i : Instr} (hf : PairFacts cA cB DA DB k e i)
    {sa sb : State} (hx : sa.exit = none) (hra : sa.reg 1 = s0.reg 1) (hpb : sb.pc = e.pb)
    (hpa : sa.pc = e.pa) (hag : Agree e.live sa sb) {sb' : State} (hst : Step cB P sb sb') :
    ∃ sa', Step cA P sa sa' ∧ Rel k s0 sa' sb' := by
  have hu := uses_live hf
  have hiA : cA.instr sa.pc = some i := hpa ▸ hf.instrA
  have hk := hf.kind
  -- the next pair, for an instruction that falls through
  have next : ∀ {sa' sb' : State} {L : List Reg}, (∃ e' ∈ k.points, e'.pb = e.pb + 4 ∧ e'.pa = e.pa + 4 ∧
      i.transfer e'.live e.live) → sa'.exit = none → sa'.reg 1 = s0.reg 1 → sa'.pc = sa.pc + 4 →
      sb'.pc = sb.pc + 4 → (∀ {e' : Pair}, i.transfer e'.live e.live → Agree e'.live sa' sb') →
      Rel k s0 sa' sb' := by
    intro sa' sb' _ ⟨e', he', hb', ha', ht⟩ hx' hra' hpa' hpb' hag'
    exact .inl ⟨hx', hra', e', he', by rw [hpb', hpb, hb'], by rw [hpa', hpa, ha'], hag' ht⟩
  cases hst with
  | sys hxb hib hokb hsys =>
    rw [hpb, hf.instrB] at hib; cases hib
    simp only [kindOk] at hk
    obtain ⟨e', he', hb', ha', ht⟩ := succOk_sound hk
    obtain ⟨sa', hsa, hag', hpa', hpb'⟩ := sys_congr ht hag hsys
    refine ⟨sa', .sys hx hiA ((instrOk_congr (i := .ecall) hu hag).2 hokb) hsa, ?_⟩
    rcases sys_exit_or hsa with h | h
    · rw [hx] at h
      exact .inl ⟨h, (sys_reg_ra hsa).trans hra, e', he', by rw [hpb' (hag'.exit ▸ h), hpb, hb'],
        by rw [hpa' h, hpa, ha'], hag'⟩
    · exact .inr (.inr ⟨h, hag'.mono (fun _ h => by simp at h)⟩)
  | exec hxb hib hokb hexb =>
    rw [hpb, hf.instrB] at hib; cases hib
    have hokA : InstrOk P i sa := (instrOk_congr hu hag).2 hokb
    have hraexec : ∀ {s s' : State}, exec i s = some s' → s'.reg 1 = s.reg 1 :=
      fun h => exec_reg_of_not_def hf.noRa h
    cases i with
    | ecall => simp [exec_ecall] at hexb
    | branch op a b off =>
      simp only [kindOk, Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨⟨⟨⟨_, hn⟩, halb⟩, hala⟩, htk⟩ := hk
      have hbr := evalBr_congr (op := op) (a := a) (b := b) (by simpa [Instr.uses] using hu) hag
      simp only [exec, jumpTo] at hexb
      by_cases hc : evalBr op (sb.reg a) (sb.reg b) = true
      · rw [hpb] at hexb; simp only [hc, halb, ite_true, Option.some.injEq] at hexb; subst hexb
        obtain ⟨e', he', hb', ha', ht⟩ := succOk_sound htk
        refine ⟨sa.setPc (e.pa + off.signExtend 64), .exec hx hiA hokA ?_, .inl ⟨hx, hra, e', he',
          by simp [hb'], by simp [ha'], ?_⟩⟩
        · simp only [exec, jumpTo, hbr, hc, hpa, hala, ite_true]
        · exact (hag.mono (fun r hr => ht.2 r hr (by simp [Instr.defs]))).setPc _ _
      · simp only [hc, ite_false, Option.some.injEq, Bool.false_eq_true] at hexb; subst hexb
        obtain ⟨e', he', hb', ha', ht⟩ := succOk_sound hn
        refine ⟨sa.setPc (sa.pc + 4), .exec hx hiA hokA ?_, .inl ⟨hx, hra, e', he',
          by simp [hb', hpb], by simp [ha', hpa], ?_⟩⟩
        · simp only [exec, jumpTo, hbr, hc, ite_false, Bool.false_eq_true]
        · exact (hag.mono (fun r hr => ht.2 r hr (by simp [Instr.defs]))).setPc _ _
    | jal rd off =>
      simp only [kindOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hk
      obtain ⟨⟨⟨rfl, halb⟩, hala⟩, htk⟩ := hk
      have e0 : ∀ (u : State) v, u.setReg 0 v = u := fun u v => by simp [State.setReg]
      simp only [exec, jumpTo, e0, hpb, halb, ite_true, Option.some.injEq] at hexb; subst hexb
      obtain ⟨e', he', hb', ha', ht⟩ := succOk_sound htk
      refine ⟨sa.setPc (e.pa + off.signExtend 64), .exec hx hiA hokA ?_, .inl ⟨hx, hra, e', he',
        by simp [hb'], by simp [ha'], ?_⟩⟩
      · simp only [exec, jumpTo, e0, hpa, hala, ite_true]
      · exact (hag.mono0 (fun r hr h0 => ht.2 r hr (by simp [Instr.defs, h0]))).setPc _ _
    | jalr rd rs1 off =>
      simp only [kindOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at hk
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hobs⟩ := hk
      have e0 : ∀ (u : State) v, u.setReg 0 v = u := fun u v => by simp [State.setReg]
      have h1 : sb.reg 1 = sa.reg 1 := (hag.regs 1 (hobs 1 (by simp [obsRegs]))).symm
      have hz : ∀ x : Word, x + BitVec.signExtend 64 (0 : BitVec 12) = x := fun x => by
        rw [show BitVec.signExtend 64 (0 : BitVec 12) = 0 by decide]; bv_omega
      simp only [exec, jumpTo, e0, hz] at hexb
      split at hexb
      · rename_i halb
        simp only [Option.some.injEq] at hexb; subst hexb
        have halb' := halb; rw [h1] at halb'
        refine ⟨sa.setPc ((sa.reg 1) &&& ~~~1), .exec hx hiA hokA ?_, .inr (.inl ⟨hx, ?_, ?_, ?_⟩)⟩
        · simp only [exec, jumpTo, e0, hz, halb', ite_true]
        · simp only [State.setPc_pc]; rw [hra, and_not_one_of_aligned hral]
        · simp only [State.setPc_pc]; rw [h1, hra, and_not_one_of_aligned hral]
        · exact (hag.mono hobs).setPc _ _
      · simp at hexb
    | auipc => simp [kindOk] at hk
    | _ =>
      simp only [kindOk] at hk
      obtain ⟨e', he', hb', ha', ht⟩ := succOk_sound hk
      obtain ⟨hnone, hres⟩ := exec_congr rfl ht hag
      cases hexa : exec _ sa with
      | none => rw [hnone.1 hexa] at hexb; cases hexb
      | some sa' =>
        obtain ⟨hag', hpa', hpb'⟩ := hres sa' sb' hexa hexb
        exact ⟨sa', .exec hx hiA hokA hexa, .inl ⟨(exec_exit hexa).trans hx, (hraexec hexa).trans hra,
          e', he', by rw [hpb', hpb, hb'], by rw [hpa', hpa, ha'], hag'⟩⟩

/-- Where A can step from a pair, B can. -/
theorem progress_pair {P : Perm} {e : Pair} {i : Instr} (hf : PairFacts cA cB DA DB k e i)
    {sa sb : State} (hpb : sb.pc = e.pb) (hpa : sa.pc = e.pa) (hag : Agree e.live sa sb)
    {sa' : State} (hst : Step cA P sa sa') : ∃ sb', Step cB P sb sb' := by
  have hu := uses_live hf
  have hiB : cB.instr sb.pc = some i := hpb ▸ hf.instrB
  have hxb : sb.exit = none := by
    obtain ⟨_, _, _, hx⟩ := hst.instrOk; rw [← hag.exit]; exact hx
  have hk := hf.kind
  cases hst with
  | sys hx hia hoka hsys =>
    rw [hpa, hf.instrA] at hia; cases hia
    obtain ⟨sb', hsb, _⟩ := sys_congr (L := []) ⟨hu, fun _ h => by simp at h⟩ hag.symm hsys
    exact ⟨sb', .sys hxb hiB ((instrOk_congr (i := .ecall) hu hag).1 hoka) hsb⟩
  | exec hx hia hoka hexa =>
    rw [hpa, hf.instrA] at hia; cases hia
    have hokB : InstrOk P i sb := (instrOk_congr hu hag).1 hoka
    suffices h : ∃ sb', exec i sb = some sb' from
      let ⟨sb', h⟩ := h; ⟨sb', .exec hxb hiB hokB h⟩
    cases i with
    | ecall => simp [exec_ecall] at hexa
    | auipc => simp [kindOk] at hk
    | branch op a b off =>
      simp only [kindOk, Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨⟨⟨_, halb⟩, _⟩, _⟩ := hk
      simp only [exec, jumpTo, hpb, halb, ite_true]
      split <;> exact ⟨_, rfl⟩
    | jal rd off =>
      simp only [kindOk, Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨⟨⟨_, halb⟩, _⟩, _⟩ := hk
      simp only [exec, jumpTo, hpb, halb, ite_true]
      exact ⟨_, rfl⟩
    | jalr rd rs1 off =>
      simp only [kindOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at hk
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hobs⟩ := hk
      have h1 : sa.reg 1 = sb.reg 1 := hag.regs 1 (hobs 1 (by simp [obsRegs]))
      simp only [exec, jumpTo] at hexa ⊢
      rw [← h1]
      split at hexa
      · rename_i h; simp only [h, ite_true]; exact ⟨_, rfl⟩
      · simp at hexa
    | _ =>
      simp only [kindOk] at hk
      obtain ⟨e', _, _, _, ht⟩ := succOk_sound hk
      obtain ⟨hnone, _⟩ := exec_congr rfl ht hag
      cases h : exec _ sb with
      | none => rw [← hnone] at h; rw [h] at hexa; cases hexa
      | some sb' => exact ⟨sb', rfl⟩

/-- One B step from a jump pair is matched by one A step. -/
theorem step_jpair {P : Perm} {s0 : State} {e : Pair} {ia ib : Instr}
    (hf : JumpFacts cA cB DA DB k e ia ib)
    {sa sb : State} (hx : sa.exit = none) (hra : sa.reg 1 = s0.reg 1) (hpb : sb.pc = e.pb)
    (hpa : sa.pc = e.pa) (hag : Agree e.live sa sb) {sb' : State} (hst : Step cB P sb sb') :
    ∃ sa', Step cA P sa sa' ∧ Rel k s0 sa' sb' := by
  have hiA : cA.instr sa.pc = some ia := hpa ▸ hf.instrA
  have hk := hf.kind
  have e0 : ∀ (u : State) v, u.setReg 0 v = u := fun u v => by simp [State.setReg]
  cases hst with
  | sys _ hib _ _ =>
    rw [hpb, hf.instrB] at hib; cases hib
    cases ia <;> simp [jumpOk] at hk
  | exec hxb hib hokb hexb =>
    rw [hpb, hf.instrB] at hib; cases hib
    cases ia <;> cases ib <;> simp only [jumpOk, Bool.false_eq_true] at hk
    case branch.branch op a b offA op' a' b' offB =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem]
        at hk
      obtain ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hu⟩, hn⟩, halb⟩, hala⟩, htk⟩ := hk
      have hbr := evalBr_congr (op := op) (a := a) (b := b) (by simpa [Instr.uses] using hu) hag
      simp only [exec, jumpTo] at hexb
      by_cases hc : evalBr op (sb.reg a) (sb.reg b) = true
      · rw [hpb] at hexb; simp only [hc, halb, ite_true, Option.some.injEq] at hexb; subst hexb
        obtain ⟨e', he', hb', ha', ht⟩ := succOk_sound htk
        refine ⟨sa.setPc (e.pa + offA.signExtend 64), .exec hx hiA trivial ?_, .inl ⟨hx, hra, e', he',
          by simp [hb'], by simp [ha'], ?_⟩⟩
        · simp only [exec, jumpTo, hbr, hc, hpa, hala, ite_true]
        · exact (hag.mono (fun r hr => ht.2 r hr (by simp [Instr.defs]))).setPc _ _
      · simp only [hc, ite_false, Option.some.injEq, Bool.false_eq_true] at hexb; subst hexb
        obtain ⟨e', he', hb', ha', ht⟩ := succOk_sound hn
        refine ⟨sa.setPc (sa.pc + 4), .exec hx hiA trivial ?_, .inl ⟨hx, hra, e', he',
          by simp [hb', hpb], by simp [ha', hpa], ?_⟩⟩
        · simp only [exec, jumpTo, hbr, hc, ite_false, Bool.false_eq_true]
        · exact (hag.mono (fun r hr => ht.2 r hr (by simp [Instr.defs]))).setPc _ _
    case jal.jal rdA offA rdB offB =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
      obtain ⟨⟨⟨⟨rfl, rfl⟩, halb⟩, hala⟩, htk⟩ := hk
      simp only [exec, jumpTo, e0, hpb, halb, ite_true, Option.some.injEq] at hexb; subst hexb
      obtain ⟨e', he', hb', ha', ht⟩ := succOk_sound htk
      refine ⟨sa.setPc (e.pa + offA.signExtend 64), .exec hx hiA trivial ?_, .inl ⟨hx, hra, e', he',
        by simp [hb'], by simp [ha'], ?_⟩⟩
      · simp only [exec, jumpTo, e0, hpa, hala, ite_true]
      · exact (hag.mono0 (fun r hr h0 => ht.2 r hr (by simp [Instr.defs, h0]))).setPc _ _

/-- Where A can step from a jump pair, B can. -/
theorem progress_jpair {P : Perm} {e : Pair} {ia ib : Instr} (hf : JumpFacts cA cB DA DB k e ia ib)
    {sa sb : State} (hpb : sb.pc = e.pb) (hag : Agree e.live sa sb)
    {sa' : State} (hst : Step cA P sa sa') : ∃ sb', Step cB P sb sb' := by
  have hiB : cB.instr sb.pc = some ib := hpb ▸ hf.instrB
  have hxb : sb.exit = none := by
    obtain ⟨_, _, _, hx⟩ := hst.instrOk; rw [← hag.exit]; exact hx
  have hk := hf.kind
  have e0 : ∀ (u : State) v, u.setReg 0 v = u := fun u v => by simp [State.setReg]
  cases ia <;> cases ib <;> simp only [jumpOk, Bool.false_eq_true] at hk
  case branch.branch op a b offA op' a' b' offB =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨⟨⟨_, halb⟩, _⟩, _⟩ := hk
    refine ⟨_, .exec hxb hiB trivial (s' := if evalBr op' (sb.reg a') (sb.reg b') then
      sb.setPc (sb.pc + offB.signExtend 64) else sb.setPc (sb.pc + 4)) ?_⟩
    simp only [exec, jumpTo, hpb, halb, ite_true]
    split <;> rfl
  case jal.jal rdA offA rdB offB =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
    obtain ⟨⟨⟨⟨_, rfl⟩, halb⟩, _⟩, _⟩ := hk
    refine ⟨sb.setPc (sb.pc + offB.signExtend 64), .exec hxb hiB trivial ?_⟩
    simp only [exec, jumpTo, e0, hpb, halb, ite_true]

theorem shapeOk_facts {r : RRegion} (h : r.shapeOk DA DB = true) :
    r.domB.mem r.pb ∧ r.domA.mem r.pa ∧ ¬ r.domB.mem r.pbExit ∧ ¬ r.domA.mem r.paExit ∧
      r.domB.sub DB ∧ r.domA.sub DA := by
  unfold RRegion.shapeOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, Dom.sub_of_rangeIn h5, Dom.sub_of_rangeIn h6⟩

/-- Soundness of the certificate check: a certificate whose regions are all
    proved gives `RefinesRel sp A B`, for every specification. -/
theorem _root_.NoCompiler.RefinesRel.of_cert {α : Type} {sp : Spec α} {eA eB : Word}
    (hc : check cA cB DA DB eA eB k = true) (hreg : ∀ r ∈ k.regions, r.Ok cA cB) :
    RefinesRel sp cA DA eA cB DB eB := by
  unfold check at hc
  simp only [Bool.and_eq_true, List.all_eq_true, Option.isSome_iff_exists] at hc
  obtain ⟨⟨hall, hrall⟩, e0, he0⟩ := hc
  obtain ⟨hm0, hb0, ha0⟩ := Cert.find_some he0
  have facts : ∀ e ∈ k.pairs, (∃ i, PairFacts cA cB DA DB k e i) ∨ ∃ ia ib, JumpFacts cA cB DA DB k e ia ib :=
    fun e he => pairOk_facts (hall e he)
  -- a point is a pair or a region's entry
  have point : ∀ e ∈ k.points, e ∈ k.pairs ∨ ∃ r ∈ k.regions, e = ⟨r.pb, r.pa, r.liveIn⟩ := by
    intro e he
    simp only [Cert.points, List.mem_append, List.mem_map] at he
    rcases he with h | ⟨r, hr, rfl⟩
    · exact .inl h
    · exact .inr ⟨r, hr, rfl⟩
  have pointMem : ∀ e ∈ k.points, DB.mem e.pb ∧ DA.mem e.pa := by
    intro e he
    rcases point e he with h | ⟨r, hr, rfl⟩
    · rcases facts e h with ⟨i, hfi⟩ | ⟨ia, ib, hfi⟩
      · exact ⟨hfi.memB, hfi.memA⟩
      · exact ⟨hfi.memB, hfi.memA⟩
    · simp only [regionOk, Bool.and_eq_true] at hrall
      obtain ⟨h1, h2, _, _, h5, h6⟩ := shapeOk_facts (hrall r hr).1
      exact ⟨h5 _ h1, h6 _ h2⟩
  refine RefinesRel.of_bigSim (fun _ s => Rel k s) (fun a s he hraB _ => ?_)
    (fun a s he _ => .inl ⟨he.live, rfl, e0, hm0, by simp [hb0], by rw [he.pc, ha0],
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩)
  have hraA := he.ret
  have hral := he.retAligned
  refine ⟨?fin, ?move⟩
  · intro sa sb hr hf
    rcases hr with ⟨hx, _, e, he, hpb, _, hag⟩ | ⟨hx, hpa, hpb, hag⟩ | ⟨hx, hag⟩
    · exfalso
      rcases hf with h | h
      · exact h (hpb ▸ (pointMem e he).1)
      · exact h (hag.exit ▸ hx)
    · refine ⟨sa, .refl _, .inl (hpa ▸ hraA), hag.trace, hag.exit, fun _ => ⟨hpa.trans hpb.symm,
        fun r hr => hag.regs r (List.mem_cons_of_mem _ hr), fun x _ => by rw [hag.mem]⟩⟩
    · exact ⟨sa, .refl _, .inr hx, hag.trace, hag.exit, fun h => absurd h hx⟩
  · intro sa sb hr hf hA
    rcases hr with ⟨hx, hra, e, he, hpb, hpa, hag⟩ | ⟨_, _, hpb, _⟩ | ⟨hx, hag⟩
    · rcases point e he with hp | ⟨r, hr, rfl⟩
      · -- a pair: one step of each
        have hdAB : DA.mem sa.pc ∧ DB.mem sb.pc := by
          rcases facts e hp with ⟨i, hfi⟩ | ⟨ia, ib, hfi⟩
          · exact ⟨hpa ▸ hfi.memA, hpb ▸ hfi.memB⟩
          · exact ⟨hpa ▸ hfi.memA, hpb ▸ hfi.memB⟩
        obtain ⟨hdA, hdB⟩ := hdAB
        cases hA with
        | done hq =>
          rcases hq.1 with h | h
          · exact absurd hdA h
          · exact absurd hx h
        | step _ hex _ =>
          obtain ⟨sa₁, hst⟩ := hex
          rcases facts e hp with ⟨i, hfi⟩ | ⟨ia, ib, hfi⟩
          · refine .step hdB (progress_pair hfi hpb hpa hag hst) (fun sb' h' => ?_)
            obtain ⟨sa', hsa, hr'⟩ := step_pair hral hfi hx hra hpb hpa hag h'
            exact .done ⟨sa', ⟨sa', hdA, hsa, .refl _⟩, hr'⟩
          · refine .step hdB (progress_jpair hfi hpb hag hst) (fun sb' h' => ?_)
            obtain ⟨sa', hsa, hr'⟩ := step_jpair hfi hx hra hpb hpa hag h'
            exact .done ⟨sa', ⟨sa', hdA, hsa, .refl _⟩, hr'⟩
      · -- a region: its proof
        simp only [regionOk, Bool.and_eq_true] at hrall
        obtain ⟨hrs, hexit⟩ := hrall r hr
        obtain ⟨h1, h2, _, h4, h5, h6⟩ := shapeOk_facts hrs
        split at hexit
        · rename_i e' he'
          obtain ⟨hm', hb', ha'⟩ := Cert.find_some he'
          simp only [List.all_eq_true, List.contains_iff_mem] at hexit
          have hB := hreg r hr _ sa sb hx hpa hpb hag trivial (hA.restrict h6)
          refine Reach.bind hB (Perm.le_refl _) h5 (fun tb ⟨_, ta, hrun, hfa, hex⟩ => ?_)
          -- A's run leaves the region, so it took at least one step
          have hplus : RunPlus cA (sp.perm a s) DA sa ta := by
            cases hrun with
            | refl =>
              exfalso; rcases hfa with h | h
              · exact h (hpa ▸ h2)
              · exact h hx
            | step hd hs hrun' => exact ⟨_, h6 _ hd, hs, hrun'.mono_dom h6⟩
          refine .done ⟨ta, hplus, ?_⟩
          rcases hex with ⟨hxa, hpa', hpb', hra', hag'⟩ | ⟨hxa, hag'⟩
          · exact .inl ⟨hxa, hra'.trans hra, e', hm', by rw [hpb', hb'], by rw [hpa', ha'],
              hag'.mono hexit⟩
          · exact .inr (.inr ⟨hxa, hag'⟩)
        · simp at hexit
    · exact absurd (.inl (hpb ▸ hraB)) hf
    · exact absurd (.inr (hag.exit ▸ hx)) hf

/-- `Refines` from A's run, a checked certificate, and its regions' proofs. -/
theorem _root_.NoCompiler.Refines.of_cert {α : Type} {sp : Spec α} {eA eB : Word}
    (hA : ARuns sp cA DA eA) (hc : check cA cB DA DB eA eB k = true)
    (hreg : ∀ r ∈ k.regions, r.Ok cA cB) : Refines sp cA DA eA cB DB eB :=
  ⟨hA, RefinesRel.of_cert hc hreg⟩

/-- A certificate without regions: lockstep. -/
theorem _root_.NoCompiler.Refines.of_lockstep {α : Type} {sp : Spec α} {eA eB : Word}
    (hA : ARuns sp cA DA eA) (hc : check cA cB DA DB eA eB ⟨k.pairs, []⟩ = true) :
    Refines sp cA DA eA cB DB eB :=
  Refines.of_cert hA hc (fun _ h => by simp at h)

end

end Lockstep
end NoCompiler
