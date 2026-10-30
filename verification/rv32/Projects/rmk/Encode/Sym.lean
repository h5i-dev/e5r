/-
  Symbolic execution of RV32 code on the pinned RMK image, with a soundness proof against the
  model's own `stepInstr`.

  Original e5r code, Apache-2.0.

  A symbolic state `AS` has a concrete pc. Its registers are expressions `SE` over the entry
  registers `R` and the entry RAM `M`, and its memory is the entry RAM under a list of symbolic
  writes. Addresses are linear in the entry sp (register 2), whose value is only known to lie in
  `[E.lo, E.hi]` and to be 4-aligned. `astep` executes one instruction from a fetch table that the
  kernel checks against the packed ELF. A branch whose outcome depends on unknown data has two
  successors. Every case that cannot be decided returns `none`.

  `check` explores the finite tree of successors until a decidable `leaf` test holds.
  `check_sound` turns `check ... = true`, evaluated by the kernel, into `Lands`:
  * the behaviour holds for every concrete machine related to the entry state, i.e. every sp in
    the range and every value of the unknown registers and RAM;
  * no successor faults, under any oracle;
  * the CSRs never change.
-/
import Projects.rmk.Fetch
import Projects.rmk.Trees

set_option maxRecDepth 100000

namespace E5R.Rmk.Sym
open E5R E5R.Rmk

/-! ## Symbolic values -/

inductive SE where
  | c (w : Word)
  | reg (r : Nat)
  | ld (w : Width) (a : SE)
  | alu (op : AluOp) (a b : SE)
  | ext (w : Width) (s : Bool) (a : SE)
  deriving DecidableEq

/-- Value under the entry registers `R` and entry RAM `M`. -/
def SE.eval (R : Nat → Word) (M : Word → BitVec 8) : SE → Word
  | .c w => w
  | .reg r => R r
  | .ld w a => ramRead M (a.eval R M) w
  | .alu op a b => E5R.alu op (a.eval R M) (b.eval R M)
  | .ext w s a => extend w s (a.eval R M)

/-- `base + off`, base absent (`none`) or an entry register. -/
def SE.lin : SE → Option (Option Nat × Word)
  | .c w => some (none, w)
  | .reg r => some (some r, 0)
  | .alu .add a b =>
    match a.lin, b.lin with
    | some (none, x), some (q, y) => some (q, x + y)
    | some (q, x), some (none, y) => some (q, x + y)
    | _, _ => none
  | _ => none

def baseVal (R : Nat → Word) : Option Nat → Word
  | none => 0
  | some r => R r

theorem lin_sound (R : Nat → Word) (M : Word → BitVec 8) :
    ∀ (e : SE) (q : Option Nat) (o : Word), e.lin = some (q, o) → e.eval R M = baseVal R q + o := by
  intro e
  induction e with
  | c w => intro q o h; simp only [SE.lin, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl⟩ := h; simp [SE.eval, baseVal]
  | reg r => intro q o h; simp only [SE.lin, Option.some.injEq, Prod.mk.injEq] at h
             obtain ⟨rfl, rfl⟩ := h; simp [SE.eval, baseVal]
  | ld w a _ => intro q o h; simp [SE.lin] at h
  | ext w s a _ => intro q o h; simp [SE.lin] at h
  | alu op a b iha ihb =>
    intro q o h
    cases op <;> simp only [SE.lin, reduceCtorEq] at h
    rcases ha : a.lin with _ | ⟨qa, x⟩
    · rw [ha] at h; simp at h
    rcases hb : b.lin with _ | ⟨qb, y⟩
    · rw [ha, hb] at h; cases qa <;> simp at h
    rw [ha, hb] at h
    have ea := iha _ _ ha
    have eb := ihb _ _ hb
    show E5R.alu .add (a.eval R M) (b.eval R M) = _
    rw [ea, eb]
    simp only [E5R.alu]
    cases qa with
    | none =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [baseVal, BitVec.zero_add]; ac_rfl
    | some r =>
      cases qb with
      | none =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [baseVal, BitVec.zero_add]; ac_rfl
      | some r' => simp at h

def mkLin : Option Nat × Word → SE
  | (none, o) => .c o
  | (some r, o) => if o = 0 then .reg r else .alu .add (.reg r) (.c o)

theorem mkLin_eval (R : Nat → Word) (M : Word → BitVec 8) (p : Option Nat × Word) :
    (mkLin p).eval R M = baseVal R p.1 + p.2 := by
  obtain ⟨q, o⟩ := p
  cases q with
  | none => simp [mkLin, SE.eval, baseVal]
  | some r =>
    simp only [mkLin]
    split
    · rename_i h; subst h; simp [SE.eval, baseVal]
    · simp [SE.eval, baseVal, E5R.alu]

/-- A symbolic ALU result: folded when both operands are known, kept linear when possible. -/
def aluS (op : AluOp) (a b : SE) : SE :=
  match a, b with
  | .c x, .c y => .c (E5R.alu op x y)
  | _, _ =>
    match (SE.alu op a b).lin with
    | some p => mkLin p
    | none => .alu op a b

theorem aluS_eval (R : Nat → Word) (M : Word → BitVec 8) (op : AluOp) (a b : SE) :
    (aluS op a b).eval R M = E5R.alu op (a.eval R M) (b.eval R M) := by
  unfold aluS
  split
  · rfl
  · split
    · rename_i p hp
      rw [mkLin_eval, ← lin_sound R M _ p.1 p.2 hp]; rfl
    · rfl

/-- A symbolic `extend`. -/
def extS (w : Width) (s : Bool) (a : SE) : SE :=
  match a with
  | .c x => .c (extend w s x)
  | _ => match w with
    | .w => a
    | _ => .ext w s a

theorem extS_eval (R : Nat → Word) (M : Word → BitVec 8) (w : Width) (s : Bool) (a : SE) :
    (extS w s a).eval R M = extend w s (a.eval R M) := by
  unfold extS
  split
  · rfl
  · cases w <;> cases s <;> rfl

/-! ## Branch outcomes -/

def decT (cnd : BrCond) (a b : SE) : Option Bool :=
  match a, b with
  | .c x, .c y => some (taken cnd x y)
  | _, _ => if a = b then some (taken cnd 0 0) else none

theorem taken_self (cnd : BrCond) (x : Word) : taken cnd x x = taken cnd 0 0 := by
  cases cnd <;> simp [taken, BitVec.slt, BitVec.ult]

theorem decT_sound (R : Nat → Word) (M : Word → BitVec 8) (cnd : BrCond) (a b : SE) (t : Bool)
    (h : decT cnd a b = some t) : taken cnd (a.eval R M) (b.eval R M) = t := by
  unfold decT at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · split at h
    · rename_i e; subst e; simp only [Option.some.injEq] at h; subst h; exact taken_self _ _
    · simp at h

/-! ## Addresses as natural numbers -/

/-- Bounds on the entry sp (register 2). -/
structure Env where
  lo : Nat
  hi : Nat

def soff (o : Word) : Int := if o.toNat < 2 ^ 31 then o.toNat else (o.toNat : Int) - 2 ^ 32

/-- Byte `j < n` of `a` is at `(sp if s else 0) + k + j`, without wrap-around, for every sp in
    the range. -/
def nform (E : Env) (a : SE) (n : Nat) : Option (Bool × Int) :=
  match a.lin with
  | some (none, o) => if o.toNat + n ≤ 2 ^ 32 then some (false, o.toNat) else none
  | some (some 2, o) =>
    if 0 ≤ (E.lo : Int) + soff o ∧ (E.hi : Int) + soff o + n ≤ 2 ^ 32 then some (true, soff o) else none
  | _ => none

def SpIn (E : Env) (R : Nat → Word) : Prop := E.lo ≤ (R 2).toNat ∧ (R 2).toNat ≤ E.hi

theorem nform_sound {E : Env} {R : Nat → Word} {M : Word → BitVec 8} (hE : SpIn E R) {a : SE} {n : Nat}
    {s : Bool} {k : Int} (h : nform E a n = some (s, k)) :
    ∀ j < n, (((a.eval R M + BitVec.ofNat 32 j).toNat : Nat) : Int) =
      (if s then ((R 2).toNat : Int) else 0) + k + j := by
  intro j hj
  unfold nform at h
  split at h
  · rename_i o hl
    split at h
    · rename_i hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [lin_sound R M a _ _ hl]
      have hz : (0 : Word).toNat = 0 := rfl
      simp only [baseVal, BitVec.toNat_add, BitVec.toNat_ofNat, Bool.false_eq_true, ite_false, hz]
      have := o.isLt
      omega
    · simp at h
  · rename_i o hl
    split at h
    · rename_i hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [lin_sound R M a _ _ hl]
      simp only [baseVal, BitVec.toNat_add, BitVec.toNat_ofNat, ite_true]
      have h1 := hE.1; have h2 := hE.2
      have := o.isLt; have := (R 2).isLt
      unfold soff at hb ⊢
      split at hb <;> simp_all <;> omega
    · simp at h
  · simp at h

/-- Disjoint byte ranges. -/
def disj (E : Env) (a : SE) (n : Nat) (b : SE) (m : Nat) : Bool :=
  match nform E a n, nform E b m with
  | some (s1, k1), some (s2, k2) =>
    if s1 = s2 then decide (k1 + n ≤ k2 ∨ k2 + m ≤ k1)
    else if s1 then decide ((E.hi : Int) + k1 + n ≤ k2 ∨ k2 + m ≤ (E.lo : Int) + k1)
    else decide ((E.hi : Int) + k2 + m ≤ k1 ∨ k1 + n ≤ (E.lo : Int) + k2)
  | _, _ => false

theorem disj_sound {E : Env} {R : Nat → Word} {M : Word → BitVec 8} (hE : SpIn E R) {a b : SE}
    {n m : Nat} (h : disj E a n b m = true) :
    ∀ i < n, ∀ j < m, a.eval R M + BitVec.ofNat 32 i ≠ b.eval R M + BitVec.ofNat 32 j := by
  intro i hi j hj he
  unfold disj at h
  split at h
  · rename_i s1 k1 s2 k2 ha hb
    have e1 := nform_sound (M := M) hE ha i hi
    have e2 := nform_sound (M := M) hE hb j hj
    rw [he] at e1
    have h1 := hE.1; have h2 := hE.2
    cases s1 <;> cases s2 <;> simp at h e1 e2 <;> omega
  · simp at h

/-! ## RAM and alignment checks -/

theorem B_inRam (a : Word) (n : Nat) :
    B.inRam a n = true ↔ 0x80029bc8 ≤ a.toNat ∧ a.toNat + n ≤ 0x81000000 := by
  rw [Board.inRam_iff]; simp [QemuVirtRv32.board, QemuVirtRv32.dramEnd]

def inRamC (E : Env) (a : SE) (n : Nat) : Bool :=
  match nform E a n with
  | some (true, k) => decide (0x80029bc8 ≤ (E.lo : Int) + k ∧ (E.hi : Int) + k + n ≤ 0x81000000)
  | some (false, k) => decide (0x80029bc8 ≤ k ∧ k + n ≤ 0x81000000)
  | none => false

theorem inRamC_sound {E : Env} {R : Nat → Word} {M : Word → BitVec 8} (hE : SpIn E R) {a : SE} {n : Nat}
    (hn : 0 < n) (h : inRamC E a n = true) : B.inRam (a.eval R M) n = true := by
  rw [B_inRam]
  unfold inRamC at h
  have h1 := hE.1; have h2 := hE.2
  split at h
  · rename_i k hk
    have e := nform_sound (M := M) hE hk 0 hn
    simp only [BitVec.add_zero, ite_true] at e
    simp only [decide_eq_true_eq] at h
    omega
  · rename_i k hk
    have e := nform_sound (M := M) hE hk 0 hn
    simp only [BitVec.add_zero, Bool.false_eq_true, ite_false] at e
    simp only [decide_eq_true_eq] at h
    omega
  · simp at h

/-- A constant address outside RAM. -/
def outRamC (a : SE) (n : Nat) : Bool :=
  match a with
  | .c x => !B.inRam x n
  | _ => false

def alC (E : Env) (a : SE) (w : Width) : Bool :=
  match nform E a w.bytes with
  | some (_, k) => decide (k % 4 % (w.bytes : Int) = 0)
  | none => false

theorem alC_sound {E : Env} {R : Nat → Word} {M : Word → BitVec 8} (hE : SpIn E R) (hsp : (R 2).toNat % 4 = 0)
    {a : SE} {w : Width} (h : alC E a w = true) : (a.eval R M).toNat % w.bytes = 0 := by
  unfold alC at h
  split at h
  · rename_i s k hk
    have e := nform_sound (M := M) hE hk 0 (by cases w <;> decide)
    simp only [BitVec.add_zero] at e
    simp only [decide_eq_true_eq] at h
    cases w <;> simp only [Width.bytes] at h ⊢ <;> split at e <;> omega
  · simp at h

/-! ## Symbolic memory -/

abbrev Wr := SE × Width × SE

/-- The entry RAM under the writes, newest first. -/
def applyW (R : Nat → Word) (M : Word → BitVec 8) : List Wr → (Word → BitVec 8)
  | [] => M
  | (a, w, v) :: ws => ramWrite (applyW R M ws) (a.eval R M) (v.eval R M) w

theorem ramWrite_other (X : Word → BitVec 8) (a v x : Word) (w : Width)
    (h : ∀ j < w.bytes, x ≠ a + BitVec.ofNat 32 j) : ramWrite X a v w x = X x := by
  have h0 := h 0 (by cases w <;> decide)
  simp only [BitVec.add_zero] at h0
  cases w with
  | b => simp [ramWrite, ramPut, h0]
  | h =>
    have h1 := h 1 (by decide)
    simp [ramWrite, ramPut, h0, h1]
  | w => exact ramWrite_w_other X a v x h

theorem ramRead_congr {X Y : Word → BitVec 8} (a : Word) (w : Width)
    (h : ∀ k < w.bytes, X (a + BitVec.ofNat 32 k) = Y (a + BitVec.ofNat 32 k)) :
    ramRead X a w = ramRead Y a w := by
  have h0 := h 0 (by cases w <;> decide)
  simp only [BitVec.add_zero] at h0
  cases w with
  | b => simp [ramRead, h0]
  | h =>
    have h1 := h 1 (by decide)
    simp [ramRead, h0, h1]
  | w => exact ramRead_w_congr a fun k hk => h k hk

theorem ramRead_ramWrite_b (X : Word → BitVec 8) (a v : Word) :
    ramRead (ramWrite X a v .b) a .b = extend .b false v := by
  simp only [ramRead, ramWrite, ramPut, ite_true, byteOf, extend]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_and, Nat.pow_zero, Nat.div_one]
  have : (0xff : Word).toNat = 255 := rfl
  rw [this, show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem ramRead_ramWrite_h (X : Word → BitVec 8) (a v : Word) :
    ramRead (ramWrite X a v .h) a .h = extend .h false v := by
  have d : a ≠ a + 1 := by
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl] at this
    have := a.isLt
    omega
  simp only [ramRead, ramWrite, ramPut, ite_true, Ne.symm d, d, ite_false, byteOf, extend]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_and, Nat.pow_zero, Nat.div_one, Nat.pow_one]
  have : (0xffff : Word).toNat = 65535 := rfl
  rw [this, show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := v.isLt
  omega

/-- What a load of `w` reads back from a store of `w` at the same address. -/
def trunc (w : Width) (v : SE) : SE :=
  match w with
  | .w => v
  | _ => extS w false v

theorem ramRead_ramWrite_same (X : Word → BitVec 8) (a v : Word) (w : Width) (R : Nat → Word)
    (M : Word → BitVec 8) (e : SE) (he : e.eval R M = v) :
    ramRead (ramWrite X a v w) a w = (trunc w e).eval R M := by
  cases w with
  | b => show _ = (extS .b false e).eval R M; rw [extS_eval, he, ramRead_ramWrite_b]
  | h => show _ = (extS .h false e).eval R M; rw [extS_eval, he, ramRead_ramWrite_h]
  | w => show _ = e.eval R M; rw [he, ramRead_ramWrite_w]

/-- A load from symbolic memory: the newest write if it is exactly the same cell, the entry RAM if
    every write is disjoint; `none` on a partial overlap. -/
def rdW (E : Env) : List Wr → SE → Width → Option SE
  | [], a, w => some (.ld w a)
  | (b, w', v) :: ws, a, w =>
    if b = a ∧ w' = w then some (trunc w v)
    else if disj E b w'.bytes a w.bytes then rdW E ws a w else none

theorem rdW_sound {E : Env} {R : Nat → Word} {M : Word → BitVec 8} (hE : SpIn E R) :
    ∀ (ws : List Wr) (a : SE) (w : Width) (v : SE), rdW E ws a w = some v →
      ramRead (applyW R M ws) (a.eval R M) w = v.eval R M := by
  intro ws
  induction ws with
  | nil => intro a w v h; simp only [rdW, Option.some.injEq] at h; subst h; rfl
  | cons hd ws ih =>
    obtain ⟨b, w', u⟩ := hd
    intro a w v h
    simp only [rdW] at h
    split at h
    · rename_i hh
      obtain ⟨rfl, rfl⟩ := hh
      simp only [Option.some.injEq] at h; subst h
      exact ramRead_ramWrite_same _ _ _ _ R M u rfl
    · split at h
      · rename_i hd
        rw [applyW, ramRead_congr _ _ (Y := applyW R M ws) fun k hk =>
          ramWrite_other _ _ _ _ _ fun j hj e => disj_sound hE hd j hj k hk e.symm]
        exact ih a w v h
      · simp at h

/-! ## Symbolic states -/

structure AS where
  pc : Word
  r : Reg → SE
  mem : List Wr

def AS.get (s : AS) (q : Reg) : SE := if q.val = 0 then .c 0 else s.r q

def AS.set (s : AS) (rd : Reg) (v : SE) : Reg → SE := fun q => if q = rd then v else s.r q

/-- A concrete machine `m` is an instance of `s` (entry registers `R`, entry RAM `M`, the CSRs of
    the entry core `c0`). -/
structure Rel (R : Nat → Word) (M : Word → BitVec 8) (c0 : Core) (s : AS) (m : Machine) : Prop where
  pc : m.core.pc = s.pc
  regs : ∀ q : Reg, m.core.get q = (s.get q).eval R M
  mem : m.ram = applyW R M s.mem
  csr : m.core.sameCsr c0

/-- The fetch table: (pc, instruction, length). -/
abbrev Tbl := List (Word × Instr × Word)

/-- Known read-only words: (address, width, value). -/
abbrev Rom := List (Word × Width × Word)

def loadV (E : Env) (rt : Rom) (ws : List Wr) (a : SE) (w : Width) : Option SE :=
  if alC E a w then
    if inRamC E a w.bytes then rdW E ws a w
    else match a with
      | .c x =>
        if B.inRam x w.bytes then none
        else (rt.find? (fun p => p.1 == x && p.2.1 == w)).map (fun p => .c p.2.2)
      | _ => none
  else none

/-- One symbolic step of instruction `i` (length `len`) at `s.pc`. -/
def astepI (E : Env) (rt : Rom) (s : AS) (i : Instr) (len : Word) : Option (List AS) :=
  let next := s.pc + len
  match i with
  | .lui rd imm => some [⟨next, s.set rd (.c imm), s.mem⟩]
  | .auipc rd imm => some [⟨next, s.set rd (.c (s.pc + imm)), s.mem⟩]
  | .jal rd off =>
    if (s.pc + off).getLsbD 0 then none else some [⟨s.pc + off, s.set rd (.c next), s.mem⟩]
  | .jalr rd rs1 off =>
    match aluS .and (aluS .add (s.get rs1) (.c off)) (.c (~~~1)) with
    | .c t => if t.getLsbD 0 then none else some [⟨t, s.set rd (.c next), s.mem⟩]
    | _ => none
  | .branch cnd rs1 rs2 off =>
    match decT cnd (s.get rs1) (s.get rs2) with
    | some true => if (s.pc + off).getLsbD 0 then none else some [⟨s.pc + off, s.r, s.mem⟩]
    | some false => some [⟨next, s.r, s.mem⟩]
    | none =>
      if (s.pc + off).getLsbD 0 then none else some [⟨s.pc + off, s.r, s.mem⟩, ⟨next, s.r, s.mem⟩]
  | .load w sg rd rs1 off =>
    match loadV E rt s.mem (aluS .add (s.get rs1) (.c off)) w with
    | some v => some [⟨next, s.set rd (extS w sg v), s.mem⟩]
    | none => none
  | .store w rs1 rs2 off =>
    if alC E (aluS .add (s.get rs1) (.c off)) w && inRamC E (aluS .add (s.get rs1) (.c off)) w.bytes then
      some [⟨next, s.r, (aluS .add (s.get rs1) (.c off), w, s.get rs2) :: s.mem⟩]
    else none
  | .opimm op rd rs1 imm => some [⟨next, s.set rd (aluS op (s.get rs1) (.c imm)), s.mem⟩]
  | .op op rd rs1 rs2 => some [⟨next, s.set rd (aluS op (s.get rs1) (s.get rs2)), s.mem⟩]
  | _ => none

/-- One symbolic step: the successor states, or `none` if the step is not supported. -/
def astep (E : Env) (tbl : Tbl) (rt : Rom) (s : AS) : Option (List AS) :=
  match tbl.find? (fun p => p.1 == s.pc) with
  | none => none
  | some p => astepI E rt s p.2.1 p.2.2

/-! ## Soundness of one step -/

section
variable {R : Nat → Word} {M : Word → BitVec 8} {c0 : Core}

theorem Rel.get {s : AS} {m : Machine} (h : Rel R M c0 s m) (q : Reg) : m.core.get q = (s.get q).eval R M :=
  h.regs q

theorem rel_wr {s : AS} {m : Machine} (h : Rel R M c0 s m) (rd : Reg) (e : SE) (v p : Word)
    (he : e.eval R M = v) : Rel R M c0 ⟨p, s.set rd e, s.mem⟩ ⟨m.core.wr rd v p, m.ram⟩ := by
  refine ⟨rfl, fun q => ?_, h.mem, Core.sameCsr_trans (Core.sameCsr_wr _ _ _ _) h.csr⟩
  rw [Core.wr_get]
  simp only [AS.get, AS.set]
  by_cases hq : q.val = 0
  · simp [hq, SE.eval]
  · simp only [hq, ite_false]
    by_cases e' : q = rd
    · simp [e', he]
    · simp only [e', ite_false]
      have := h.regs q
      simp only [AS.get, hq, ite_false] at this
      exact this

theorem rel_goto {s : AS} {m : Machine} (h : Rel R M c0 s m) (p : Word) :
    Rel R M c0 ⟨p, s.r, s.mem⟩ ⟨m.core.goto p, m.ram⟩ :=
  ⟨rfl, fun q => h.regs q, h.mem, Core.sameCsr_trans (Core.sameCsr_goto _ _) h.csr⟩

theorem rel_store {s : AS} {m : Machine} (h : Rel R M c0 s m) (p : Word) (a : SE) (w : Width) (e : SE) :
    Rel R M c0 ⟨p, s.r, (a, w, e) :: s.mem⟩
      ⟨m.core.goto p, ramWrite m.ram (a.eval R M) (e.eval R M) w⟩ :=
  ⟨rfl, fun q => h.regs q, by rw [h.mem]; rfl, Core.sameCsr_trans (Core.sameCsr_goto _ _) h.csr⟩

theorem addr_eval {s : AS} {m : Machine} (h : Rel R M c0 s m) (rs1 : Reg) (off : Word) :
    m.core.get rs1 + off = (aluS .add (s.get rs1) (.c off)).eval R M := by
  rw [aluS_eval, h.regs rs1]; rfl

theorem astepI_sound {E : Env} {rt : Rom} {s : AS} {m : Machine} {i : Instr} {len : Word}
    {succs : List AS} (hE : SpIn E R) (hsp : (R 2).toNat % 4 = 0)
    (hrt : ∀ p ∈ rt, romRead? img p.1.toNat p.2.1.bytes false = some p.2.2)
    (h : Rel R M c0 s m) (hal : m.core.pc.getLsbD 0 = false) (hd : fetchDecode img m.core.pc = some (i, len))
    (hs : astepI E rt s i len = some succs) :
    ∀ o, ∃ c r, stepInstr B img m o = .ok c r [] ∧ ∃ s' ∈ succs, Rel R M c0 s' ⟨c, r⟩ := by
  intro o
  rw [stepInstr_of hal hd]
  have hpc := h.pc
  cases i with
  | lui rd imm =>
    simp only [astepI, Option.some.injEq] at hs; subst hs
    refine ⟨_, _, by rw [exec_lui]; rfl, _, List.mem_singleton_self _, ?_⟩
    rw [hpc]; exact rel_wr h rd _ _ _ rfl
  | auipc rd imm =>
    simp only [astepI, Option.some.injEq] at hs; subst hs
    refine ⟨_, _, by rw [exec_auipc]; rfl, _, List.mem_singleton_self _, ?_⟩
    rw [hpc]; exact rel_wr h rd _ _ _ rfl
  | jal rd off =>
    simp only [astepI] at hs
    split at hs
    · simp at hs
    · rename_i hev
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨_, _, by rw [exec_jal, hpc, jump_ok _ _ (by simpa using hev)]; rfl, _,
        List.mem_singleton_self _, ?_⟩
      exact rel_wr h rd _ _ _ rfl
  | jalr rd rs1 off =>
    simp only [astepI] at hs
    split at hs
    · rename_i t ht
      split at hs
      · simp at hs
      · rename_i hev
        simp only [Option.some.injEq] at hs; subst hs
        have et : (m.core.get rs1 + off) &&& ~~~1 = t := by
          have := congrArg (SE.eval R M) ht
          rw [aluS_eval, aluS_eval, ← h.regs rs1] at this
          exact this
        refine ⟨_, _, by rw [exec_jalr, et, jump_ok _ _ (by simpa using hev)]; rfl, _,
          List.mem_singleton_self _, ?_⟩
        rw [hpc]; exact rel_wr h rd _ _ _ rfl
    · simp at hs
  | branch cnd rs1 rs2 off =>
    simp only [astepI] at hs
    have ht : ∀ t, decT cnd (s.get rs1) (s.get rs2) = some t → taken cnd (m.core.get rs1) (m.core.get rs2) = t :=
      fun t e => by rw [h.regs, h.regs]; exact decT_sound R M _ _ _ t e
    split at hs
    · rename_i hdt
      split at hs
      · simp at hs
      · rename_i hev
        simp only [Option.some.injEq] at hs; subst hs
        refine ⟨_, _, by rw [exec_branch, ht true hdt, if_pos rfl, jump_ok _ _ (by rw [hpc]; simpa using hev)]; rfl,
          _, List.mem_singleton_self _, ?_⟩
        rw [hpc]; exact rel_goto h _
    · rename_i hdt
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨_, _, by rw [exec_branch, ht false hdt]; rfl, _, List.mem_singleton_self _, ?_⟩
      rw [hpc]; exact rel_goto h _
    · split at hs
      · simp at hs
      · rename_i hdt hev
        simp only [Option.some.injEq] at hs; subst hs
        cases htk : taken cnd (m.core.get rs1) (m.core.get rs2)
        · refine ⟨_, _, by rw [exec_branch, htk]; rfl, ⟨s.pc + len, s.r, s.mem⟩, by simp, ?_⟩
          rw [hpc]; exact rel_goto h _
        · refine ⟨_, _, by rw [exec_branch, htk, if_pos rfl, jump_ok _ _ (by rw [hpc]; simpa using hev)]; rfl,
            ⟨s.pc + off, s.r, s.mem⟩, by simp, ?_⟩
          rw [hpc]; exact rel_goto h _
  | load w sg rd rs1 off =>
    simp only [astepI] at hs
    split at hs
    · rename_i v hv
      simp only [Option.some.injEq] at hs; subst hs
      unfold loadV at hv
      split at hv
      · rename_i hA
        have hal' := alC_sound (M := M) hE hsp hA
        rw [← addr_eval h] at hal'
        split at hv
        · rename_i hI
          have hin := inRamC_sound (M := M) hE (by cases w <;> decide) hI
          rw [← addr_eval h] at hin
          have hr := rdW_sound (M := M) hE _ _ _ _ hv
          rw [← addr_eval h, ← h.mem] at hr
          refine ⟨_, _, by rw [exec_load, interp_load_ram o hal' hin]; rfl, _, List.mem_singleton_self _, ?_⟩
          rw [hpc]; exact rel_wr h rd _ _ _ (by rw [extS_eval, ← hr])
        · split at hv
          · rename_i x hx
            split at hv
            · simp at hv
            · rename_i hnin
              cases hf : rt.find? (fun p => p.1 == x && p.2.1 == w) with
              | none => rw [hf] at hv; simp at hv
              | some q =>
                rw [hf] at hv
                simp only [Option.map_some, Option.some.injEq] at hv
                subst hv
                have hq := List.find?_some hf
                simp only [Bool.and_eq_true, beq_iff_eq] at hq
                have hrom := hrt q (List.mem_of_find?_eq_some hf)
                rw [hq.1, hq.2] at hrom
                have ea : m.core.get rs1 + off = x := by
                  rw [addr_eval h]; exact congrArg (SE.eval R M) hx
                rw [ea] at hal'
                refine ⟨_, _, by rw [exec_load, ea, interp_load_rom o hal' (by simpa using hnin) rfl hrom]; rfl,
                  _, List.mem_singleton_self _, ?_⟩
                rw [hpc]; exact rel_wr h rd _ _ _ (by rw [extS_eval]; rfl)
          · simp at hv
      · simp at hv
    · simp at hs
  | store w rs1 rs2 off =>
    simp only [astepI] at hs
    split at hs
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      simp only [Option.some.injEq] at hs; subst hs
      have hal' := alC_sound (M := M) hE hsp hc.1
      have hin := inRamC_sound (M := M) hE (by cases w <;> decide) hc.2
      rw [← addr_eval h] at hal' hin
      refine ⟨_, _, by rw [exec_store, interp_store_ram o hal' hin]; rfl, _, List.mem_singleton_self _, ?_⟩
      have := rel_store h (m.core.pc + len) (aluS .add (s.get rs1) (.c off)) w (s.get rs2)
      rw [← addr_eval h, ← h.regs rs2, hpc] at this
      rw [hpc]; exact this
    · simp at hs
  | opimm op rd rs1 imm =>
    simp only [astepI, Option.some.injEq] at hs; subst hs
    refine ⟨_, _, by rw [exec_opimm]; rfl, _, List.mem_singleton_self _, ?_⟩
    rw [hpc]; exact rel_wr h rd _ _ _ (by rw [aluS_eval, ← h.regs rs1]; rfl)
  | op op rd rs1 rs2 =>
    simp only [astepI, Option.some.injEq] at hs; subst hs
    refine ⟨_, _, by rw [exec_op]; rfl, _, List.mem_singleton_self _, ?_⟩
    rw [hpc]; exact rel_wr h rd _ _ _ (by rw [aluS_eval, ← h.regs rs1, ← h.regs rs2])
  | _ => simp [astepI] at hs

/-! ## The checker -/

def check (E : Env) (tbl : Tbl) (rt : Rom) (leaf : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n+1, s => leaf s || (!s.pc.getLsbD 0 &&
      match astep E tbl rt s with
      | some succs => succs.all (check E tbl rt leaf n)
      | none => false)

theorem check_sound {E : Env} {tbl : Tbl} {rt : Rom} {leaf : AS → Bool} {P : Machine → Prop}
    (hE : SpIn E R) (hsp : (R 2).toNat % 4 = 0)
    (htbl : ∀ p ∈ tbl, fetchDecode img p.1 = some p.2)
    (hrt : ∀ p ∈ rt, romRead? img p.1.toNat p.2.1.bytes false = some p.2.2)
    (hq0 : Quiet c0) (hleaf : ∀ s m, leaf s = true → Rel R M c0 s m → P m) :
    ∀ n s m, Rel R M c0 s m → check E tbl rt leaf n s = true → Lands B img P m := by
  intro n
  induction n with
  | zero => intro s m _ h; simp [check] at h
  | succ n ih =>
    intro s m hr h
    simp only [check, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with h | ⟨hev, h⟩
    · exact .done (hleaf s m h hr)
    · split at h
      · rename_i succs hs
        unfold astep at hs
        split at hs
        · simp at hs
        · rename_i p hp
          have hm := List.mem_of_find?_eq_some hp
          have hq : p.1 = s.pc := by simpa using List.find?_some hp
          have hal : m.core.pc.getLsbD 0 = false := by rw [hr.pc]; exact hev
          have hd : fetchDecode img m.core.pc = some (p.2.1, p.2.2) := by
            rw [hr.pc, ← hq]; exact htbl p hm
          have st := fun o => astepI_sound hE hsp hrt hr hal hd hs o
          have hall := List.all_eq_true.mp h
          refine .step (Quiet.of_sameCsr hr.csr hq0) (fun o f e => ?_) (fun x evs hx => ?_)
          · obtain ⟨c, r, e', _⟩ := st o
            rw [e'] at e; cases e
          · cases hx with
            | instr o ho =>
              obtain ⟨c, r, e', s', hs', hr'⟩ := st o
              rw [e'] at ho
              cases ho
              exact ih s' _ hr' (hall s' hs')
            | irq code he _ =>
              have := Quiet.of_sameCsr hr.csr hq0 code
              rw [this] at he; cases he
      · simp at h

end
