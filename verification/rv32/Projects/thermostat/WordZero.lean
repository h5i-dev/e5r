import Projects.thermostat.ZeroCode
import Projects.thermostat.Memory
set_option linter.unusedSimpArgs false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WordZero
open E5R E5R.Thermostat

def writes (ram : Word → BitVec 8) (p : Word) : Nat → (Word → BitVec 8)
  | 0 => ram
  | n+1 => writes (ramWrite ram p 0#32 .w) (p+4#32) n

theorem turn (B : Board) (c : Core) (ram : Word → BitVec 8) (p e : Word) (b : Bool)
    (hp : c.pc = 0x80005676#32) (h14 : c.get 14 = p) (h13 : c.get 13 = e)
    (h15 : c.get 15 = 0#32) (ha : p.toNat%4 = 0) (hr : B.inRam p 4 = true)
    (ht : taken .ltu (p+4#32) e = b) :
    ∃ d, DetSteps B img 3 ⟨c,ram⟩ ⟨d,ramWrite ram p 0#32 .w⟩ ∧
      d.pc = (if b then 0x80005676#32 else 0x8000567e#32) ∧
      d.get 14 = p+4#32 ∧ (∀ r : Reg, r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram p 0#32 .w
  let c1 := c.goto 0x80005678#32
  let c2 := c1.wr 14 (p+4#32) 0x8000567a#32
  let d := c2.goto (if b then 0x80005676#32 else 0x8000567e#32)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ze2147505782) fun o => ?_
    rw [exec_store,h14,h15,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .w) o ha hr,hp]
    rfl
  have s1 : DetStep B img ⟨c1,r1⟩ ⟨c2,r1⟩ := by
    refine detStep_of (by change (0x80005678#32).getLsbD 0 = false;decide) ze2147505784 fun o => ?_
    have hv : c1.get 14 = p := h14
    rw [exec_opimm,hv]
    rfl
  have s2 : DetStep B img ⟨c2,r1⟩ ⟨d,r1⟩ := by
    refine detStep_of (by change (0x8000567a#32).getLsbD 0 = false;decide) ze2147505786 fun o => ?_
    have h14' : c2.get 14 = p+4#32 := by simp [c2,Core.wr_get]
    have h13' : c2.get 13 = e := by simp [c2,c1,Core.wr_get_ne,h13]
    rw [exec_branch,h14',h13',ht]
    cases b with
    | false => rfl
    | true =>
      simp only [ite_true]
      change interp B img o (jump c2 (0x8000567a#32+0xfffffffc#32)) r1 0 [] = _
      rw [show 0x8000567a#32+0xfffffffc#32 = 0x80005676#32 by decide +kernel]
      rw [jump_ok _ _ (by decide)]
      rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,?_,by rfl⟩
  · simp [d,c2,Core.wr_get]
  · intro r hr
    simp [d,c2,c1,Core.wr_get_ne,hr]

theorem add_nat (p : Word) (k : Nat) (h : p.toNat+k < 2^32) :
    (p+BitVec.ofNat 32 k).toNat = p.toNat+k := by
  rw [BitVec.toNat_add,BitVec.toNat_ofNat]
  have hk : k < 2^32 := by omega
  rw [Nat.mod_eq_of_lt hk,Nat.mod_eq_of_lt h]

theorem loop (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (n : Nat)
    (hn : 0 < n) (hp : c.pc = 0x80005676#32) (h14 : c.get 14 = p)
    (h13 : c.get 13 = p+BitVec.ofNat 32 (4*n)) (h15 : c.get 15 = 0#32)
    (ha : p.toNat%4 = 0) (hm : Memory.Block B p (4*n)) (htop : p.toNat+4*n < 2^32) :
    ∃ d, DetSteps B img (3*n) ⟨c,ram⟩ ⟨d,writes ram p n⟩ ∧
      d.pc = 0x8000567e#32 ∧ d.get 14 = p+BitVec.ofNat 32 (4*n) ∧
      (∀ r : Reg, r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  induction n generalizing c ram p with
  | zero => omega
  | succ n ih =>
    have hram : B.inRam p 4 = true := by
      simpa using Memory.block_access (B := B) (p := p) (n := 4*(n+1)) (off := 0) (width := 4) hm (by decide) (by omega)
    have hnext : (p+4#32).toNat = p.toNat+4 := add_nat p 4 (by omega)
    have hend : (p+BitVec.ofNat 32 (4*(n+1))).toNat = p.toNat+4*(n+1) := add_nat p _ htop
    have ht : taken .ltu (p+4#32) (p+BitVec.ofNat 32 (4*(n+1))) = decide (0 < n) := by
      change decide ((p+4#32).toNat < (p+BitVec.ofNat 32 (4*(n+1))).toNat) = _
      rw [hnext,hend]
      have hh : p.toNat+4 < p.toNat+4*(n+1) ↔ 0 < n := by omega
      simp only [hh]
    obtain ⟨d,hr,hpc,hptr,hregs,hcsr⟩ := turn B c ram p _ (decide (0 < n)) hp h14 h13 h15 ha hram ht
    by_cases hz : n = 0
    · subst n
      refine ⟨d,?_,?_,?_,hregs,hcsr⟩
      · simpa [writes] using hr
      · simpa using hpc
      · exact hptr
    · have hn' : 0 < n := by omega
      have heq : (p+4#32)+BitVec.ofNat 32 (4*n) = p+BitVec.ofNat 32 (4*(n+1)) := by
        rw [BitVec.add_assoc,←BitVec.ofNat_add]
        rw [show 4+4*n = 4*(n+1) by omega]
      have hm' : Memory.Block B (p+4#32) (4*n) :=
        Memory.sub_block hm (by omega) (by omega)
      obtain ⟨d',hr',hpc',hptr',hregs',hcsr'⟩ := ih d (ramWrite ram p 0#32 .w) (p+4#32) hn'
        (by simpa [hn'] using hpc) hptr
        (by rw [hregs 13 (by decide),h13,heq])
        ((hregs 15 (by decide)).trans h15)
        (by rw [hnext];omega) hm' (by rw [hnext];omega)
      refine ⟨d',?_,hpc',hptr'.trans heq,?_,hcsr'.trans hcsr⟩
      · have hs := hr.trans hr'
        simpa [writes,Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hs
      · intro r hr
        exact (hregs' r hr).trans (hregs r hr)

theorem frame (ram : Word → BitVec 8) (p : Word) (n : Nat) (x : Word)
    (hx : ∀ i : Fin (4*n), x ≠ p+BitVec.ofNat 32 i.val) : writes ram p n x = ram x := by
  induction n generalizing ram p with
  | zero => rfl
  | succ n ih =>
    change writes (ramWrite ram p 0#32 .w) (p+4#32) n x = ram x
    rw [ih _ _ (by
      intro i
      have hi := i.isLt
      have ha : (p+4#32)+BitVec.ofNat 32 i.val = p+BitVec.ofNat 32 (4+i.val) := by
        rw [BitVec.ofNat_add,BitVec.add_assoc]
      rw [ha]
      exact hx ⟨4+i.val,by omega⟩)]
    exact ramWrite_w_other ram p 0#32 x (fun k hk => hx ⟨k,by omega⟩)

theorem offset_ne (p : Word) (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) (hne : a ≠ b) :
    p+BitVec.ofNat 32 a ≠ p+BitVec.ofNat 32 b := by
  intro h
  have hh := congrArg BitVec.toNat ((BitVec.add_right_inj p).mp h)
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hh
  exact hne hh

theorem zero_bytes (ram : Word → BitVec 8) (p : Word) (n : Nat)
    (htop : p.toNat+4*n < 2^32) :
    ∀ i : Fin (4*n), writes ram p n (p+BitVec.ofNat 32 i.val) = 0#8 := by
  induction n generalizing ram p with
  | zero => intro i;have := i.isLt;omega
  | succ n ih =>
    intro i
    have hi := i.isLt
    by_cases hfirst : i.val < 4
    · change writes (ramWrite ram p 0#32 .w) (p+4#32) n (p+BitVec.ofNat 32 i.val) = 0#8
      rw [frame _ _ _ _ (by
        intro j
        have hj := j.isLt
        rw [BitVec.add_assoc,←BitVec.ofNat_add]
        exact offset_ne p i.val (4+j.val) (by omega) (by omega) (by omega))]
      have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
      rcases hc with h|h|h|h
      all_goals simp [h,ramWrite,ramPut,byteOf,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]
    · have hk : i.val-4 < 4*n := by omega
      have hn : (p+4#32).toNat+4*n < 2^32 := by
        rw [add_nat p 4 (by omega)]
        omega
      have hh := ih (ramWrite ram p 0#32 .w) (p+4#32) hn ⟨i.val-4,hk⟩
      change writes (ramWrite ram p 0#32 .w) (p+4#32) n (p+BitVec.ofNat 32 i.val) = 0#8
      have ha : (p+4#32)+BitVec.ofNat 32 (i.val-4) = p+BitVec.ofNat 32 i.val := by
        rw [BitVec.add_assoc,←BitVec.ofNat_add,show 4+(i.val-4) = i.val by omega]
      rw [ha] at hh
      exact hh


theorem separated (a b : Word) (n m : Nat) (horder : a.toNat+n ≤ b.toNat)
    (htop : b.toNat+m ≤ 2^32) :
    ∀ i : Fin n, ∀ j : Fin m, a+BitVec.ofNat 32 i.val ≠ b+BitVec.ofNat 32 j.val := by
  intro i j he
  have hi := i.isLt
  have hj := j.isLt
  have hb := b.isLt
  have hh := congrArg BitVec.toNat he
  rw [add_nat a i.val (by omega),add_nat b j.val (by omega)] at hh
  omega

end E5R.Thermostat.WordZero
