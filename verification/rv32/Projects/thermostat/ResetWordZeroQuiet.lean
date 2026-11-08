-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.WordZero
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option linter.unusedSimpArgs false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.WordZero
theorem turn_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p e : Word) (b : Bool)
    (hp : c.pc = 0x80005676#32) (h14 : c.get 14 = p) (h13 : c.get 13 = e)
    (h15 : c.get 15 = 0#32) (ha : p.toNat%4 = 0) (hr : B.inRam p 4 = true)
    (ht : taken .ltu (p+4#32) e = b) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ramWrite ram p 0#32 .w⟩ ∧
      d.pc = (if b then 0x80005676#32 else 0x8000567e#32) ∧
      d.get 14 = p+4#32 ∧ (∀ r : Reg, r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram p 0#32 .w
  let c1 := c.goto 0x80005678#32
  let c2 := c1.wr 14 (p+4#32) 0x8000567a#32
  let d := c2.goto (if b then 0x80005676#32 else 0x8000567e#32)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact ze2147505782) fun o => ?_
    rw [exec_store,h14,h15,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .w) o ha hr,hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r1⟩ := by
    refine QuietDet.step_of (by change (0x80005678#32).getLsbD 0 = false;decide) ze2147505784 fun o => ?_
    have hv : c1.get 14 = p := h14
    rw [exec_opimm,hv]
    rfl
  have s2 : Quiet.Step B img ⟨c2,r1⟩ ⟨d,r1⟩ := by
    refine QuietDet.step_of (by change (0x8000567a#32).getLsbD 0 = false;decide) ze2147505786 fun o => ?_
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

end E5R.Thermostat.WordZero
namespace E5R.Thermostat.WordZero
theorem loop_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (n : Nat)
    (hn : 0 < n) (hp : c.pc = 0x80005676#32) (h14 : c.get 14 = p)
    (h13 : c.get 13 = p+BitVec.ofNat 32 (4*n)) (h15 : c.get 15 = 0#32)
    (ha : p.toNat%4 = 0) (hm : Memory.Block B p (4*n)) (htop : p.toNat+4*n < 2^32) :
    ∃ d, Quiet.Steps B img (3*n) ⟨c,ram⟩ ⟨d,writes ram p n⟩ ∧
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
    obtain ⟨d,hr,hpc,hptr,hregs,hcsr⟩ := E5R.Thermostat.WordZero.turn_quiet B c ram p _ (decide (0 < n)) hp h14 h13 h15 ha hram ht
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

end E5R.Thermostat.WordZero
