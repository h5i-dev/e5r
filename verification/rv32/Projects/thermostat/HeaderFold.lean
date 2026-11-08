import Projects.thermostat.HeaderCode
import Projects.thermostat.HeaderMath
import Projects.thermostat.ReadBytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeaderFold
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p q : Word) (a b : BitVec 8)
    (hp : c.pc = 0x80002706#32) (h10 : c.get 10 = p) (h14 : c.get 14 = q)
    (ha : ReadBytes.Byte B img ram p a) (hb : ReadBytes.Byte B img ram q b) :
    ∃ d, DetSteps B img 10 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x8000272a#32 ∧
      d.get 6 = BitVec.ofNat 32 (HeaderSpec.lower a).toNat ∧ d.get 7 = BitVec.ofNat 32 (HeaderSpec.lower b).toNat ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 28 → r ≠ 29 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 6 (BitVec.ofNat 32 a.toNat) 0x8000270a#32
  let c2 := c1.wr 7 (BitVec.ofNat 32 b.toNat) 0x8000270e#32
  let c3 := c2.wr 28 (BitVec.ofNat 32 a.toNat+0xffffffbf#32) 0x80002712#32
  let c4 := c3.wr 29 (BitVec.ofNat 32 b.toNat+0xffffffbf#32) 0x80002716#32
  let c5 := c4.wr 28 (HeaderMath.upperFlag a) 0x8000271a#32
  let c6 := c5.wr 29 (HeaderMath.upperFlag b) 0x8000271e#32
  let c7 := c6.wr 28 (HeaderMath.upperFlag a <<< 5) 0x80002720#32
  let c8 := c7.wr 29 (HeaderMath.upperFlag b <<< 5) 0x80002722#32
  let c9 := c8.wr 6 (BitVec.ofNat 32 (HeaderSpec.lower a).toNat) 0x80002726#32
  let c10 := c9.wr 7 (BitVec.ofNat 32 (HeaderSpec.lower b).toNat) 0x8000272a#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact hd2147493638) fun o => ?_
    have hv0 : c.get 10 = (p) := by simp [Core.wr_get_ne,Core.wr_get,h10,h14]
    rw [exec_load,hv0,BitVec.add_zero,ReadBytes.load ha,ReadBytes.extend_byte,←Memory.ofNat_width,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000270a#32).getLsbD 0 = false;decide) hd2147493642 fun o => ?_
    have hv0 : c1.get 14 = (q) := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h14]
    rw [exec_load,hv0,BitVec.add_zero,ReadBytes.load hb,ReadBytes.extend_byte,←Memory.ofNat_width];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x8000270e#32).getLsbD 0 = false;decide) hd2147493646 fun o => ?_
    have hv0 : c2.get 6 = (BitVec.ofNat 32 a.toNat) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h14]
    rw [exec_opimm,hv0]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80002712#32).getLsbD 0 = false;decide) hd2147493650 fun o => ?_
    have hv0 : c3.get 7 = (BitVec.ofNat 32 b.toNat) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h14]
    rw [exec_opimm,hv0]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80002716#32).getLsbD 0 = false;decide) hd2147493654 fun o => ?_
    have hv0 : c4.get 28 = (BitVec.ofNat 32 a.toNat+0xffffffbf#32) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h14]
    rw [exec_opimm,hv0]
    rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x8000271a#32).getLsbD 0 = false;decide) hd2147493658 fun o => ?_
    have hv0 : c5.get 29 = (BitVec.ofNat 32 b.toNat+0xffffffbf#32) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h14]
    rw [exec_opimm,hv0]
    rfl
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x8000271e#32).getLsbD 0 = false;decide) hd2147493662 fun o => ?_
    have hv0 : c6.get 28 = (HeaderMath.upperFlag a) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h14]
    rw [exec_opimm,hv0]
    rfl
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine detStep_of (by change (0x80002720#32).getLsbD 0 = false;decide) hd2147493664 fun o => ?_
    have hv0 : c7.get 29 = (HeaderMath.upperFlag b) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h14]
    rw [exec_opimm,hv0]
    rfl
  have s8 : DetStep B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine detStep_of (by change (0x80002722#32).getLsbD 0 = false;decide) hd2147493666 fun o => ?_
    have hv0 : c8.get 28 = (HeaderMath.upperFlag a <<< 5) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h14]
    have hv1 : c8.get 6 = (BitVec.ofNat 32 a.toNat) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h14]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c8.wr 6 ((HeaderMath.upperFlag a <<< 5) ||| BitVec.ofNat 32 a.toNat) 0x80002726#32)) ram 0 [] = _
    rw [HeaderMath.folded a];rfl
  have s9 : DetStep B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine detStep_of (by change (0x80002726#32).getLsbD 0 = false;decide) hd2147493670 fun o => ?_
    have hv0 : c9.get 29 = (HeaderMath.upperFlag b <<< 5) := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h14]
    have hv1 : c9.get 7 = (BitVec.ofNat 32 b.toNat) := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h14]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c9.wr 7 ((HeaderMath.upperFlag b <<< 5) ||| BitVec.ofNat 32 b.toNat) 0x8000272a#32)) ram 0 [] = _
    rw [HeaderMath.folded b];rfl
  refine ⟨c10,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.single s9))))))))),rfl,?_,?_,?_,by rfl⟩
  · simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h3 h4
    simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3,h4]
end E5R.Thermostat.HeaderFold
