import Projects.thermostat.HeaderCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeaderSetup
open E5R E5R.Thermostat

theorem shift_count (n : Nat) (hn : n ≤ 16) : BitVec.ofNat 32 n <<< 4 = BitVec.ofNat 32 (16*n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  change (n%4294967296*16)%4294967296 = 16*n%4294967296
  omega

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (req p : Word) (rawLength count : Nat)
    (hb : count ≤ 16) (hp : c.pc = 0x800026ce#32) (h10 : c.get 10 = req)
    (h14 : c.get 14 = BitVec.ofNat 32 count) (hm : Memory.Block B req 336) (ha : req.toNat%4 = 0)
    (hptr : ramRead ram (req+328#32) .w = p) (hlen : ramRead ram (req+332#32) .w = BitVec.ofNat 32 rawLength) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800026e8#32 ∧
      d.get 15 = p ∧ d.get 12 = BitVec.ofNat 32 rawLength ∧ d.get 16 = req+32#32 ∧
      d.get 17 = (req+32#32)+BitVec.ofNat 32 (16*count) ∧
      (∀ r : Reg, r ≠ 12 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 15 p 0x800026d2#32
  let c2 := c1.wr 12 (BitVec.ofNat 32 rawLength) 0x800026d6#32
  let c3 := c2.wr 16 (req+32#32) 0x800026da#32
  let c4 := c3.wr 14 (BitVec.ofNat 32 (16*count)) 0x800026dc#32
  let c5 := c4.wr 17 ((req+32#32)+BitVec.ofNat 32 (16*count)) 0x800026e0#32
  let d := c5.goto 0x800026e8#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact hd2147493582) fun o => ?_
    rw [exec_load,h10,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned req 82 ha)
      (Memory.block_access hm (off := 328) (by decide) (by decide)),hptr,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x800026d2#32).getLsbD 0 = false;decide) hd2147493586 fun o => ?_
    have hv : c1.get 10 = req := by simp [c1,Core.wr_get_ne,h10]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned req 83 ha)
      (Memory.block_access hm (off := 332) (by decide) (by decide)),hlen];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x800026d6#32).getLsbD 0 = false;decide) hd2147493590 fun o => ?_
    have hv : c2.get 10 = req := by simp [c2,c1,Core.wr_get_ne,h10]
    rw [exec_opimm,hv];rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x800026da#32).getLsbD 0 = false;decide) hd2147493594 fun o => ?_
    have hv : c3.get 14 = BitVec.ofNat 32 count := by simp [c3,c2,c1,Core.wr_get_ne,h14]
    rw [exec_opimm,hv]
    change interp B img o (.done (c3.wr 14 (BitVec.ofNat 32 count <<< 4) 0x800026dc#32)) ram 0 [] = _
    rw [shift_count count hb];rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x800026dc#32).getLsbD 0 = false;decide) hd2147493596 fun o => ?_
    have v16 : c4.get 16 = req+32#32 := by simp [c4,c3,Core.wr_get_ne,Core.wr_get]
    have v14 : c4.get 14 = BitVec.ofNat 32 (16*count) := by simp [c4,Core.wr_get]
    rw [exec_op,v16,v14];rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x800026e0#32).getLsbD 0 = false;decide) hd2147493600 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c5 (0x800026e0#32+8#32)) ram 0 [] = _
    rw [show 0x800026e0#32+8#32 = 0x800026e8#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_,?_,?_,?_,?_,by rfl⟩
  · simp [d,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c5,c4,c3,c2,Core.wr_get_ne,Core.wr_get]
  · simp [d,c5,c4,c3,Core.wr_get_ne,Core.wr_get]
  · simp [d,c5,Core.wr_get]
  · intro r h1 h2 h3 h4 h5;simp [d,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h3,h4,h5]
end E5R.Thermostat.HeaderSetup
