import Projects.thermostat.MemcpyCode
import Projects.thermostat.ReadBytes
import Projects.thermostat.ParamMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SmallCopyTurn
open E5R E5R.Thermostat

theorem byte_word (b : BitVec 8) : byteOf (BitVec.ofNat 32 b.toNat) 0 = b := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  simp only [byteOf,BitVec.toNat_ofNat,Nat.pow_zero,Nat.div_one]
  omega

/-- One actual memcpy byte-copy iteration, using an actual checked RAM/ROM load. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word) (b : BitVec 8) (n : Nat)
    (hn : 0 < n) (hb : n < 2^32) (hp : c.pc = 0x800052fc#32)
    (h11 : c.get 11 = src) (h13 : c.get 13 = dst) (h12 : c.get 12 = BitVec.ofNat 32 n)
    (hs : ReadBytes.Byte B img ram src b) (hd : B.inRam dst 1 = true) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,ramPut ram dst b⟩ ∧
      d.pc = (if n = 1 then 0x8000530c#32 else 0x800052fc#32) ∧
      d.get 11 = src+1#32 ∧ d.get 13 = dst+1#32 ∧ d.get 12 = BitVec.ofNat 32 (n-1) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (BitVec.ofNat 32 b.toNat) 0x80005300#32
  let c2 := c1.wr 12 (BitVec.ofNat 32 (n-1)) 0x80005302#32
  let c3 := c2.goto 0x80005306#32
  let c4 := c3.wr 13 (dst+1#32) 0x80005308#32
  let c5 := c4.wr 11 (src+1#32) 0x8000530a#32
  let d := c5.goto (if n = 1 then 0x8000530c#32 else 0x800052fc#32)
  let r := ramPut ram dst b
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact cp2147504892) fun o => ?_
    rw [exec_load,h11,BitVec.add_zero,ReadBytes.load hs,ReadBytes.extend_byte,←Memory.ofNat_width,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80005300#32).getLsbD 0 = false;decide) cp2147504896 fun o => ?_
    have hv : c1.get 12 = BitVec.ofNat 32 n := by simp [c1,Core.wr_get_ne,h12]
    rw [exec_opimm,hv]
    change interp B img o (.done (c1.wr 12 (BitVec.ofNat 32 n+0xffffffff#32) 0x80005302#32)) ram 0 [] = _
    rw [ParamMath.decrement n hn];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,r⟩ := by
    refine detStep_of (by change (0x80005302#32).getLsbD 0 = false;decide) cp2147504898 fun o => ?_
    have hv13 : c2.get 13 = dst := by simp [c2,c1,Core.wr_get_ne,h13]
    have hv14 : c2.get 14 = BitVec.ofNat 32 b.toNat := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hv13,hv14,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hd]
    change interp B img o (.done c3) (ramPut ram dst (byteOf (BitVec.ofNat 32 b.toNat) 0)) 0 [] = _
    rw [byte_word];rfl
  have s3 : DetStep B img ⟨c3,r⟩ ⟨c4,r⟩ := by
    refine detStep_of (by change (0x80005306#32).getLsbD 0 = false;decide) cp2147504902 fun o => ?_
    have hv : c3.get 13 = dst := by simp [c3,c2,c1,Core.wr_get_ne,h13]
    rw [exec_opimm,hv];rfl
  have s4 : DetStep B img ⟨c4,r⟩ ⟨c5,r⟩ := by
    refine detStep_of (by change (0x80005308#32).getLsbD 0 = false;decide) cp2147504904 fun o => ?_
    have hv : c4.get 11 = src := by simp [c4,c3,c2,c1,Core.wr_get_ne,h11]
    rw [exec_opimm,hv];rfl
  have s5 : DetStep B img ⟨c5,r⟩ ⟨d,r⟩ := by
    refine detStep_of (by change (0x8000530a#32).getLsbD 0 = false;decide) cp2147504906 fun o => ?_
    have hv : c5.get 12 = BitVec.ofNat 32 (n-1) := by simp [c5,c4,c3,c2,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,hv,Core.get_zero,ParamMath.counter_branch n hn hb]
    by_cases he : n = 1
    · simp only [he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,d];rfl
    · simp only [he,ne_eq,not_false_eq_true,decide_true,ite_true,d,ite_false]
      change interp B img o (jump c5 (0x8000530a#32+0xfffffff2#32)) r 0 [] = _
      rw [show 0x8000530a#32+0xfffffff2#32 = 0x800052fc#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_,?_,?_,?_,by rfl⟩
  · simp [d,c5,Core.wr_get]
  · simp [d,c5,c4,Core.wr_get_ne,Core.wr_get]
  · simp [d,c5,c4,c3,c2,Core.wr_get_ne,Core.wr_get]
  · intro reg h11 h12 h13 h14
    simp [d,c5,c4,c3,c2,c1,Core.wr_get_ne,h11,h12,h13,h14]
end E5R.Thermostat.SmallCopyTurn
