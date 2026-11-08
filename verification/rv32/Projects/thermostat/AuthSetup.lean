import Projects.thermostat.AuthCode
import Projects.thermostat.Usize
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.AuthSetup
open E5R E5R.Thermostat

theorem subtract_prefix (len : Nat) : BitVec.ofNat 32 (len+7)+0xfffffff9#32 = BitVec.ofNat 32 len := by
  rw [BitVec.ofNat_add,BitVec.add_assoc,show 7#32+0xfffffff9#32 = 0#32 by decide +kernel,BitVec.add_zero]

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (eng header key : Word) (len : Nat)
    (hl : len+7 < 2^32) (hp : c.pc = 0x80000568#32)
    (h23 : c.get 23 = eng) (h24 : c.get 24 = header) (h25 : c.get 25 = BitVec.ofNat 32 (len+7))
    (hm : Memory.Block B eng 24) (ha : eng.toNat%4 = 0)
    (hlen : ramRead ram (eng+20#32) .w = 7#32) (hkey : ramRead ram (eng+16#32) .w = key) :
    ∃ d n, n ≤ 8 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if len = 7 then 0x80000582#32 else 0x800005a2#32) ∧
      (len = 7 → d.get 10 = 0#32 ∧ d.get 11 = key ∧ d.get 12 = header+7#32 ∧ d.get 13 = key+7#32) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 7#32 0x8000056c#32
  let c2 := c1.wr 13 (BitVec.ofNat 32 len) 0x80000570#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact au2147485032) fun o => ?_
    rw [exec_load,h23,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned eng 5 ha)
      (Memory.block_access hm (off := 20) (by decide) (by decide)),hlen,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000056c#32).getLsbD 0 = false;decide) au2147485036 fun o => ?_
    have hv : c1.get 25 = BitVec.ofNat 32 (len+7) := by simp [c1,Core.wr_get_ne,h25]
    rw [exec_opimm,hv]
    change interp B img o (.done (c1.wr 13 (BitVec.ofNat 32 (len+7)+0xfffffff9#32) 0x80000570#32)) ram 0 [] = _
    rw [subtract_prefix];rfl
  have v10 : c2.get 10 = 7#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
  have v13 : c2.get 13 = BitVec.ofNat 32 len := by simp [c2,Core.wr_get]
  by_cases he : len = 7
  · let c3 := c2.goto 0x80000574#32
    let c4 := c3.wr 10 0#32 0x80000576#32
    let c5 := c4.goto 0x80000578#32
    let c6 := c5.wr 11 key 0x8000057c#32
    let c7 := c6.wr 12 (header+7#32) 0x80000580#32
    let d := c7.wr 13 (key+7#32) 0x80000582#32
    have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
      refine detStep_of (by change (0x80000570#32).getLsbD 0 = false;decide) au2147485040 fun o => ?_
      rw [exec_branch,v13,v10,he];rfl
    have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      refine detStep_of (by change (0x80000574#32).getLsbD 0 = false;decide) au2147485044 fun o => ?_
      rw [exec_opimm,Core.get_zero];rfl
    have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
      refine detStep_of (by change (0x80000576#32).getLsbD 0 = false;decide) au2147485046 fun o => ?_
      have hv : c4.get 13 = 7#32 := by simp [c4,c3,c2,Core.wr_get_ne,Core.wr_get,he]
      rw [exec_branch,hv,Core.get_zero];rfl
    have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
      refine detStep_of (by change (0x80000578#32).getLsbD 0 = false;decide) au2147485048 fun o => ?_
      have hv : c5.get 23 = eng := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,h23]
      rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned eng 4 ha)
        (Memory.block_access hm (off := 16) (by decide) (by decide)),hkey];rfl
    have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
      refine detStep_of (by change (0x8000057c#32).getLsbD 0 = false;decide) au2147485052 fun o => ?_
      have hv : c6.get 24 = header := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h24]
      rw [exec_opimm,hv];rfl
    have s7 : DetStep B img ⟨c7,ram⟩ ⟨d,ram⟩ := by
      refine detStep_of (by change (0x80000580#32).getLsbD 0 = false;decide) au2147485056 fun o => ?_
      have hv13 : c7.get 13 = 7#32 := by simp [c7,c6,c5,c4,c3,c2,Core.wr_get_ne,Core.wr_get,he]
      have hv11 : c7.get 11 = key := by simp [c7,c6,Core.wr_get_ne,Core.wr_get]
      rw [exec_op,hv13,hv11]
      simp only [alu]
      rw [BitVec.add_comm 7#32 key];rfl
    refine ⟨d,8,by omega,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.single s7))))))),by simp [d,he],?_,?_,by rfl⟩
    · intro _;simp [d,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · intro r h1 h2 h3 h4;simp [d,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h3,h4]
  · let d := c2.goto 0x800005a2#32
    have s2 : DetStep B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
      refine detStep_of (by change (0x80000570#32).getLsbD 0 = false;decide) au2147485040 fun o => ?_
      rw [exec_branch,v13,v10]
      change interp B img o (if taken .ne (BitVec.ofNat 32 len) (BitVec.ofNat 32 7) then _ else _) ram 0 [] = _
      rw [Usize.ne len 7 (by omega) (by decide),decide_eq_true he]
      simp only [ite_true]
      change interp B img o (jump c2 (0x80000570#32+0x32#32)) ram 0 [] = _
      rw [show 0x80000570#32+0x32#32 = 0x800005a2#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    refine ⟨d,3,by omega,.step s0 (.step s1 (.single s2)),by simp [d,he],?_,?_,by rfl⟩
    · intro h;contradiction
    · intro r h1 h2 h3 h4;simp [d,c2,c1,Core.wr_get_ne,h1,h4]
end E5R.Thermostat.AuthSetup
