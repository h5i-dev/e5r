import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecMath
import Projects.thermostat.HttpStatusMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadSelectYes
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame dst pos body : Word) (status : Nat) (hstatus : status≤599) (h2 : c.get 2=frame+16#32) (h11 : c.get 11=pos) (h10 : c.get 10=1#32) (h18 : c.get 18=1#32) (h23 : c.get 23=dst) (hm : Memory.Block B frame 96) (ha : frame.toNat%4=0) (hc : ramRead ram (frame+40#32) .w=192#32) (hs : ramRead ram (frame+36#32) .w=BitVec.ofNat 32 status) (hb : ramRead ram (frame+28#32) .w=body) (hsmall : ¬status<200) (hn304 : status≠304) (hn204 : status≠204)
    (hp : c.pc=0x80004076#32) :
    ∃ d, Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80004180#32 ∧
      d.get 12=pos ∧ d.get 11=192#32 ∧ d.get 10=dst ∧ d.get 13=body ∧ d.get 1=2147500196#32 ∧ (∀ r : Reg, r≠12 → r≠11 → r≠10 → r≠13 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x8000407a#32
  let c2 := c1.wr 12 (pos) 0x8000407c#32
  let c3 := c2.wr 11 (200#32) 0x80004080#32
  let c4 := c3.wr 10 (BitVec.ofNat 32 status) 0x80004082#32
  let c5 := c4.goto 0x80004086#32
  let c6 := c5.wr 11 (304#32) 0x8000408a#32
  let c7 := c6.goto 0x8000408e#32
  let c8 := c7.wr 11 (204#32) 0x80004092#32
  let c9 := c8.goto 0x80004096#32
  let c10 := c9.wr 10 (dst) 0x80004098#32
  let c11 := c10.wr 11 (192#32) 0x8000409a#32
  let c12 := c11.wr 13 (body) 0x8000409c#32
  let c13 := c12.wr 1 (2147500188#32) 0x800040a0#32
  let c14 := c13.wr 1 (2147500196#32) 0x80004180#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147500150) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v10 : c.get 10=1#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    have v18 : c.get 18=1#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    rw [exec_branch,v10,v18,show taken .ne 1#32 1#32=false by decide]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp]; rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000407a#32).getLsbD 0=false;decide) rh2147500154 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v11 : c1.get 11=pos := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    rw [exec_op,Core.get_zero,v11,(show alu .add (0 : Word) (pos)=pos from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000407c#32).getLsbD 0=false;decide) rh2147500156 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80004080#32).getLsbD 0=false;decide) rh2147500160 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v2 : c3.get 2=frame+16#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+20#32=36#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 9 ha) (Memory.block_access hm (off := 36) (by decide) (by decide)),hs];first | rfl | (rw [hp]; rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80004082#32).getLsbD 0=false;decide) rh2147500162 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v10 : c4.get 10=BitVec.ofNat 32 status := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    have v11 : c4.get 11=200#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    rw [exec_branch,v10,v11]
    rw [HttpDecMath.branch_ltu status 200 (by omega) (by decide),show decide (status<200)=false by simp [hsmall]]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80004086#32).getLsbD 0=false;decide) rh2147500166 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x8000408a#32).getLsbD 0=false;decide) rh2147500170 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v10 : c6.get 10=BitVec.ofNat 32 status := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    have v11 : c6.get 11=304#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    rw [exec_branch,v10,v11]
    rw [HttpStatusMath.unequal status 304 (by omega) (by decide) hn304]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x8000408e#32).getLsbD 0=false;decide) rh2147500174 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80004092#32).getLsbD 0=false;decide) rh2147500178 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v10 : c8.get 10=BitVec.ofNat 32 status := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    have v11 : c8.get 11=204#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    rw [exec_branch,v10,v11]
    rw [HttpStatusMath.unequal status 204 (by omega) (by decide) hn204]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80004096#32).getLsbD 0=false;decide) rh2147500182 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v23 : c9.get 23=dst := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    rw [exec_op,Core.get_zero,v23,(show alu .add (0 : Word) (dst)=dst from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80004098#32).getLsbD 0=false;decide) rh2147500184 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v2 : c10.get 2=frame+16#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+24#32=40#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 10 ha) (Memory.block_access hm (off := 40) (by decide) (by decide)),hc];first | rfl | (rw [hp]; rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x8000409a#32).getLsbD 0=false;decide) rh2147500186 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v2 : c11.get 2=frame+16#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+12#32=28#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 7 ha) (Memory.block_access hm (off := 28) (by decide) (by decide)),hb];first | rfl | (rw [hp]; rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x8000409c#32).getLsbD 0=false;decide) rh2147500188 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    rw [exec_auipc,show c12.pc=2147500188#32 by rfl,BitVec.add_zero];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x800040a0#32).getLsbD 0=false;decide) rh2147500192 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v1 : c13.get 1=2147500188#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c13.set 1 (2147500192#32+4#32)) ((2147500188#32+228#32) &&& ~~~1)) ram 0 [] [] = _
    rw [show (2147500188#32+228#32) &&& ~~~1=2147500416#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c14,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.single t13))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23]
  · intro reg h12 h11 h10 h13 h1;simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h10,h18,h23,h12,h11,h10,h13,h1]
end E5R.Thermostat.ResponseHeadSelectYes
