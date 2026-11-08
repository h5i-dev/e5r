import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadSetupCTName
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame dst pos src count : Word) (h2 : c.get 2=frame+16#32) (h11 : c.get 11=pos) (h23 : c.get 23=dst) (hm : Memory.Block B frame 96) (ha : frame.toNat%4=0) (hc : ramRead ram (frame+40#32) .w=192#32) (h10 : c.get 10=1#32) (hs : c.get 21=src) (hn : c.get 24=count) (hg : c.get 22=1#32)
    (hp : c.pc=0x80004018#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80004122#32 ∧
      d.get 12=pos ∧ d.get 10=dst ∧ d.get 11=192#32 ∧ d.get 13=src ∧ d.get 14=count ∧ d.get 1=2147500078#32 ∧ (∀ r : Reg, r≠12 → r≠10 → r≠11 → r≠13 → r≠14 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x8000401c#32
  let c2 := c1.wr 12 (pos) 0x8000401e#32
  let c3 := c2.wr 10 (dst) 0x80004020#32
  let c4 := c3.wr 11 (192#32) 0x80004022#32
  let c5 := c4.wr 13 (src) 0x80004024#32
  let c6 := c5.wr 14 (count) 0x80004026#32
  let c7 := c6.wr 1 (2147500070#32) 0x8000402a#32
  let c8 := c7.wr 1 (2147500078#32) 0x80004122#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147500056) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v10 : c.get 10=1#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
    have v22 : c.get 22=1#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
    rw [exec_branch,v10,v22,show taken .ne 1#32 1#32=false by decide]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp]; rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000401c#32).getLsbD 0=false;decide) rh2147500060 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v11 : c1.get 11=pos := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
    rw [exec_op,Core.get_zero,v11,(show alu .add (0 : Word) (pos)=pos from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000401e#32).getLsbD 0=false;decide) rh2147500062 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v23 : c2.get 23=dst := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
    rw [exec_op,Core.get_zero,v23,(show alu .add (0 : Word) (dst)=dst from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80004020#32).getLsbD 0=false;decide) rh2147500064 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v2 : c3.get 2=frame+16#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+24#32=40#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 10 ha) (Memory.block_access hm (off := 40) (by decide) (by decide)),hc];first | rfl | (rw [hp]; rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80004022#32).getLsbD 0=false;decide) rh2147500066 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v21 : c4.get 21=src := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
    rw [exec_op,Core.get_zero,v21,(show alu .add (0 : Word) (src)=src from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80004024#32).getLsbD 0=false;decide) rh2147500068 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v24 : c5.get 24=count := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
    rw [exec_op,Core.get_zero,v24,(show alu .add (0 : Word) (count)=count from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80004026#32).getLsbD 0=false;decide) rh2147500070 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    rw [exec_auipc,show c6.pc=2147500070#32 by rfl,BitVec.add_zero];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x8000402a#32).getLsbD 0=false;decide) rh2147500074 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v1 : c7.get 1=2147500070#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c7.set 1 (2147500074#32+4#32)) ((2147500070#32+252#32) &&& ~~~1)) ram 0 [] [] = _
    rw [show (2147500070#32+252#32) &&& ~~~1=2147500322#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c8,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.single t7))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg]
  · intro reg h12 h10 h11 h13 h14 h1;simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h10,hs,hn,hg,h12,h10,h11,h13,h14,h1]
end E5R.Thermostat.ResponseHeadSetupCTName
