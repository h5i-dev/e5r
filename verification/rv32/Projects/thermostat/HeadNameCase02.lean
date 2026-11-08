import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadNameCase02
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (v last count sp : Word) (h5 : c.get 5=33#32)
(h6 : c.get 6=48#32)
(h7 : c.get 7=14#32)
(h28 : c.get 28=58#32)
(h27 : c.get 27=91#32)
(h30 : c.get 30=v)
(h15 : c.get 15=last)
(h14 : c.get 14=count)
(h2 : c.get 2=sp)
(hmask : ramRead ram (sp+32#32) .w=9409#32) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
(hb0 : taken .ltu (v) (33#32)=false)
(hb1 : taken .geu (v) (48#32)=false)
(hb2 : taken .geu (alu .and (alu .add (v) (0xffffffde#32)) (255#32)) (14#32)=false)
(hb3 : taken .eq (last) (count)=true)
    (hp : c.pc=0x80002ff8#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000342c#32 ∧
      d.get 30=alu .add (v) (0xffffffde#32) ∧ d.get 19=alu .and (alu .add (v) (0xffffffde#32)) (255#32) ∧ (∀ r : Reg, r≠30 → r≠19 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80002ffc#32
  let c2 := c1.goto 0x80003000#32
  let c3 := c2.wr 30 (alu .add (v) (0xffffffde#32)) 0x80003004#32
  let c4 := c3.wr 19 (alu .and (alu .add (v) (0xffffffde#32)) (255#32)) 0x80003008#32
  let c5 := c4.goto 0x8000300c#32
  let c6 := c5.goto 0x8000342c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495928) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v30 : c.get 30=v := by simp [Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    have v5 : c.get 5=33#32 := by simp [Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_branch,v30,v5,hb0]
    rw [hp]
    rfl
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ffc#32).getLsbD 0=false;decide) hh2147495932 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v30 : c1.get 30=v := by simp [c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    have v6 : c1.get 6=48#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_branch,v30,v6,hb1]
    rfl
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003000#32).getLsbD 0=false;decide) hh2147495936 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v30 : c2.get 30=v := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_opimm,v30];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80003004#32).getLsbD 0=false;decide) hh2147495940 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v30 : c3.get 30=alu .add (v) (0xffffffde#32) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_opimm,v30];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80003008#32).getLsbD 0=false;decide) hh2147495944 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v19 : c4.get 19=alu .and (alu .add (v) (0xffffffde#32)) (255#32) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    have v7 : c4.get 7=14#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_branch,v19,v7,hb2]
    rfl
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x8000300c#32).getLsbD 0=false;decide) hh2147495948 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v15 : c5.get 15=last := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    have v14 : c5.get 14=count := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_branch,v15,v14,hb3]
    simp only [ite_true]
    change Observed.interp B img o (jump c5 (0x8000300c#32+0x420#32)) ram 0 [] []=_
    rw [show 0x8000300c#32+0x420#32=0x8000342c#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
  · intro reg h30 h19;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2,h30,h19]
end E5R.Thermostat.HeadNameCase02
