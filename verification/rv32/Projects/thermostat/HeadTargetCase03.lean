import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadTargetCase03
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (offset index last stopByte base remaining : Word) (byte : BitVec 8) (h30 : c.get 30=offset)
(h18 : c.get 18=index)
(h9 : c.get 9=last)
(h20 : c.get 20=stopByte)
(h28 : c.get 28=base)
(h31 : c.get 31=remaining)
(hm : B.inRam (base+1#32) 1=true) (hbyte : ram (base+1#32)=byte)
(hb0 : taken .eq (offset) ((0 : Word))=false)
(hb1 : taken .geu (index) (last)=false)
(hb2 : taken .ne (stopByte) (alu .add ((0 : Word)) (32#32))=false)
(hb3 : taken .ne (BitVec.ofNat 32 byte.toNat) (alu .add ((0 : Word)) (47#32))=true)
    (hp : c.pc=0x80002dfe#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002efc#32 ∧
      d.get 8=alu .add ((0 : Word)) (47#32) ∧ d.get 28=BitVec.ofNat 32 byte.toNat ∧ (∀ r : Reg, r≠8 → r≠28 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80002e02#32
  let c2 := c1.goto 0x80002e06#32
  let c3 := c2.wr 8 (alu .add ((0 : Word)) (32#32)) 0x80002e0a#32
  let c4 := c3.goto 0x80002e0e#32
  let c5 := c4.wr 28 (BitVec.ofNat 32 byte.toNat) 0x80002e12#32
  let c6 := c5.wr 8 (alu .add ((0 : Word)) (47#32)) 0x80002e16#32
  let c7 := c6.goto 0x80002efc#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495422) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v30 : c.get 30=offset := by simp [Core.wr_get_ne,Core.wr_get,h30,h18,h9,h20,h28,h31]
    rw [exec_branch,v30,Core.get_zero,hb0]
    rw [hp]
    rfl
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e02#32).getLsbD 0=false;decide) hh2147495426 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v18 : c1.get 18=index := by simp [c1,Core.wr_get_ne,Core.wr_get,h30,h18,h9,h20,h28,h31]
    have v9 : c1.get 9=last := by simp [c1,Core.wr_get_ne,Core.wr_get,h30,h18,h9,h20,h28,h31]
    rw [exec_branch,v18,v9,hb1]
    rfl
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e06#32).getLsbD 0=false;decide) hh2147495430 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e0a#32).getLsbD 0=false;decide) hh2147495434 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v20 : c3.get 20=stopByte := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h18,h9,h20,h28,h31]
    have v8 : c3.get 8=alu .add ((0 : Word)) (32#32) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h18,h9,h20,h28,h31]
    rw [exec_branch,v20,v8,hb2]
    rfl
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e0e#32).getLsbD 0=false;decide) hh2147495438 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v28 : c4.get 28=base := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h18,h9,h20,h28,h31]
    rw [exec_load,v28,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm,Memory.load_byte,hbyte];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e12#32).getLsbD 0=false;decide) hh2147495442 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e16#32).getLsbD 0=false;decide) hh2147495446 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v28 : c6.get 28=BitVec.ofNat 32 byte.toNat := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h18,h9,h20,h28,h31]
    have v8 : c6.get 8=alu .add ((0 : Word)) (47#32) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h18,h9,h20,h28,h31]
    rw [exec_branch,v28,v8,hb3]
    simp only [ite_true]
    change Observed.interp B img o (jump c6 (0x80002e16#32+0xe6#32)) ram 0 [] []=_
    rw [show 0x80002e16#32+0xe6#32=0x80002efc#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h18,h9,h20,h28,h31]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h18,h9,h20,h28,h31]
  · intro reg h8 h28;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h30,h18,h9,h20,h28,h31,h8,h28]
end E5R.Thermostat.HeadTargetCase03
