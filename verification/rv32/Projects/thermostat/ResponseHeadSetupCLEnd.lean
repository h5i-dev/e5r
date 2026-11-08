import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadSetupCLEnd
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame dst pos src count : Word) (h2 : c.get 2=frame+16#32) (h11 : c.get 11=pos) (h23 : c.get 23=dst) (hm : Memory.Block B frame 96) (ha : frame.toNat%4=0) (hc : ramRead ram (frame+40#32) .w=192#32) (h25 : c.get 25=count) (h19 : c.get 19=src)
    (hp : c.pc=0x800040ac#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80004122#32 ∧
      d.get 11=192#32 ∧ d.get 10=dst ∧ d.get 14=count <<< 1 ∧ d.get 13=src ∧ d.get 1=2147500222#32 ∧ (∀ r : Reg, r≠11 → r≠10 → r≠14 → r≠13 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (192#32) 0x800040ae#32
  let c2 := c1.wr 10 (dst) 0x800040b0#32
  let c3 := c2.wr 14 (count <<< 1) 0x800040b4#32
  let c4 := c3.wr 13 (src) 0x800040b6#32
  let c5 := c4.wr 1 (2147500214#32) 0x800040ba#32
  let c6 := c5.wr 1 (2147500222#32) 0x80004122#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147500204) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=frame+16#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h11,h23,h25,h19]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+24#32=40#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 10 ha) (Memory.block_access hm (off := 40) (by decide) (by decide)),hc];first | rfl | (rw [hp]; rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800040ae#32).getLsbD 0=false;decide) rh2147500206 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v23 : c1.get 23=dst := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h25,h19]
    rw [exec_op,Core.get_zero,v23,(show alu .add (0 : Word) (dst)=dst from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800040b0#32).getLsbD 0=false;decide) rh2147500208 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v25 : c2.get 25=count := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h25,h19]
    rw [exec_opimm,v25];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800040b4#32).getLsbD 0=false;decide) rh2147500212 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v19 : c3.get 19=src := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h25,h19]
    rw [exec_op,Core.get_zero,v19,(show alu .add (0 : Word) (src)=src from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800040b6#32).getLsbD 0=false;decide) rh2147500214 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    rw [exec_auipc,show c4.pc=2147500214#32 by rfl,BitVec.add_zero];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800040ba#32).getLsbD 0=false;decide) rh2147500218 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v1 : c5.get 1=2147500214#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h25,h19]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c5.set 1 (2147500218#32+4#32)) ((2147500214#32+108#32) &&& ~~~1)) ram 0 [] [] = _
    rw [show (2147500214#32+108#32) &&& ~~~1=2147500322#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h25,h19]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h25,h19]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h25,h19]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h25,h19]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h25,h19]
  · intro reg h11 h10 h14 h13 h1;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h23,h25,h19,h11,h10,h14,h13,h1]
end E5R.Thermostat.ResponseHeadSetupCLEnd
