import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RouteNextIndex
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (pe se plen : Nat) (h22 : c.get 22=BitVec.ofNat 32 pe) (h23 : c.get 23=BitVec.ofNat 32 se) (h18 : c.get 18=BitVec.ofNat 32 plen) (room : pe+1<plen) (bound : plen≤2048)
    (hp : c.pc=0x8000291a#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000287a#32 ∧
      d.get 11=BitVec.ofNat 32 (pe+1) ∧ d.get 10=BitVec.ofNat 32 (se+1) ∧ d.get 22=BitVec.ofNat 32 (pe+1) ∧ (∀ r : Reg, r≠11 → r≠10 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (BitVec.ofNat 32 (pe+1)) 0x8000291e#32
  let c2 := c1.wr 10 (BitVec.ofNat 32 (se+1)) 0x80002922#32
  let c3 := c2.wr 22 (BitVec.ofNat 32 (pe+1)) 0x80002924#32
  let c4 := c3.goto 0x8000287a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494170) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have source : c.get 22=BitVec.ofNat 32 pe := by simp [Core.wr_get_ne,Core.wr_get,h22,h23,h18,room,bound]
    rw [exec_opimm,source]
    try rw [hp]
    change Observed.interp B img o (.done (c.wr 11 (BitVec.ofNat 32 pe+1#32) 0x8000291e#32)) ram 0 [] []=_
    rw [show BitVec.ofNat 32 pe+1#32=BitVec.ofNat 32 (pe+1) by exact (BitVec.ofNat_add pe 1).symm];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000291e#32).getLsbD 0=false;decide) rt2147494174 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have source : c1.get 23=BitVec.ofNat 32 se := by simp [c1,Core.wr_get_ne,Core.wr_get,h22,h23,h18,room,bound]
    rw [exec_opimm,source]
    try rw [hp]
    change Observed.interp B img o (.done (c1.wr 10 (BitVec.ofNat 32 se+1#32) 0x80002922#32)) ram 0 [] []=_
    rw [show BitVec.ofNat 32 se+1#32=BitVec.ofNat 32 (se+1) by exact (BitVec.ofNat_add se 1).symm];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002922#32).getLsbD 0=false;decide) rt2147494178 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have source : c2.get 11=BitVec.ofNat 32 (pe+1) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h22,h23,h18,room,bound]
    rw [exec_op,Core.get_zero,source]
    change Observed.interp B img o (.done (c2.wr 22 (0#32+BitVec.ofNat 32 (pe+1)) 0x80002924#32)) ram 0 [] []=_
    rw [BitVec.zero_add];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002924#32).getLsbD 0=false;decide) rt2147494180 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have start : c3.get 11=BitVec.ofNat 32 (pe+1) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h22,h23,h18,room,bound]
    have last : c3.get 18=BitVec.ofNat 32 plen := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h22,h23,h18,room,bound]
    have compare : taken .ltu (BitVec.ofNat 32 (pe+1)) (BitVec.ofNat 32 plen)=true := by
      simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show pe+1<2^32 by omega),Nat.mod_eq_of_lt (show plen<2^32 by omega)]
      exact decide_eq_true room
    rw [exec_branch,start,last,compare,ite_eq_left rfl,show c3.pc=0x80002924#32 from rfl,show 0x80002924#32+4294967126#32=0x8000287a#32 by decide +kernel]
    change Observed.interp B img o (jump c3 0x8000287a#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h22,h23,h18,room,bound]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h22,h23,h18,room,bound]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h22,h23,h18,room,bound]
  · intro reg h11 h10 h22;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h22,h23,h18,room,bound,h11,h10,h22]
end E5R.Thermostat.RouteNextIndex
