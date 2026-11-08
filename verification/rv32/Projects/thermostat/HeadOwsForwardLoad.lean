import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadOwsForwardLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf index length : Word) (byte : BitVec 8) (h2 : c.get 2=sp) (h15 : c.get 15=index) (hlength : ramRead ram (sp+48#32) .w=length) (hbuf : ramRead ram (sp+44#32) .w=buf)
(ht : taken .geu index length=false) (hm : B.inRam (buf+index) 1=true) (hbyte : ram (buf+index)=byte) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x800030a4#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800030b4#32 ∧
      d.get 10=BitVec.ofNat 32 byte.toNat ∧ d.get 12=9#32 ∧ (∀ r : Reg, r≠10 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (length) 0x800030a6#32
  let c2 := c1.goto 0x800030aa#32
  let c3 := c2.wr 10 (buf) 0x800030ac#32
  let c4 := c3.wr 10 (buf+index) 0x800030ae#32
  let c5 := c4.wr 10 (BitVec.ofNat 32 byte.toNat) 0x800030b2#32
  let c6 := c5.wr 12 (9#32) 0x800030b4#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496100) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=sp := by simp [Core.wr_get_ne,Core.wr_get,h2,h15]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
     (Memory.block_access stack (off := 48) (by decide) (by decide)),hlength];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800030a6#32).getLsbD 0=false;decide) hh2147496102 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v15 : c1.get 15=index := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h15]
    have v10 : c1.get 10=length := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h15]
    rw [exec_branch,v15,v10,ht];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800030aa#32).getLsbD 0=false;decide) hh2147496106 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v2 : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h15]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 11 ha)
     (Memory.block_access stack (off := 44) (by decide) (by decide)),hbuf];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800030ac#32).getLsbD 0=false;decide) hh2147496108 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v10 : c3.get 10=buf := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h15]
    have v15 : c3.get 15=index := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h15]
    rw [exec_op,v10,v15];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800030ae#32).getLsbD 0=false;decide) hh2147496110 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v10 : c4.get 10=buf+index := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h15]
    rw [exec_load,v10,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm,Memory.load_byte,hbyte];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800030b2#32).getLsbD 0=false;decide) hh2147496114 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h15]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h15]
  · intro reg h10 h12;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h15,h10,h12]
end E5R.Thermostat.HeadOwsForwardLoad
