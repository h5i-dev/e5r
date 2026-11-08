import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadOwsBackLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf index length : Word) (byte : BitVec 8) (h2 : c.get 2=sp) (h25 : c.get 25=index) (hlength : ramRead ram (sp+48#32) .w=length) (hbuf : ramRead ram (sp+44#32) .w=buf)
(ht : taken .geu (index+0xffffffff#32) length=false) (hm : B.inRam ((buf+index)+0xffffffff#32) 1=true)
(hbyte : ram ((buf+index)+0xffffffff#32)=byte) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x800030d0#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800030e2#32 ∧
      d.get 10=index+0xffffffff#32 ∧ d.get 13=BitVec.ofNat 32 byte.toNat ∧ (∀ r : Reg, r≠10 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (index+0xffffffff#32) 0x800030d4#32
  let c2 := c1.wr 13 (length) 0x800030d6#32
  let c3 := c2.goto 0x800030da#32
  let c4 := c3.wr 13 (buf) 0x800030dc#32
  let c5 := c4.wr 13 (buf+index) 0x800030de#32
  let c6 := c5.wr 13 (BitVec.ofNat 32 byte.toNat) 0x800030e2#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496144) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h25];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800030d4#32).getLsbD 0=false;decide) hh2147496148 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h25]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
     (Memory.block_access stack (off := 48) (by decide) (by decide)),hlength];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800030d6#32).getLsbD 0=false;decide) hh2147496150 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=index+0xffffffff#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h25]
    have v13 : c2.get 13=length := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h25]
    rw [exec_branch,v10,v13,ht];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800030da#32).getLsbD 0=false;decide) hh2147496154 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v2 : c3.get 2=sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h25]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 11 ha)
     (Memory.block_access stack (off := 44) (by decide) (by decide)),hbuf];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800030dc#32).getLsbD 0=false;decide) hh2147496156 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v13 : c4.get 13=buf := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h25]
    have v25 : c4.get 25=index := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h25]
    rw [exec_op,v13,v25];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800030de#32).getLsbD 0=false;decide) hh2147496158 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v13 : c5.get 13=buf+index := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h25]
    rw [exec_load,v13,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm,Memory.load_byte,hbyte];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h25]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h25]
  · intro reg h10 h13;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h25,h10,h13]
end E5R.Thermostat.HeadOwsBackLoad
