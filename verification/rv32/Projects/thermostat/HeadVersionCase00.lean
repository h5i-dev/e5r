import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadVersionCase00
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp pos base limits buf dst : Word) (major dot minor : BitVec 8) (h2 : c.get 2=sp)
(h7 : c.get 7=pos)
(h6 : c.get 6=base)
(h13 : c.get 13=limits)
(h15 : c.get 15=400#32)
(hm : Memory.Block B sp 56) (ha : sp.toNat%4=0)
(hbuf : ramRead ram (sp+44#32) .w=buf) (hdst : ramRead ram (sp+52#32) .w=dst)
(hmmajor : B.inRam (buf+pos+7#32) 1=true) (hmajor : ram (buf+pos+7#32)=major)
(hmdot : B.inRam (base+8#32) 1=true) (hdot : ram (base+8#32)=dot)
(hmminor : B.inRam (base+9#32) 1=true) (hminor : ram (base+9#32)=minor)
(hb0 : taken .ltu (alu .add (BitVec.ofNat 32 major.toNat) (0xffffffc6#32)) (alu .add ((0 : Word)) (0xfffffff6#32))=true)
    (hp : c.pc=0x80002eaa#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002efa#32 ∧
      d.get 10=alu .add (BitVec.ofNat 32 major.toNat) (0xffffffc6#32) ∧ d.get 11=BitVec.ofNat 32 major.toNat ∧ d.get 12=alu .add ((0 : Word)) (0xfffffff6#32) ∧ (∀ r : Reg, r≠10 → r≠11 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (buf) 0x80002eac#32
  let c2 := c1.wr 10 (alu .add (buf) (pos)) 0x80002eae#32
  let c3 := c2.wr 11 (BitVec.ofNat 32 major.toNat) 0x80002eb2#32
  let c4 := c3.wr 10 (alu .add (BitVec.ofNat 32 major.toNat) (0xffffffc6#32)) 0x80002eb6#32
  let c5 := c4.wr 12 (alu .add ((0 : Word)) (0xfffffff6#32)) 0x80002eb8#32
  let c6 := c5.goto 0x80002efa#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495594) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=sp := by simp [Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 11 ha) (Memory.block_access hm (off := 44) (by decide) (by decide)),hbuf];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002eac#32).getLsbD 0=false;decide) hh2147495596 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=buf := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    have v7 : c1.get 7=pos := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    rw [exec_op,v10,v7];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002eae#32).getLsbD 0=false;decide) hh2147495598 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=alu .add (buf) (pos) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    have address : alu .add (buf) (pos)+7#32=buf+pos+7#32 := by rfl
    rw [exec_load,v10,address,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hmmajor,Memory.load_byte,hmajor];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002eb2#32).getLsbD 0=false;decide) hh2147495602 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v11 : c3.get 11=BitVec.ofNat 32 major.toNat := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    rw [exec_opimm,v11];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002eb6#32).getLsbD 0=false;decide) hh2147495606 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002eb8#32).getLsbD 0=false;decide) hh2147495608 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v10 : c5.get 10=alu .add (BitVec.ofNat 32 major.toNat) (0xffffffc6#32) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    have v12 : c5.get 12=alu .add ((0 : Word)) (0xfffffff6#32) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    rw [exec_branch,v10,v12,hb0]
    simp only [ite_true]
    change Observed.interp B img o (jump c5 (0x80002eb8#32+0x42#32)) ram 0 [] []=_
    rw [show 0x80002eb8#32+0x42#32=0x80002efa#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
  · intro reg h10 h11 h12;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15,h10,h11,h12]
end E5R.Thermostat.HeadVersionCase00
