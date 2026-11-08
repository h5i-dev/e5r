import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadVersionCase03
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
(hb0 : taken .ltu (alu .add (BitVec.ofNat 32 major.toNat) (0xffffffc6#32)) (alu .add ((0 : Word)) (0xfffffff6#32))=false)
(hb1 : taken .ne (BitVec.ofNat 32 dot.toNat) (alu .add ((0 : Word)) (46#32))=false)
(hb2 : taken .ltu (alu .add (BitVec.ofNat 32 minor.toNat) (0xffffffc6#32)) (alu .add ((0 : Word)) (0xfffffff6#32))=false)
(hb3 : taken .ne (BitVec.ofNat 32 major.toNat) (alu .add ((0 : Word)) (49#32))=true)
    (hp : c.pc=0x80002eaa#32) :
    ∃ d, Quiet.Steps B img 18 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002efa#32 ∧
      d.get 10=alu .add ((0 : Word)) (49#32) ∧ d.get 11=BitVec.ofNat 32 major.toNat ∧ d.get 12=BitVec.ofNat 32 minor.toNat ∧ d.get 20=alu .add ((0 : Word)) (limits) ∧ d.get 13=alu .add (BitVec.ofNat 32 minor.toNat) (0xffffffc6#32) ∧ d.get 14=alu .add ((0 : Word)) (0xfffffff6#32) ∧ d.get 15=alu .add ((0 : Word)) (505#32) ∧ (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠20 → r≠13 → r≠14 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (buf) 0x80002eac#32
  let c2 := c1.wr 10 (alu .add (buf) (pos)) 0x80002eae#32
  let c3 := c2.wr 11 (BitVec.ofNat 32 major.toNat) 0x80002eb2#32
  let c4 := c3.wr 10 (alu .add (BitVec.ofNat 32 major.toNat) (0xffffffc6#32)) 0x80002eb6#32
  let c5 := c4.wr 12 (alu .add ((0 : Word)) (0xfffffff6#32)) 0x80002eb8#32
  let c6 := c5.goto 0x80002ebc#32
  let c7 := c6.wr 10 (BitVec.ofNat 32 dot.toNat) 0x80002ec0#32
  let c8 := c7.wr 12 (alu .add ((0 : Word)) (46#32)) 0x80002ec4#32
  let c9 := c8.goto 0x80002ec8#32
  let c10 := c9.wr 20 (alu .add ((0 : Word)) (limits)) 0x80002eca#32
  let c11 := c10.wr 12 (BitVec.ofNat 32 minor.toNat) 0x80002ece#32
  let c12 := c11.wr 13 (alu .add (BitVec.ofNat 32 minor.toNat) (0xffffffc6#32)) 0x80002ed2#32
  let c13 := c12.wr 14 (alu .add ((0 : Word)) (0xfffffff6#32)) 0x80002ed4#32
  let c14 := c13.wr 10 (dst) 0x80002ed6#32
  let c15 := c14.goto 0x80002eda#32
  let c16 := c15.wr 10 (alu .add ((0 : Word)) (49#32)) 0x80002ede#32
  let c17 := c16.wr 15 (alu .add ((0 : Word)) (505#32)) 0x80002ee2#32
  let c18 := c17.goto 0x80002efa#32
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
    rfl
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ebc#32).getLsbD 0=false;decide) hh2147495612 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v6 : c6.get 6=base := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    have address : base+8#32=base+8#32 := by rfl
    rw [exec_load,v6,address,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hmdot,Memory.load_byte,hdot];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ec0#32).getLsbD 0=false;decide) hh2147495616 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ec4#32).getLsbD 0=false;decide) hh2147495620 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v10 : c8.get 10=BitVec.ofNat 32 dot.toNat := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    have v12 : c8.get 12=alu .add ((0 : Word)) (46#32) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    rw [exec_branch,v10,v12,hb1]
    rfl
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ec8#32).getLsbD 0=false;decide) hh2147495624 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v13 : c9.get 13=limits := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    rw [exec_op,Core.get_zero,v13];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80002eca#32).getLsbD 0=false;decide) hh2147495626 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v6 : c10.get 6=base := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    have address : base+9#32=base+9#32 := by rfl
    rw [exec_load,v6,address,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hmminor,Memory.load_byte,hminor];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ece#32).getLsbD 0=false;decide) hh2147495630 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v12 : c11.get 12=BitVec.ofNat 32 minor.toNat := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ed2#32).getLsbD 0=false;decide) hh2147495634 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ed4#32).getLsbD 0=false;decide) hh2147495636 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v2 : c13.get 2=sp := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 13 ha) (Memory.block_access hm (off := 52) (by decide) (by decide)),hdst];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ed6#32).getLsbD 0=false;decide) hh2147495638 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v13 : c14.get 13=alu .add (BitVec.ofNat 32 minor.toNat) (0xffffffc6#32) := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    have v14 : c14.get 14=alu .add ((0 : Word)) (0xfffffff6#32) := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    rw [exec_branch,v13,v14,hb2]
    rfl
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x80002eda#32).getLsbD 0=false;decide) hh2147495642 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ede#32).getLsbD 0=false;decide) hh2147495646 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ee2#32).getLsbD 0=false;decide) hh2147495650 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) ram 0 [] [] = ⟨.ok c18 ram [],[]⟩
    have v11 : c17.get 11=BitVec.ofNat 32 major.toNat := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    have v10 : c17.get 10=alu .add ((0 : Word)) (49#32) := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
    rw [exec_branch,v11,v10,hb3]
    simp only [ite_true]
    change Observed.interp B img o (jump c17 (0x80002ee2#32+0x18#32)) ram 0 [] []=_
    rw [show 0x80002ee2#32+0x18#32=0x80002efa#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c18,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.single t17))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
  · simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15]
  · intro reg h10 h11 h12 h20 h13 h14 h15;simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h7,h6,h13,h15,h10,h11,h12,h20,h13,h14,h15]
end E5R.Thermostat.HeadVersionCase03
