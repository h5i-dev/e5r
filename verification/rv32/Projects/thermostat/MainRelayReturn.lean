import Projects.thermostat.MainWriteReturnCode
import Projects.thermostat.QuietRam
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
import Projects.thermostat.Memory
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRelayReturn
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (ct len used status : Word) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32) (h18 : c.get 18=2#32) (h22 : c.get 22=1#32)
    (stack : Memory.Block B 0x80ffeb90#32 5232)
    (hct : ramRead ram 0x80fffd38#32 .w=ct) (hlen : ramRead ram 0x80fffd3c#32 .w=len)
    (hused : ramRead ram 0x80fffd40#32 .w=used) (hstatus : extend .h false (ramRead ram 0x80fffd44#32 .h)=status)
    (hflag : ram 0x80fffd46#32=0#8)
    (hp : c.pc=0x8000196c#32) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001710#32 ∧
      d.get 13=0#32 ∧ d.get 9=2164258936#32 ∧ d.get 12=ct ∧ d.get 11=len ∧ d.get 20=used ∧ d.get 10=status ∧ d.get 6=extend .b false (ramRead ram 2164260167#32 .b) ∧ d.get 24=4294967294#32 ∧ (∀ r : Reg, r≠13 → r≠9 → r≠12 → r≠11 → r≠20 → r≠10 → r≠6 → r≠24 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 (0#32) 0x80001970#32
  let c2 := c1.wr 9 (4#32) 0x80001972#32
  let c3 := c2.goto 0x80001998#32
  let c4 := c3.wr 12 (ct) 0x8000199c#32
  let c5 := c4.wr 11 (len) 0x800019a0#32
  let c6 := c5.wr 20 (used) 0x800019a4#32
  let c7 := c6.wr 10 (status) 0x800019a8#32
  let c8 := c7.wr 6 (extend .b false (ramRead ram 2164260167#32 .b)) 0x800019ac#32
  let c9 := c8.wr 9 (2164257679#32) 0x800019b0#32
  let c10 := c9.wr 9 (2164258936#32) 0x800019b4#32
  let c11 := c10.wr 24 (4294967294#32) 0x800019b6#32
  let c12 := c11.goto 0x80001710#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact mw2147490156) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=2164258836#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_load,v8,show 2164258836#32+1330#32=sp+4534#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 4534) (by decide) (by decide))]
    change Observed.interp B img o (.done (c.wr 13 (extend .b false (ramRead ram 2164260166#32 .b)) (c.pc+4#32))) ram 0 [] []=_
    rw [Memory.load_byte,hflag];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80001970#32).getLsbD 0=false;decide) mw2147490160 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v0 : c1.get 0=0#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_opimm,v0,show alu .add 0#32 4#32=4#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80001972#32).getLsbD 0=false;decide) mw2147490162 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v13 : c2.get 13=0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    have v18 : c2.get 18=2#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_branch,v13,v18,show taken .ne 0#32 2#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c2.pc=2147490162#32 from rfl,show 2147490162#32+38#32=2147490200#32 by decide +kernel]
    change Observed.interp B img o (jump c2 2147490200#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80001998#32).getLsbD 0=false;decide) mw2147490200 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v8 : c3.get 8=2164258836#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_load,v8,show 2164258836#32+1316#32=sp+4520#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1130 (by decide +kernel)) (Memory.block_access stack (off := 4520) (by decide) (by decide))]
    change Observed.interp B img o (.done (c3.wr 12 (extend .w true (ramRead ram 2164260152#32 .w)) (c3.pc+4#32))) ram 0 [] []=_
    rw [hct];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x8000199c#32).getLsbD 0=false;decide) mw2147490204 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v8 : c4.get 8=2164258836#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_load,v8,show 2164258836#32+1320#32=sp+4524#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1131 (by decide +kernel)) (Memory.block_access stack (off := 4524) (by decide) (by decide))]
    change Observed.interp B img o (.done (c4.wr 11 (extend .w true (ramRead ram 2164260156#32 .w)) (c4.pc+4#32))) ram 0 [] []=_
    rw [hlen];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800019a0#32).getLsbD 0=false;decide) mw2147490208 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v8 : c5.get 8=2164258836#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_load,v8,show 2164258836#32+1324#32=sp+4528#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1132 (by decide +kernel)) (Memory.block_access stack (off := 4528) (by decide) (by decide))]
    change Observed.interp B img o (.done (c5.wr 20 (extend .w true (ramRead ram 2164260160#32 .w)) (c5.pc+4#32))) ram 0 [] []=_
    rw [hused];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800019a4#32).getLsbD 0=false;decide) mw2147490212 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v8 : c6.get 8=2164258836#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_load,v8,show 2164258836#32+1328#32=sp+4532#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2266 (by decide +kernel)) (Memory.block_access stack (off := 4532) (by decide) (by decide))]
    change Observed.interp B img o (.done (c6.wr 10 (extend .h false (ramRead ram 2164260164#32 .h)) (c6.pc+4#32))) ram 0 [] []=_
    rw [hstatus];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800019a8#32).getLsbD 0=false;decide) mw2147490216 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v8 : c7.get 8=2164258836#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_load,v8,show 2164258836#32+1331#32=sp+4535#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 4535) (by decide) (by decide))]
    change Observed.interp B img o (.done (c7.wr 6 (extend .b false (ramRead ram 2164260167#32 .b)) (c7.pc+4#32))) ram 0 [] []=_
    rfl
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x800019ac#32).getLsbD 0=false;decide) mw2147490220 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v2 : c8.get 2=2164255632#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_opimm,v2,show alu .add 2164255632#32 2047#32=2164257679#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x800019b0#32).getLsbD 0=false;decide) mw2147490224 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v9 : c9.get 9=2164257679#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_opimm,v9,show alu .add 2164257679#32 1257#32=2164258936#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x800019b4#32).getLsbD 0=false;decide) mw2147490228 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v0 : c10.get 0=0#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_opimm,v0,show alu .add 0#32 4294967294#32=4294967294#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x800019b6#32).getLsbD 0=false;decide) mw2147490230 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    rw [exec_jal,show c11.pc=0x800019b6#32 from rfl,show 0x800019b6#32+0xfffffd5a#32=0x80001710#32 by decide +kernel]
    change Observed.interp B img o (jump c11 2147489552#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c12,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.single t11))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · intro reg h13 h9 h12 h11 h20 h10 h6 h24;simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22,h13,h9,h12,h11,h20,h10,h6,h24]
end E5R.Thermostat.MainRelayReturn
