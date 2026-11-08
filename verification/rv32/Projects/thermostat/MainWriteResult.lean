import Projects.thermostat.MainWriteCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainWriteResult
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp sp ct len used status : Word) (h8 : c.get 8=fp) (h2 : c.get 2=sp) (hm : Memory.Block B fp 1332) (ha : fp.toNat%4=0) (hct : ramRead ram (fp+1316#32) .w=ct) (hlen : ramRead ram (fp+1320#32) .w=len) (hused : ramRead ram (fp+1324#32) .w=used) (hstatus : extend .h false (ramRead ram (fp+1328#32) .h)=status)
    (hp : c.pc=0x80001998#32) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001710#32 ∧
      d.get 12=ct ∧ d.get 11=len ∧ d.get 20=used ∧ d.get 10=status ∧ d.get 6=extend .b false (ramRead ram (fp+1331#32) .b) ∧ d.get 9=sp+3304#32 ∧ d.get 24=0xfffffffe#32 ∧ (∀ r : Reg, r≠12 → r≠11 → r≠20 → r≠10 → r≠6 → r≠9 → r≠24 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (ct) 0x8000199c#32
  let c2 := c1.wr 11 (len) 0x800019a0#32
  let c3 := c2.wr 20 (used) 0x800019a4#32
  let c4 := c3.wr 10 (status) 0x800019a8#32
  let c5 := c4.wr 6 (extend .b false (ramRead ram (fp+1331#32) .b)) 0x800019ac#32
  let c6 := c5.wr 9 (sp+2047#32) 0x800019b0#32
  let c7 := c6.wr 9 (sp+3304#32) 0x800019b4#32
  let c8 := c7.wr 24 (0xfffffffe#32) 0x800019b6#32
  let c9 := c8.goto 0x80001710#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact mw2147490200) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=fp := by simp [Core.wr_get_ne,Core.wr_get,h8,h2]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 329 ha) (Memory.block_access hm (off := 1316) (by decide) (by decide)),hct];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000199c#32).getLsbD 0=false;decide) mw2147490204 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=fp := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h2]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 330 ha) (Memory.block_access hm (off := 1320) (by decide) (by decide)),hlen];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800019a0#32).getLsbD 0=false;decide) mw2147490208 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=fp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 331 ha) (Memory.block_access hm (off := 1324) (by decide) (by decide)),hused];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800019a4#32).getLsbD 0=false;decide) mw2147490212 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v8 : c3.get 8=fp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned fp 664 (by omega)) (Memory.block_access hm (off := 1328) (by decide) (by decide))];first | (rw [hstatus];first | rfl | (rw [hp];rfl)) | (change Observed.interp B img o (.done (c3.wr 10 (extend .h false (ramRead ram (fp+1328#32) .h)) 0x800019a8#32)) ram 0 [] [] = _;rw [hstatus];first | rfl | (rw [hp];rfl));first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800019a8#32).getLsbD 0=false;decide) mw2147490216 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v8 : c4.get 8=fp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 1331) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800019ac#32).getLsbD 0=false;decide) mw2147490220 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v2 : c5.get 2=sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800019b0#32).getLsbD 0=false;decide) mw2147490224 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v9 : c6.get 9=sp+2047#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
    rw [exec_opimm,v9]
    change Observed.interp B img o (.done (c6.wr 9 ((sp+2047#32)+1257#32) 0x800019b4#32)) ram 0 [] [] = _
    rw [BitVec.add_assoc];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800019b4#32).getLsbD 0=false;decide) mw2147490228 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x800019b6#32).getLsbD 0=false;decide) mw2147490230 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump (c8.set 0 (c8.pc+2#32)) (c8.pc+0xfffffd5a#32)) ram 0 [] [] = _
    rw [show c8.pc=0x800019b6#32 by rfl,show 0x800019b6#32+0xfffffd5a#32=0x80001710#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c9,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.single t8)))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2]
  · intro reg h12 h11 h20 h10 h6 h9 h24;simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h12,h11,h20,h10,h6,h9,h24]
end E5R.Thermostat.MainWriteResult
