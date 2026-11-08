import Projects.thermostat.MainWriteReturnCode
import Projects.thermostat.QuietRam
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainTempReturn
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32

def memory (ram : Word → BitVec 8) (ct len used status : Word) :=
  ramWrite (ramWrite (ram) (sp+3824#32) (1#32) .b) (sp+3780#32) (1#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (ct len used status : Word) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32) (h18 : c.get 18=2#32) (h22 : c.get 22=1#32)
    (stack : Memory.Block B 0x80ffeb90#32 5232)
    (hct : ramRead ram 0x80fffd38#32 .w=ct) (hlen : ramRead ram 0x80fffd3c#32 .w=len)
    (hused : ramRead ram 0x80fffd40#32 .w=used) (hstatus : extend .h false (ramRead ram 0x80fffd44#32 .h)=status)
    (hflag : ram 0x80fffd46#32=0#8)
    (hp : c.pc=0x80001604#32) :
    ∃ d, Quiet.Steps B img 13 ⟨c,ram⟩ ⟨d,memory ram ct len used status⟩ ∧ d.pc=0x80001710#32 ∧
      d.get 13=0#32 ∧ d.get 12=ct ∧ d.get 11=len ∧ d.get 20=used ∧ d.get 10=status ∧ d.get 6=extend .b false (ramRead ram 2164260167#32 .b) ∧ d.get 9=2164258936#32 ∧ d.get 24=4294967294#32 ∧ (∀ r : Reg, r≠13 → r≠12 → r≠11 → r≠20 → r≠10 → r≠6 → r≠9 → r≠24 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 (0#32) 0x80001608#32
  let c2 := c1.goto 0x800016a6#32
  let c3 := c2.wr 12 (ct) 0x800016aa#32
  let c4 := c3.wr 11 (len) 0x800016ae#32
  let c5 := c4.wr 20 (used) 0x800016b2#32
  let c6 := c5.wr 10 (status) 0x800016b6#32
  let c7 := c6.wr 6 (extend .b false (ramRead ram 2164260167#32 .b)) 0x800016ba#32
  let c8 := c7.wr 9 (2164257679#32) 0x800016be#32
  let c9 := c8.wr 9 (2164258936#32) 0x800016c2#32
  let c10 := c9.wr 24 (4294967294#32) 0x800016c4#32
  let c11 := c10.goto 0x80001708#32
  let r1 := ramWrite ram (sp+3824#32) (1#32) .b
  let c12 := c11.goto 0x8000170c#32
  let r2 := ramWrite r1 (sp+3780#32) (1#32) .b
  let c13 := c12.goto 0x80001710#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact wr2147489284) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=2164258836#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_load,v8,show 2164258836#32+1330#32=sp+4534#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 4534) (by decide) (by decide))]
    change Observed.interp B img o (.done (c.wr 13 (extend .b false (ramRead ram 2164260166#32 .b)) (c.pc+4#32))) ram 0 [] []=_
    rw [Memory.load_byte,hflag];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80001608#32).getLsbD 0=false;decide) wr2147489288 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v13 : c1.get 13=0#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    have v18 : c1.get 18=2#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_branch,v13,v18,show taken .ne 0#32 2#32=true by decide +kernel]
    rw [ite_eq_left rfl,show c1.pc=2147489288#32 from rfl,show 2147489288#32+158#32=2147489446#32 by decide +kernel]
    change Observed.interp B img o (jump c1 2147489446#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800016a6#32).getLsbD 0=false;decide) wr2147489446 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=2164258836#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_load,v8,show 2164258836#32+1316#32=sp+4520#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1130 (by decide +kernel)) (Memory.block_access stack (off := 4520) (by decide) (by decide))]
    change Observed.interp B img o (.done (c2.wr 12 (extend .w true (ramRead ram 2164260152#32 .w)) (c2.pc+4#32))) ram 0 [] []=_
    rw [hct];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800016aa#32).getLsbD 0=false;decide) wr2147489450 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v8 : c3.get 8=2164258836#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_load,v8,show 2164258836#32+1320#32=sp+4524#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1131 (by decide +kernel)) (Memory.block_access stack (off := 4524) (by decide) (by decide))]
    change Observed.interp B img o (.done (c3.wr 11 (extend .w true (ramRead ram 2164260156#32 .w)) (c3.pc+4#32))) ram 0 [] []=_
    rw [hlen];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800016ae#32).getLsbD 0=false;decide) wr2147489454 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v8 : c4.get 8=2164258836#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_load,v8,show 2164258836#32+1324#32=sp+4528#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1132 (by decide +kernel)) (Memory.block_access stack (off := 4528) (by decide) (by decide))]
    change Observed.interp B img o (.done (c4.wr 20 (extend .w true (ramRead ram 2164260160#32 .w)) (c4.pc+4#32))) ram 0 [] []=_
    rw [hused];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800016b2#32).getLsbD 0=false;decide) wr2147489458 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v8 : c5.get 8=2164258836#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_load,v8,show 2164258836#32+1328#32=sp+4532#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2266 (by decide +kernel)) (Memory.block_access stack (off := 4532) (by decide) (by decide))]
    change Observed.interp B img o (.done (c5.wr 10 (extend .h false (ramRead ram 2164260164#32 .h)) (c5.pc+4#32))) ram 0 [] []=_
    rw [hstatus];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800016b6#32).getLsbD 0=false;decide) wr2147489462 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v8 : c6.get 8=2164258836#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_load,v8,show 2164258836#32+1331#32=sp+4535#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 4535) (by decide) (by decide))]
    change Observed.interp B img o (.done (c6.wr 6 (extend .b false (ramRead ram 2164260167#32 .b)) (c6.pc+4#32))) ram 0 [] []=_
    rfl
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800016ba#32).getLsbD 0=false;decide) wr2147489466 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v2 : c7.get 2=2164255632#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_opimm,v2,show alu .add 2164255632#32 2047#32=2164257679#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x800016be#32).getLsbD 0=false;decide) wr2147489470 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v9 : c8.get 9=2164257679#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_opimm,v9,show alu .add 2164257679#32 1257#32=2164258936#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x800016c2#32).getLsbD 0=false;decide) wr2147489474 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v0 : c9.get 0=0#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_opimm,v0,show alu .add 0#32 4294967294#32=4294967294#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x800016c4#32).getLsbD 0=false;decide) wr2147489476 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c10 2147489544#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,r1⟩ := by
    refine Quiet.step_of (by change (0x80001708#32).getLsbD 0=false;decide) wr2147489544 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 r1 [],[]⟩
    have v8 : c11.get 8=2164258836#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    have v22 : c11.get 22=1#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_store,v8,v22,show 2164258836#32+620#32=sp+3824#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3824) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r1⟩ ⟨c13,r2⟩ := by
    refine Quiet.step_of (by change (0x8000170c#32).getLsbD 0=false;decide) wr2147489548 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r1 0 [] [] = ⟨.ok c13 r2 [],[]⟩
    have v8 : c12.get 8=2164258836#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    have v22 : c12.get 22=1#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
    rw [exec_store,v8,v22,show 2164258836#32+576#32=sp+3780#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3780) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c13,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.single t12)))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22]
  · intro reg h13 h12 h11 h20 h10 h6 h9 h24;simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h18,h22,h13,h12,h11,h20,h10,h6,h9,h24]

/-- The real future flag writes preserve App/RX/metadata/body/output. -/
theorem frame (ram : Word → BitVec 8) (ct len used status : Word) (off size : Nat) (bound : off+size≤5232)
    (apart : off+size≤3780 ∨ 3869≤off) : ViewFrame.Region ram (memory ram ct len used status) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold memory
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    exact FrameOffsets.ne sp off 3780 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    exact FrameOffsets.ne sp off 3824 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h <;>omega))]
end E5R.Thermostat.MainTempReturn
