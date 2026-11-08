import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HeaderSetup
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainCloseSetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (req rawPtr : Word) (rawLength count : Nat) (bounded : count≤16) (h10 : c.get 10=req) (h11 : c.get 11=BitVec.ofNat 32 count)
    (object : Memory.Block B req 336) (aligned : req.toNat%4=0)
    (pointer : ramRead ram (req+328#32) .w=rawPtr) (length : ramRead ram (req+332#32) .w=BitVec.ofNat 32 rawLength)
    (hp : c.pc=0x80002418#32) :
    ∃ d, Quiet.Steps B img 20 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000247a#32 ∧
      d.get 13=req+32#32 ∧ d.get 11=BitVec.ofNat 32 (16*count) ∧ d.get 16=rawPtr ∧ d.get 12=BitVec.ofNat 32 rawLength ∧ d.get 17=(req+32#32)+BitVec.ofNat 32 (16*count) ∧ d.get 5=10#32 ∧ d.get 6=99#32 ∧ d.get 7=111#32 ∧ d.get 28=110#32 ∧ d.get 29=101#32 ∧ d.get 30=116#32 ∧ d.get 31=105#32 ∧ d.get 8=44#32 ∧ d.get 9=23#32 ∧ d.get 18=5#32 ∧ d.get 19=108#32 ∧ d.get 21=0x80001b#32 ∧ d.get 20=115#32 ∧ (∀ r : Reg, r≠13 → r≠11 → r≠16 → r≠12 → r≠17 → r≠5 → r≠6 → r≠7 → r≠28 → r≠29 → r≠30 → r≠31 → r≠8 → r≠9 → r≠18 → r≠19 → r≠21 → r≠20 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 (req+32#32) 0x8000241c#32
  let c2 := c1.wr 11 (BitVec.ofNat 32 (16*count)) 0x8000241e#32
  let c3 := c2.wr 16 (rawPtr) 0x80002422#32
  let c4 := c3.wr 12 (BitVec.ofNat 32 rawLength) 0x80002426#32
  let c5 := c4.wr 17 ((req+32#32)+BitVec.ofNat 32 (16*count)) 0x8000242a#32
  let c6 := c5.wr 5 (10#32) 0x8000242c#32
  let c7 := c6.wr 6 (99#32) 0x80002430#32
  let c8 := c7.wr 7 (111#32) 0x80002434#32
  let c9 := c8.wr 28 (110#32) 0x80002438#32
  let c10 := c9.wr 29 (101#32) 0x8000243c#32
  let c11 := c10.wr 30 (116#32) 0x80002440#32
  let c12 := c11.wr 31 (105#32) 0x80002444#32
  let c13 := c12.wr 8 (44#32) 0x80002448#32
  let c14 := c13.wr 9 (23#32) 0x8000244a#32
  let c15 := c14.wr 18 (5#32) 0x8000244c#32
  let c16 := c15.wr 19 (108#32) 0x80002450#32
  let c17 := c16.wr 21 (0x800000#32) 0x80002454#32
  let c18 := c17.wr 20 (115#32) 0x80002458#32
  let c19 := c18.wr 21 (0x80001b#32) 0x8000245a#32
  let c20 := c19.goto 0x8000247a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147492888) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v10 : c.get 10=req := by simp [Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000241c#32).getLsbD 0=false;decide) re2147492892 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v11 : c1.get 11=BitVec.ofNat 32 count := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_opimm,v11]
    change Observed.interp B img o (.done (c1.wr 11 (BitVec.ofNat 32 count <<< 4) 0x8000241e#32)) ram 0 [] []=_
    rw [HeaderSetup.shift_count count bounded];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000241e#32).getLsbD 0=false;decide) re2147492894 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=req := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_load,v10,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned req 82 aligned) (Memory.block_access object (off := 328) (by decide) (by decide)),pointer];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002422#32).getLsbD 0=false;decide) re2147492898 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v10 : c3.get 10=req := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_load,v10,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned req 83 aligned) (Memory.block_access object (off := 332) (by decide) (by decide)),length];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002426#32).getLsbD 0=false;decide) re2147492902 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v13 : c4.get 13=req+32#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have v11 : c4.get 11=BitVec.ofNat 32 (16*count) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,v13,v11];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x8000242a#32).getLsbD 0=false;decide) re2147492906 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x8000242c#32).getLsbD 0=false;decide) re2147492908 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80002430#32).getLsbD 0=false;decide) re2147492912 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80002434#32).getLsbD 0=false;decide) re2147492916 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80002438#32).getLsbD 0=false;decide) re2147492920 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x8000243c#32).getLsbD 0=false;decide) re2147492924 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80002440#32).getLsbD 0=false;decide) re2147492928 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80002444#32).getLsbD 0=false;decide) re2147492932 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80002448#32).getLsbD 0=false;decide) re2147492936 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x8000244a#32).getLsbD 0=false;decide) re2147492938 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x8000244c#32).getLsbD 0=false;decide) re2147492940 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x80002450#32).getLsbD 0=false;decide) re2147492944 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,ram⟩ := by
    refine Quiet.step_of (by change (0x80002454#32).getLsbD 0=false;decide) re2147492948 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) ram 0 [] [] = ⟨.ok c18 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,ram⟩ ⟨c19,ram⟩ := by
    refine Quiet.step_of (by change (0x80002458#32).getLsbD 0=false;decide) re2147492952 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) ram 0 [] [] = ⟨.ok c19 ram [],[]⟩
    have v21 : c18.get 21=0x800000#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_opimm,v21];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,ram⟩ ⟨c20,ram⟩ := by
    refine Quiet.step_of (by change (0x8000245a#32).getLsbD 0=false;decide) re2147492954 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) ram 0 [] [] = ⟨.ok c20 ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c19 0x8000247a#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c20,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.single t19))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · intro reg h13 h11 h16 h12 h17 h5 h6 h7 h28 h29 h30 h31 h8 h9 h18 h19 h21 h20;simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h11,h16,h12,h17,h5,h6,h7,h28,h29,h30,h31,h8,h9,h18,h19,h21,h20]
end E5R.Thermostat.MainCloseSetup
