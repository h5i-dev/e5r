import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HeaderInput
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainCloseHeaderBounds
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (cell : Word) (rawLength : Nat) (e : HeaderSpec.Entry) (stored : HeaderInput.Cell B ram cell rawLength e) (limit : rawLength≤2048)
    (h13 : c.get 13=cell) (h12 : c.get 12=BitVec.ofNat 32 rawLength)
    (hp : c.pc=0x8000247a#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002492#32 ∧
      d.get 15=BitVec.ofNat 32 e.nameStart ∧ d.get 14=BitVec.ofNat 32 e.nameEnd ∧ d.get 10=BitVec.ofNat 32 e.valueStart ∧ d.get 11=BitVec.ofNat 32 e.valueEnd ∧ (∀ r : Reg, r≠15 → r≠14 → r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 15 (BitVec.ofNat 32 e.nameStart) 0x8000247c#32
  let c2 := c1.wr 14 (BitVec.ofNat 32 e.nameEnd) 0x8000247e#32
  let c3 := c2.goto 0x80002482#32
  let c4 := c3.goto 0x80002486#32
  let c5 := c4.wr 10 (BitVec.ofNat 32 e.valueStart) 0x80002488#32
  let c6 := c5.wr 11 (BitVec.ofNat 32 e.valueEnd) 0x8000248a#32
  let c7 := c6.goto 0x8000248e#32
  let c8 := c7.goto 0x80002492#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147492986) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v13 : c.get 13=cell := by simp [Core.wr_get_ne,Core.wr_get,h13,h12]
    rw [exec_load,v13,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned cell 0 stored.aligned) (Memory.block_access stored.block (off := 0) (by decide) (by decide))]
    rw [show BitVec.ofNat 32 (4*0)=0#32 from rfl,BitVec.add_zero,stored.nameStart];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000247c#32).getLsbD 0=false;decide) re2147492988 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v13 : c1.get 13=cell := by simp [c1,Core.wr_get_ne,Core.wr_get,h13,h12]
    rw [exec_load,v13,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned cell 1 stored.aligned) (Memory.block_access stored.block (off := 4) (by decide) (by decide))]
    simp only [BitVec.add_zero,stored.nameEnd];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000247e#32).getLsbD 0=false;decide) re2147492990 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v14 : c2.get 14=BitVec.ofNat 32 e.nameEnd := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
    have v15 : c2.get 15=BitVec.ofNat 32 e.nameStart := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
    have bounds := stored.bounds
    unfold HeaderSpec.Bounds at bounds
    have compare : taken .ltu (BitVec.ofNat 32 e.nameEnd) (BitVec.ofNat 32 e.nameStart)=false := by
      simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : e.nameEnd<2^32),Nat.mod_eq_of_lt (by omega : e.nameStart<2^32)]
      simp only [decide_eq_false_iff_not]
      omega
    rw [exec_branch,v14,v15,compare];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002482#32).getLsbD 0=false;decide) re2147492994 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v12 : c3.get 12=BitVec.ofNat 32 rawLength := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
    have v14 : c3.get 14=BitVec.ofNat 32 e.nameEnd := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
    have bounds := stored.bounds
    unfold HeaderSpec.Bounds at bounds
    have compare : taken .ltu (BitVec.ofNat 32 rawLength) (BitVec.ofNat 32 e.nameEnd)=false := by
      simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : rawLength<2^32),Nat.mod_eq_of_lt (by omega : e.nameEnd<2^32)]
      simp only [decide_eq_false_iff_not]
      omega
    rw [exec_branch,v12,v14,compare];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002486#32).getLsbD 0=false;decide) re2147492998 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v13 : c4.get 13=cell := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
    rw [exec_load,v13,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned cell 2 stored.aligned) (Memory.block_access stored.block (off := 8) (by decide) (by decide))]
    simp only [BitVec.add_zero,stored.valueStart];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002488#32).getLsbD 0=false;decide) re2147493000 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v13 : c5.get 13=cell := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
    rw [exec_load,v13,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned cell 3 stored.aligned) (Memory.block_access stored.block (off := 12) (by decide) (by decide))]
    simp only [BitVec.add_zero,stored.valueEnd];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x8000248a#32).getLsbD 0=false;decide) re2147493002 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v11 : c6.get 11=BitVec.ofNat 32 e.valueEnd := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
    have v10 : c6.get 10=BitVec.ofNat 32 e.valueStart := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
    have bounds := stored.bounds
    unfold HeaderSpec.Bounds at bounds
    have compare : taken .ltu (BitVec.ofNat 32 e.valueEnd) (BitVec.ofNat 32 e.valueStart)=false := by
      simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : e.valueEnd<2^32),Nat.mod_eq_of_lt (by omega : e.valueStart<2^32)]
      simp only [decide_eq_false_iff_not]
      omega
    rw [exec_branch,v11,v10,compare];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x8000248e#32).getLsbD 0=false;decide) re2147493006 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v12 : c7.get 12=BitVec.ofNat 32 rawLength := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
    have v11 : c7.get 11=BitVec.ofNat 32 e.valueEnd := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
    have bounds := stored.bounds
    unfold HeaderSpec.Bounds at bounds
    have compare : taken .ltu (BitVec.ofNat 32 rawLength) (BitVec.ofNat 32 e.valueEnd)=false := by
      simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : rawLength<2^32),Nat.mod_eq_of_lt (by omega : e.valueEnd<2^32)]
      simp only [decide_eq_false_iff_not]
      omega
    rw [exec_branch,v12,v11,compare];first | rfl | (rw [hp];rfl)
  refine ⟨c8,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.single t7))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12]
  · intro reg h15 h14 h10 h11;simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h12,h15,h14,h10,h11]
end E5R.Thermostat.MainCloseHeaderBounds
