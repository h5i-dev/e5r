-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.SharedResponseFlags
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.SharedResponseFlags
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (fp capacity used : Word)
    (hp : c.pc=0x80001704#32) (h8 : c.get 8=fp) (h22 : c.get 22=1#32) (h20 : c.get 20=used)
    (hm : Memory.Block B fp 668) (ha : fp.toNat%4=0)
    (hcap : ramRead ram (fp+488#32) .w=capacity) (hfit : used.toNat≤capacity.toNat) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,memory ram fp⟩ ∧ d.pc=0x80001728#32 ∧
      d.get 14=capacity ∧ (∀ r : Reg, r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.goto 0x80001708#32
  let b := a.goto 0x8000170c#32
  let z := b.goto 0x80001710#32
  let u := z.wr 14 capacity 0x80001714#32
  let v := u.goto 0x80001718#32
  let d := v.goto 0x80001728#32
  let r1 := ramWrite ram (fp+664#32) 1#32 .b
  let r2 := ramWrite r1 (fp+620#32) 1#32 .b
  let r3 := first ram fp
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,r1⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact sr2147489540) fun o => ?_
    rw [exec_store,h8,h22,interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 664) (by decide) (by decide)),hp];rfl
  have t1 : Quiet.Step B img ⟨a,r1⟩ ⟨b,r2⟩ := by
    refine QuietDet.step_of (by change (0x80001708#32).getLsbD 0=false;decide) sr2147489544 fun o => ?_
    have a8 : a.get 8=fp := h8
    have a22 : a.get 22=1#32 := h22
    rw [exec_store,a8,a22,interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 620) (by decide) (by decide))];rfl
  have t2 : Quiet.Step B img ⟨b,r2⟩ ⟨z,r3⟩ := by
    refine QuietDet.step_of (by change (0x8000170c#32).getLsbD 0=false;decide) sr2147489548 fun o => ?_
    have b8 : b.get 8=fp := h8
    have b22 : b.get 22=1#32 := h22
    rw [exec_store,b8,b22,interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 576) (by decide) (by decide))];rfl
  have t3 : Quiet.Step B img ⟨z,r3⟩ ⟨u,r3⟩ := by
    refine QuietDet.step_of (by change (0x80001710#32).getLsbD 0=false;decide) sr2147489552 fun o => ?_
    have z8 : z.get 8=fp := h8
    rw [exec_load,z8,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 122 ha) (Memory.block_access hm (off := 488) (by decide) (by decide)),read_capacity,hcap];rfl
  have t4 : Quiet.Step B img ⟨u,r3⟩ ⟨v,memory ram fp⟩ := by
    refine QuietDet.step_of (by change (0x80001714#32).getLsbD 0=false;decide) sr2147489556 fun o => ?_
    have u8 : u.get 8=fp := by simp [u,z,b,a,Core.wr_get_ne,h8]
    have u22 : u.get 22=1#32 := by simp [u,z,b,a,Core.wr_get_ne,h22]
    rw [exec_store,u8,u22,interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 532) (by decide) (by decide))];rfl
  have t5 : Quiet.Step B img ⟨v,memory ram fp⟩ ⟨d,memory ram fp⟩ := by
    refine QuietDet.step_of (by change (0x80001718#32).getLsbD 0=false;decide) sr2147489560 fun o => ?_
    have v14 : v.get 14=capacity := by simp [v,u,Core.wr_get]
    have v20 : v.get 20=used := by simp [v,u,z,b,a,Core.wr_get_ne,h20]
    have ht : taken .geu capacity used=true := by simp [taken,BitVec.ult,show ¬capacity.toNat<used.toNat by omega]
    rw [exec_branch,v14,v20,ht]
    simp only [ite_true]
    change interp B img o (jump v (0x80001718#32+16#32)) (memory ram fp) 0 [] = _
    rw [show 0x80001718#32+16#32=0x80001728#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_,?_,by rfl⟩
  · simp [d,v,u,Core.wr_get]
  · intro reg hr;simp [d,v,u,z,b,a,Core.wr_get_ne,hr]

end E5R.Thermostat.SharedResponseFlags
