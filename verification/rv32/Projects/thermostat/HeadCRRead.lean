import Projects.thermostat.HttpParseCode00
import Projects.thermostat.HeadByteFacts
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
namespace E5R.Thermostat.HeadCRRead
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (b : BitVec 8)
    (hp : c.pc=0x80002cb0#32) (h5 : c.get 5=p)
    (hm : B.inRam (p+1#32) 1=true) (hbyte : ram (p+1#32)=b) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if b.toNat=10 then 0x80002cba#32 else 0x80002d5a#32) ∧
      d.get 15=BitVec.ofNat 32 b.toNat ∧ d.get 17=10#32 ∧
      (∀ r : Reg, r≠15 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 15 (BitVec.ofNat 32 b.toNat) 0x80002cb4#32
  let e := a.wr 17 10#32 0x80002cb6#32
  let d := e.goto (if b.toNat=10 then 0x80002cba#32 else 0x80002d5a#32)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495088) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
    rw [exec_load,h5,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm,
      Memory.load_byte,hbyte,hp]
    rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨e,ram⟩ := by
    refine Quiet.step_of (by change (0x80002cb4#32).getLsbD 0=false;decide) hh2147495092 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have t2 : Quiet.Step B img ⟨e,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x80002cb6#32).getLsbD 0=false;decide) hh2147495094 fun o => ?_
    have v15 : e.get 15=BitVec.ofNat 32 b.toNat := by simp [e,a,Core.wr_get_ne,Core.wr_get]
    have v17 : e.get 17=10#32 := by simp [e,Core.wr_get]
    have ht : taken .ne (BitVec.ofNat 32 b.toNat) 10#32= !(decide (b.toNat=10)) := by
      change Bool.not (taken .eq (BitVec.ofNat 32 b.toNat) 10#32)=Bool.not (decide (b.toNat=10))
      rw [HeadByteFacts.lf]
    rw [exec_branch,v15,v17,ht]
    by_cases he : b.toNat=10
    · simp only [d,he,decide_true,Bool.not_true,ite_true]
      rfl
    · simp only [d,he,decide_false,Bool.not_false,ite_true,ite_false]
      change Observed.interp B img o (jump e (0x80002cb6#32+0xa4#32)) ram 0 [] []=_
      rw [show 0x80002cb6#32+0xa4#32=0x80002d5a#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.step t0 (.step t1 (.single t2)),rfl,by simp [d,e,a,Core.wr_get_ne,Core.wr_get],
    by simp [d,e,Core.wr_get],fun r h15 h17 => by simp [d,e,a,Core.wr_get_ne,h15,h17],rfl⟩
end E5R.Thermostat.HeadCRRead
