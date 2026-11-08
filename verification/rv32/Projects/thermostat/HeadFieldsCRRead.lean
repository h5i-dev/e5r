import Projects.thermostat.HttpParseCode
import Projects.thermostat.HeadByteFacts
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
namespace E5R.Thermostat.HeadFieldsCRRead
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (byte : BitVec 8)
    (hp : c.pc=0x80002fa8#32) (h15 : c.get 15=p) (h16 : c.get 16=10#32)
    (hm : B.inRam (p+1#32) 1=true) (hbyte : ram (p+1#32)=byte) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat=10 then 0x80002fb4#32 else 0x8000342c#32) ∧
      d.get 10=BitVec.ofNat 32 byte.toNat ∧ d.get 1=400#32 ∧
      (∀ r : Reg, r≠10 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 10 (BitVec.ofNat 32 byte.toNat) 0x80002fac#32
  let e := a.wr 1 400#32 0x80002fb0#32
  let d := e.goto (if byte.toNat=10 then 0x80002fb4#32 else 0x8000342c#32)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495848) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
    rw [exec_load,h15,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm,Memory.load_byte,hbyte,hp]
    rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨e,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fac#32).getLsbD 0=false;decide) hh2147495852 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have t2 : Quiet.Step B img ⟨e,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fb0#32).getLsbD 0=false;decide) hh2147495856 fun o => ?_
    have v10 : e.get 10=BitVec.ofNat 32 byte.toNat := by simp [e,a,Core.wr_get_ne,Core.wr_get]
    have v16 : e.get 16=10#32 := by simp [e,a,Core.wr_get_ne,h16]
    have test : taken .ne (BitVec.ofNat 32 byte.toNat) 10#32= !(decide (byte.toNat=10)) := by
      change Bool.not (taken .eq (BitVec.ofNat 32 byte.toNat) 10#32)=Bool.not (decide (byte.toNat=10))
      rw [HeadByteFacts.lf]
    rw [exec_branch,v10,v16,test]
    by_cases lf : byte.toNat=10
    · simp only [d,lf,decide_true,Bool.not_true,ite_true];rfl
    · simp only [d,lf,decide_false,Bool.not_false,ite_true,ite_false]
      change Observed.interp B img o (jump e (0x80002fb0#32+0x47c#32)) ram 0 [] [] = _
      rw [show 0x80002fb0#32+0x47c#32=0x8000342c#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  refine ⟨d,.step t0 (.step t1 (.single t2)),rfl,?_,?_,?_,rfl⟩
  · simp [d,e,a,Core.wr_get_ne,Core.wr_get]
  · simp [d,e,Core.wr_get]
  · intro r h10 h1;simp [d,e,a,Core.wr_get_ne,h10,h1]
end E5R.Thermostat.HeadFieldsCRRead
