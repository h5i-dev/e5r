import Projects.thermostat.MainMethodDecodeCode
import Projects.thermostat.MainMethodByteMath
import Projects.thermostat.QuietBranch
import Projects.thermostat.Memory
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainMethodLast
open E5R E5R.Thermostat

/-- The shared last-character check, including the actual fallback to Other. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (base offset candidate : Word) (literal : Nat) (byte : BitVec 8)
    (hp : c.pc=0x80001154#32) (h15 : c.get 15=base) (h17 : c.get 17=offset)
    (h14 : c.get 14=candidate) (h16 : c.get 16=BitVec.ofNat 32 literal)
    (bound : literal≤255) (memory : B.inRam (base+offset) 1=true) (data : ram (base+offset)=byte) :
    ∃ n d, 3≤n ∧ n≤4 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001160#32 ∧
      d.get 14=(if byte.toNat=literal then candidate else 6#32) ∧
      (∀ r : Reg, r≠14 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 15 (base+offset) 0x80001156#32
  let b := a.wr 15 (BitVec.ofNat 32 byte.toNat) 0x8000115a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488084) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_op,h15,h17,hp];rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine Quiet.step_of (by change (0x80001156#32).getLsbD 0=false;decide) re2147488086 fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] [] = ⟨.ok b ram [],[]⟩
    have a15 : a.get 15=base+offset := by simp [a,Core.wr_get]
    rw [exec_load,a15,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) memory,Memory.load_byte,data];rfl
  have b15 : b.get 15=BitVec.ofNat 32 byte.toNat := by simp [b,Core.wr_get]
  have b16 : b.get 16=BitVec.ofNat 32 literal := by simp [b,a,Core.wr_get_ne,h16]
  obtain ⟨e,t2,pe,er,ec⟩ := QuietBranch.contract B img b ram 0x8000115a#32 4#32 6#32 .eq 15 16 (decide (byte.toNat=literal)) rfl (by decide) (by decide) re2147488090
    (by rw [b15,b16];exact MainMethodByteMath.eqTest byte literal bound)
  have frame (r : Reg) (safe : r≠15) : e.get r=c.get r := (er r).trans (by simp [b,a,Core.wr_get_ne,safe])
  by_cases hit : byte.toNat=literal
  · have pc : e.pc=0x80001160#32 := by simpa only [hit,decide_true,ite_true,show 0x8000115a#32+6#32=0x80001160#32 by decide +kernel] using pe
    refine ⟨3,e,by decide,by decide,(Quiet.Steps.single t0).trans ((Quiet.Steps.single t1).trans t2),pc,?_,fun r _ h15 => frame r h15,ec⟩
    simpa only [hit,ite_true] using (frame 14 (by decide)).trans h14
  · have pc : e.pc=0x8000115e#32 := by simpa only [hit,decide_false,Bool.false_eq_true,ite_false,show 0x8000115a#32+4#32=0x8000115e#32 by decide +kernel] using pe
    let d := e.wr 14 6#32 0x80001160#32
    have t3 : Quiet.Step B img ⟨e,ram⟩ ⟨d,ram⟩ := by
      refine Quiet.step_of (by rw [pc];decide) (by rw [pc];exact re2147488094) fun o => ?_
      change Observed.interp B img o (exec e _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
      rw [exec_opimm,Core.get_zero,pc];rfl
    refine ⟨4,d,by decide,by decide,((Quiet.Steps.single t0).trans ((Quiet.Steps.single t1).trans t2)).trans (.single t3),rfl,?_,?_,ec⟩
    · simp only [hit,ite_false];simp [d,Core.wr_get]
    · intro r h14 h15
      exact (show d.get r=e.get r by simp [d,Core.wr_get_ne,h14]).trans (frame r h15)
end E5R.Thermostat.MainMethodLast
