import Projects.thermostat.HeadOwsForwardCase00
import Projects.thermostat.HeadOwsForwardCase01
import Projects.thermostat.HeadOwsForwardCase02
import Projects.thermostat.HttpRequestSpec
namespace E5R.Thermostat.HeadOwsForwardClass
open E5R E5R.Thermostat HttpRequestSpec

def flow (b : BitVec 8) : Word :=
  let v := BitVec.ofNat 32 b.toNat
  if taken .eq v 9#32 then 0x8000309c#32
  else if taken .eq v (alu .add (0 : Word) 32#32) then 0x8000309c#32 else 0x800030c0#32

theorem byte_classes : ∀ b : BitVec 8,
    flow b=(if isOws b.toNat then 0x8000309c#32 else 0x800030c0#32) := by decide +kernel

/-- Actual SP/TAB classifier at the corresponding ELF OWS loop. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc=0x800030b4#32) (h10 : c.get 10=BitVec.ofNat 32 b.toNat) (h12 : c.get 12=9#32) :
    ∃ n d, 1≤n ∧ n≤3 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if isOws b.toNat then 0x8000309c#32 else 0x800030c0#32) ∧
      (∀ r : Reg, r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let v := BitVec.ofNat 32 b.toNat
  cases hb0 : taken .eq (v) (9#32) with
  | false =>
    cases hb1 : taken .eq (v) (alu .add ((0 : Word)) (32#32)) with
    | false =>
      obtain ⟨d,trace,pc,out12,frame,csr⟩ := HeadOwsForwardCase00.contract B c ram v h10 h12 hb0 hb1 hp
      have flowPC : flow b=0x800030c0#32 := by
        simp only [flow,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,Bool.false_eq_true,ite_true,ite_false]
      refine ⟨3,d,by decide,by decide,trace,?_,?_,csr⟩
      · simpa only [byte_classes] using pc.trans flowPC.symm
      · intro r h12
        exact frame r h12
    | true =>
      obtain ⟨d,trace,pc,out12,frame,csr⟩ := HeadOwsForwardCase01.contract B c ram v h10 h12 hb0 hb1 hp
      have flowPC : flow b=0x8000309c#32 := by
        simp only [flow,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,Bool.false_eq_true,ite_true,ite_false]
      refine ⟨3,d,by decide,by decide,trace,?_,?_,csr⟩
      · simpa only [byte_classes] using pc.trans flowPC.symm
      · intro r h12
        exact frame r h12
  | true =>
    obtain ⟨d,trace,pc,frame,csr⟩ := HeadOwsForwardCase02.contract B c ram v h10 h12 hb0 hp
    have flowPC : flow b=0x8000309c#32 := by
      simp only [flow,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨1,d,by decide,by decide,trace,?_,?_,csr⟩
    · simpa only [byte_classes] using pc.trans flowPC.symm
    · intro r h12
      exact frame r 
end E5R.Thermostat.HeadOwsForwardClass
