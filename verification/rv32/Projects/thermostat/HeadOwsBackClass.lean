import Projects.thermostat.HeadOwsBackCase00
import Projects.thermostat.HeadOwsBackCase01
import Projects.thermostat.HeadOwsBackCase02
import Projects.thermostat.HttpRequestSpec
namespace E5R.Thermostat.HeadOwsBackClass
open E5R E5R.Thermostat HttpRequestSpec

def flow (b : BitVec 8) : Word :=
  let v := BitVec.ofNat 32 b.toNat
  if taken .eq v (alu .add (0 : Word) 9#32) then 0x800030ca#32
  else if taken .eq v (alu .add (0 : Word) 32#32) then 0x800030ca#32 else 0x800030fa#32

theorem byte_classes : ∀ b : BitVec 8,
    flow b=(if isOws b.toNat then 0x800030ca#32 else 0x800030fa#32) := by decide +kernel

/-- Actual SP/TAB classifier at the corresponding ELF OWS loop. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc=0x800030e2#32) (h13 : c.get 13=BitVec.ofNat 32 b.toNat)  :
    ∃ n d, 1≤n ∧ n≤5 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if isOws b.toNat then 0x800030ca#32 else 0x800030fa#32) ∧
      (∀ r : Reg, r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let v := BitVec.ofNat 32 b.toNat
  cases hb0 : taken .eq (v) (alu .add ((0 : Word)) (9#32)) with
  | false =>
    cases hb1 : taken .eq (v) (alu .add ((0 : Word)) (32#32)) with
    | false =>
      obtain ⟨d,trace,pc,out12,frame,csr⟩ := HeadOwsBackCase00.contract B c ram v h13 hb0 hb1 hp
      have flowPC : flow b=0x800030fa#32 := by
        simp only [flow,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,Bool.false_eq_true,ite_true,ite_false]
      refine ⟨5,d,by decide,by decide,trace,?_,?_,csr⟩
      · simpa only [byte_classes] using pc.trans flowPC.symm
      · intro r h12
        exact frame r h12
    | true =>
      obtain ⟨d,trace,pc,out12,frame,csr⟩ := HeadOwsBackCase01.contract B c ram v h13 hb0 hb1 hp
      have flowPC : flow b=0x800030ca#32 := by
        simp only [flow,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,Bool.false_eq_true,ite_true,ite_false]
      refine ⟨4,d,by decide,by decide,trace,?_,?_,csr⟩
      · simpa only [byte_classes] using pc.trans flowPC.symm
      · intro r h12
        exact frame r h12
  | true =>
    obtain ⟨d,trace,pc,out12,frame,csr⟩ := HeadOwsBackCase02.contract B c ram v h13 hb0 hp
    have flowPC : flow b=0x800030ca#32 := by
      simp only [flow,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨2,d,by decide,by decide,trace,?_,?_,csr⟩
    · simpa only [byte_classes] using pc.trans flowPC.symm
    · intro r h12
      exact frame r h12
end E5R.Thermostat.HeadOwsBackClass
