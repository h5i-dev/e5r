import Projects.thermostat.MainCloseBegin
import Projects.thermostat.MainCloseForceSetup
import Projects.thermostat.MainCloseCountSetup
import Projects.thermostat.MainCloseCountBranch
import Projects.thermostat.MainCloseHeaderCall
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseDispatch
open E5R E5R.Thermostat

def forced (minor served : Nat) : Prop := minor=0 ∨ 100≤served
instance (minor served : Nat) : Decidable (forced minor served) := inferInstanceAs (Decidable (minor=0 ∨ 100≤served))

/-- Actual main close dispatch. Forced closure is fully decided from initialized
    configuration, minor and served count; otherwise this reaches the real
    wants_close entry with the actual Request pointer and return address. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (minor served : Nat)
    (minorBound : minor≤1) (servedBound : served≤100)
    (hp : c.pc=0x80001246#32) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32)
    (h9 : c.get 9=BitVec.ofNat 32 minor) (h18 : c.get 18=BitVec.ofNat 32 served)
    (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
    (hconfig : ramRead ram (sp+3248#32) .w=sp+3204#32) (hrequests : ramRead ram (sp+3212#32) .w=100#32) :
    ∃ n d, n≤15 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if forced minor served then 0x8000128c#32 else 0x800023f2#32) ∧
      d.get 10=(if forced minor served then 1#32 else sp+3312#32) ∧
      d.get 20=5#32 ∧ d.get 21=6#32 ∧ d.get 24=sp+3740#32 ∧ d.get 25=sp+3784#32 ∧
      (¬forced minor served → d.get 1=0x80001276#32) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠20 → r≠21 → r≠24 → r≠25 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,begin,pa,a10,ar,ac⟩ := MainCloseBegin.contract B c ram minor minorBound hp h9
  have a2 : a.get 2=sp := (ar 2 (by decide)).trans h2
  by_cases zero : minor=0
  · have atZero : a.pc=0x80001278#32 := by simpa only [zero,ite_true] using pa
    obtain ⟨d,setup,pd,d20,d21,d24,d25,dr,dc⟩ := MainCloseForceSetup.contract B a ram sp a2 atZero
    have yes : forced minor served := Or.inl zero
    refine ⟨8,d,by decide,begin.trans setup,?_,?_,d20,d21,d24,d25,?_,?_,dc.trans ac⟩
    · simpa only [yes,ite_true] using pd
    · simpa only [yes,ite_true] using (dr 10 (by decide) (by decide) (by decide) (by decide)).trans a10
    · intro no;exact False.elim (no yes)
    · intro r n10 _ n20 n21 n24 n25 _
      exact (dr r n20 n21 n24 n25).trans (ar r n10)
  · have atOne : a.pc=0x8000124a#32 := by simpa only [zero,ite_false] using pa
    obtain ⟨b,setup,pb,b11,b20,b21,b24,b25,br,bc⟩ := MainCloseCountSetup.contract B a ram sp a2
      ((ar 8 (by decide)).trans h8) stack aligned hconfig hrequests atOne
    have b18 : b.get 18=BitVec.ofNat 32 served := (br 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ar 18 (by decide)).trans h18)
    obtain ⟨e,branch,pe,er,ec⟩ := MainCloseCountBranch.contract B b ram served servedBound pb b18 b11
    have e20 : e.get 20=5#32 := (er 20).trans b20
    have e21 : e.get 21=6#32 := (er 21).trans b21
    have e24 : e.get 24=sp+3740#32 := (er 24).trans b24
    have e25 : e.get 25=sp+3784#32 := (er 25).trans b25
    have frame (r : Reg) (n10 : r≠10) (n11 : r≠11) (n20 : r≠20) (n21 : r≠21) (n24 : r≠24) (n25 : r≠25) : e.get r=c.get r :=
      (er r).trans ((br r n11 n20 n21 n24 n25).trans (ar r n10))
    by_cases reached : 100≤served
    · have yes : forced minor served := Or.inr reached
      refine ⟨11,e,by decide,(begin.trans setup).trans branch,?_,?_,e20,e21,e24,e25,?_,?_,ec.trans (bc.trans ac)⟩
      · simpa only [reached,yes,ite_true] using pe
      · simpa only [yes,ite_true] using (er 10).trans ((br 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a10)
      · intro no;exact False.elim (no yes)
      · intro r n10 n11 n20 n21 n24 n25 _;exact frame r n10 n11 n20 n21 n24 n25
    · have no : ¬forced minor served := by intro yes;rcases yes with h|h <;>contradiction
      have atScan : e.pc=0x80001266#32 := by simpa only [reached,ite_false] using pe
      have e2 : e.get 2=sp := (frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
      obtain ⟨d,call,pd,d10,d1,dr,dc⟩ := MainCloseHeaderCall.contract B e ram sp e2 atScan
      refine ⟨15,d,by decide,((begin.trans setup).trans branch).trans call,?_,?_,
        (dr 20 (by decide) (by decide)).trans e20,(dr 21 (by decide) (by decide)).trans e21,
        (dr 24 (by decide) (by decide)).trans e24,(dr 25 (by decide) (by decide)).trans e25,fun _ => d1,?_,dc.trans (ec.trans (bc.trans ac))⟩
      · simpa only [no,ite_false] using pd
      · simpa only [no,ite_false] using d10
      · intro r n10 n11 n20 n21 n24 n25 n1
        exact (dr r n10 n1).trans (frame r n10 n11 n20 n21 n24 n25)
end E5R.Thermostat.MainCloseDispatch
