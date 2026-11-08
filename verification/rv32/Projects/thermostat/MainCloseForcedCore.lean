import Projects.thermostat.MainCloseDispatch
import Projects.thermostat.MainCloseCommit
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseForcedCore
open E5R E5R.Thermostat

/-- The actual forced-close path reaches route setup with the persisted close
    flag, including the real TX-capacity guard. No Connection scan is assumed. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (minor served : Nat)
    (minorBound : minor≤1) (servedBound : served≤100) (forced : MainCloseDispatch.forced minor served)
    (hp : c.pc=0x80001246#32) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32)
    (h9 : c.get 9=BitVec.ofNat 32 minor) (h18 : c.get 18=BitVec.ofNat 32 served)
    (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
    (hconfig : ramRead ram (sp+3248#32) .w=sp+3204#32) (hrequests : ramRead ram (sp+3212#32) .w=100#32)
    (hcapacity : ramRead ram (sp+3272#32) .w=1024#32) :
    ∃ n d, n≤19 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,MainCloseCommit.memory ram sp 1#32⟩ ∧ d.pc=0x8000129a#32 ∧
      d.get 12=1024#32 ∧ d.get 10=191#32 ∧ d.get 20=5#32 ∧ d.get 21=6#32 ∧
      d.get 24=sp+3740#32 ∧ d.get 25=sp+3784#32 ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠20 → r≠21 → r≠24 → r≠25 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨first,a,nb,dispatch,pa,a10,a20,a21,a24,a25,_,ar,ac⟩ := MainCloseDispatch.contract B c ram sp minor served minorBound servedBound hp h2 h8 h9 h18 stack aligned hconfig hrequests
  have atCommit : a.pc=0x8000128c#32 := by simpa only [forced,ite_true] using pa
  have flag : a.get 10=1#32 := by simpa only [forced,ite_true] using a10
  have a8 : a.get 8=sp+3204#32 := (ar 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
  obtain ⟨d,commit,pd,d12,d10,dr,dc⟩ := MainCloseCommit.contract B a ram sp 1#32 a8 flag stack aligned hcapacity atCommit
  refine ⟨first+4,d,by omega,dispatch.trans commit,pd,d12,d10,
    (dr 20 (by decide) (by decide)).trans a20,(dr 21 (by decide) (by decide)).trans a21,
    (dr 24 (by decide) (by decide)).trans a24,(dr 25 (by decide) (by decide)).trans a25,?_,dc.trans ac⟩
  intro r n10 n11 n12 n20 n21 n24 n25 n1
  exact (dr r n12 n10).trans (ar r n10 n11 n20 n21 n24 n25 n1)
end E5R.Thermostat.MainCloseForcedCore
