import Projects.thermostat.DecodedEngine
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.DecodedTight
open E5R E5R.Thermostat

theorem contract_inv (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : DecodedEngine.Pre B c ram p admin s)
    (hc : WireSpec.CommandWord (c.get 10) cmd) (hi : Spec.Inv s) :
    ∃ a n d r, n ≤ 183 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Engine.Post a d (WireCallerBytes.memory ram (p+80#32) (c.get 10)) r p s (Spec.transition admin s cmd) ∧
      Engine.InvariantAt r (c.get 23) ∧
      (∀ reg : Reg, reg ≠ 11 → reg ≠ 12 → reg ≠ 20 → a.get reg = c.get reg) ∧ a.sameCsr c ∧ Engine.TopSame p ram r := by
  have hm : Memory.Block B (p+80#32) 16 := Memory.sub_block h.arena (by decide) (by decide)
  have ha : (p+80#32).toNat%2 = 0 := Memory.half_aligned p 40 (by have := h.align;omega)
  obtain ⟨a,ht,hpc,hcommand,hregs,hcsr⟩ := WireCaller.ok B c ram (p+80#32) cmd h.pc h.sp hc hm ha
  have pre := DecodedEngine.establishes_pre B c a ram p admin s cmd h hpc hcommand hregs
  obtain ⟨n,d,r,hn,td,hpost,htop⟩ := Acquire.contract_full B a (WireCallerBytes.memory ram (p+80#32) (c.get 10)) p admin s cmd pre
  have heng : a.get 23 = c.get 23 := hregs 23 (by decide) (by decide) (by decide)
  have hinv : Engine.InvariantAt r (c.get 23) := by
    refine ⟨Spec.commit s (Spec.transition admin s cmd),?_,Spec.commit_inv admin s cmd hi⟩
    simpa only [heng] using hpost.state
  refine ⟨a,8+n,d,r,by omega,ht.trans td,hpost,hinv,hregs,hcsr,?_⟩
  intro k
  rw [htop k]
  apply WireCallerBytes.frame
  intro i
  have hi := i.isLt
  have hk := k.isLt
  have he := ShellCall.offset_ne p (124+k.val) (90+i.val) (by omega) (by omega) (by omega)
  have hp : (p+80#32)+10#32 = p+90#32 := by rw [BitVec.add_assoc];rfl
  simpa only [hp,BitVec.ofNat_add,BitVec.add_assoc] using he

end E5R.Thermostat.DecodedTight
