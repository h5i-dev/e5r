-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ApplyAdapter
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ApplyQuiet
import Projects.thermostat.ApplyReturnQuiet
import Projects.thermostat.ApplyWrapperQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.ApplyAdapter
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (s : Spec.Snapshot) (w : Option Spec.Snapshot)
    (hp : c.pc = 0x80001e38) (hr : B.inRam (ApplyWrapper.saved c) 4 = true)
    (ha : (ApplyWrapper.saved c).toNat%4 = 0)
    (htag : B.inRam (c.get 12) 1 = true)
    (hstate : Apply.HalfBlock B (c.get 11)) (hwrite : Apply.HalfBlock B (c.get 12))
    (hout : Apply.HalfBlock B (c.get 10))
    (hs : Encoding.SnapshotAt (ApplyWrapper.save c ram) (c.get 11) s)
    (hw : Encoding.OptionAt (ApplyWrapper.save c ram) (c.get 12) w)
    (hsep : ∀ k : Fin 4, ∀ i : Fin 10,
      ApplyWrapper.saved c+BitVec.ofNat 32 k.val ≠ c.get 10+BitVec.ofNat 32 i.val) :
    ∃ n d r, n ≤ 22 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 2 = c.get 2 ∧ d.sameCsr c ∧
      Encoding.SnapshotAt r (c.get 10) (Spec.apply s w) ∧
      (∀ x, (∀ i : Fin 10, x ≠ c.get 10+BitVec.ofNat 32 i.val) →
        (∀ k : Fin 4, x ≠ ApplyWrapper.saved c+BitVec.ofNat 32 k.val) → r x = ram x) ∧
      (∀ rr : Reg, rr ≠ 1 → rr ≠ 2 → rr ≠ 11 → rr ≠ 12 → rr ≠ 13 → rr ≠ 14 → rr ≠ 15 → d.get rr = c.get rr) := by
  have hi (r : Reg) (h1 : r ≠ 1) (h2 : r ≠ 2) : (ApplyWrapper.inner c).get r = c.get r :=
    ApplyWrapper.inner_reg c r h1 h2
  obtain ⟨n,ca,r,hn,hrun,hpc,_,hresult,hframe,hregs,hcsr⟩ :=
    E5R.Thermostat.Apply.source_contract_quiet B (ApplyWrapper.inner c) (ApplyWrapper.save c ram) s w rfl
      (by simpa only [hi 12 (by decide) (by decide)] using htag)
      (by simpa only [hi 11 (by decide) (by decide)] using hstate)
      (by simpa only [hi 12 (by decide) (by decide)] using hwrite)
      (by simpa only [hi 10 (by decide) (by decide)] using hout)
      (by simpa only [hi 11 (by decide) (by decide)] using hs)
      (by simpa only [hi 12 (by decide) (by decide)] using hw)
  have hpc' : ca.pc = 0x80001e44 := by
    rw [hpc,ApplyWrapper.inner_ra]
    decide +kernel
  have hsp : ca.get 2 = ApplyWrapper.low c :=
    (hregs 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ApplyWrapper.inner_sp c)
  have hslot : ca.get 2+12#32 = ApplyWrapper.saved c := by rw [hsp];rfl
  have hv : ramRead r (ApplyWrapper.saved c) .w = c.get 1 := by
    calc
      _ = ramRead (ApplyWrapper.save c ram) (ApplyWrapper.saved c) .w := by
        apply ramRead_w_congr
        intro k hk
        apply hframe
        simpa only [hi 10 (by decide) (by decide)] using hsep ⟨k,hk⟩
      _ = c.get 1 := ramRead_ramWrite_w _ _ _
  obtain ⟨d,hsuffix,hpcd,hspd,hregsd,hcsrd⟩ := E5R.Thermostat.ApplyReturn.contract_quiet B ca r (c.get 1) hpc'
    (by rw [hslot];exact hr) (by rw [hslot];exact ha) (by rw [hslot];exact hv)
  refine ⟨4+n+3,d,r,by omega,((E5R.Thermostat.ApplyWrapper.enter_quiet B c ram hp hr ha).trans hrun).trans hsuffix,
    hpcd,?_,hcsrd.trans (hcsr.trans (by rfl)),?_,?_,?_⟩
  · rw [hspd,hsp]
    simp [ApplyWrapper.low,BitVec.add_assoc]
  · simpa only [hi 10 (by decide) (by decide)] using hresult
  · intro x hxo hxs
    rw [hframe x (by simpa only [hi 10 (by decide) (by decide)] using hxo)]
    apply ramWrite_w_other
    intro k hk
    exact hxs ⟨k,hk⟩
  · intro rr h1 h2 h11 h12 h13 h14 h15
    exact (hregsd rr h1 h2).trans ((hregs rr h11 h12 h13 h14 h15).trans (hi rr h1 h2))

end E5R.Thermostat.ApplyAdapter
