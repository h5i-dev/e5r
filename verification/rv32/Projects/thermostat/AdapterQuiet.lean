-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Adapter
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.KernelQuiet
import Projects.thermostat.ReturnQuiet
import Projects.thermostat.WrapperQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.Adapter
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (hp : c.pc = 0x80001e26) (hr : B.inRam (Wrapper.saved c) 4 = true)
    (ha : (Wrapper.saved c).toNat % 4 = 0)
    (h : Call.Pre B (Wrapper.inner c) (Wrapper.save c ram) admin s cmd)
    (hout : ∀ k : Fin 4, ∀ i : Fin 20,
      Wrapper.saved c+BitVec.ofNat 32 k.val ≠ (Wrapper.inner c).get 10+BitVec.ofNat 32 i.val)
    (hstack : ∀ k : Fin 4, ∀ i : Fin 64,
      Wrapper.saved c+BitVec.ofNat 32 k.val ≠ Stack.base (Wrapper.inner c)+BitVec.ofNat 32 i.val) :
    ∃ n m d, n ≤ 88 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,m.ram⟩ ∧
      Call.Post (Wrapper.inner c) (Wrapper.save c ram) m (Spec.transition admin s cmd) ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 2 = c.get 2 ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 2 → d.get r = m.core.get r) ∧ d.sameCsr c := by
  have hentry := E5R.Thermostat.Wrapper.enter_quiet B c ram hp hr ha
  obtain ⟨n,m,hn,hrun,hpost⟩ := E5R.Thermostat.Kernel.transition_contract_quiet B (Wrapper.inner c) (Wrapper.save c ram)
    admin s cmd h
  have hpc : m.core.pc = 0x80001e32 := by
    rw [hpost.pc,Wrapper.inner_ra]
    decide +kernel
  have hsaved : m.core.get 2+12#32 = Wrapper.saved c := by
    rw [hpost.sp,Wrapper.inner_sp]
    rfl
  have hv : ramRead m.ram (Wrapper.saved c) .w = c.get 1 := by
    calc
      _ = ramRead (Wrapper.save c ram) (Wrapper.saved c) .w := by
        apply ramRead_w_congr
        intro k hk
        exact hpost.frame _ (hout ⟨k,hk⟩) (hstack ⟨k,hk⟩)
      _ = c.get 1 := ramRead_ramWrite_w _ _ _
  obtain ⟨d,hs,hpcd,hspd,hregs,hcsr⟩ := E5R.Thermostat.Return.contract_quiet B m.core m.ram (c.get 1) hpc
    (by rw [hsaved];exact hr) (by rw [hsaved];exact ha) (by rw [hsaved];exact hv)
  refine ⟨4+n+3,m,d,by omega,(hentry.trans hrun).trans hs,hpost,hpcd,?_,hregs,?_⟩
  · rw [hspd,hpost.sp,Wrapper.inner_sp]
    simp [Wrapper.low,BitVec.add_assoc]
  · exact hcsr.trans (hpost.csr.trans (by rfl))

end E5R.Thermostat.Adapter
