-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Startup
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ResetBootQuiet
import Projects.thermostat.ResetInitQuiet
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.Startup
theorem contract_full_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000000) (hm : c.mpp = 0 ∨ c.mpp = 3)
    (hmem : Memory.Block B 0x80ffeb90 5232) :
    ∃ d r, Quiet.Steps B img 44 ⟨c,ram⟩ ⟨d,r⟩ ∧ Ready B d r ∧
      Engine.InvariantAt r 0x80ffebbc ∧ d.mie_ = false ∧ d.mieReg = 0 ∧
      (∀ x, (∀ i : Fin 5232, x ≠ 0x80ffeb90+BitVec.ofNat 32 i.val) → r x = ram x) ∧ d.get 8 = 0x80fff814#32 ∧ d.get 19 = 0x10000000#32 ∧ d.get 22 = 1#32 ∧ d.get 12 = 2048#32 := by
  have hboot := E5R.Thermostat.Boot.contract_quiet B c ram hp hm
  obtain ⟨d,r,hr,hpc,hsp,hcsr,hstate,hfree,hkey,hlen,hactor,hframe,hfp,huart,hone,hlen2⟩ := E5R.Thermostat.Init.contract_full_quiet B
    (Boot.mainEntry c) ram (Boot.main_layout c).1 (Boot.main_layout c).2.1 hmem
  have hmie : d.mie_ = (Boot.mainEntry c).mie_ := congrArg Prod.fst hcsr
  have hreg : d.mieReg = (Boot.mainEntry c).mieReg := congrArg (fun t => t.2.2.2.1) hcsr
  refine ⟨d,r,hboot.trans hr,⟨hpc,hsp,hmem,hstate,hfree,hkey,hlen,hactor⟩,
    ⟨Spec.initial,hstate,Spec.initial_inv⟩,hmie.trans (Boot.main_layout c).2.2.1,
    hreg.trans (Boot.main_layout c).2.2.2,hframe,hfp,huart,hone,hlen2⟩

end E5R.Thermostat.Startup
