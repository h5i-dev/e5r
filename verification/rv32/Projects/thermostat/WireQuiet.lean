-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Wire
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.CommandBodyQuiet
import Projects.thermostat.DecodeReturnQuiet
import Projects.thermostat.WirePrefixQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.Wire
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp req pathPtr bodyPtr : Word)
    (path body : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (h : Pre B c ram sp req pathPtr bodyPtr path body first) :
    ∃ d n, n ≤ 18*body.length+303 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,DecodeSave.memory ram sp c⟩ ∧ Post c d path body first := by
  obtain ⟨a,n,hn,ht,apc,asp,areq,abody,a9,aframe,acsr⟩ := E5R.Thermostat.WirePrefix.contract_quiet B c ram sp req bodyPtr body
    h.pc h.stack h.request h.stackRam h.aligned h.bodyView h.requestSeparate h.bodySeparate
  let r := DecodeSave.memory ram sp c
  have pathView := WireInput.path_saved h.pathView sp c h.requestSeparate h.pathSeparate
  have params := WireInput.params_saved h.params sp c h.requestSeparate h.pathSeparate
  obtain ⟨b,k,hk,tb,bpc,bval,bframe,bcsr⟩ := E5R.Thermostat.CommandBody.contract_quiet B a r req pathPtr (a.get 8)
    path (TrimMath.trim body) first pathView params.as_pre abody apc areq rfl a9
  have bsp : b.get 2 = sp := (bframe 2 (by decide) (by decide) (by decide)).trans asp
  obtain ⟨d,td,dpc,dsp,dra,ds0,ds1,dframe,dcsr⟩ := E5R.Thermostat.DecodeReturn.contract_quiet B b r sp bpc bsp h.stackRam h.aligned
  obtain ⟨savedRA,saved0,saved1⟩ := DecodeSave.saved ram sp c
  refine ⟨d,n+k+5,by omega,(ht.trans tb).trans td,?_,?_,?_,?_,?_,?_,?_,(dcsr.trans bcsr).trans acsr⟩
  · exact dpc.trans (congrArg (fun w : Word => w &&& ~~~1) savedRA)
  · have hv : d.get 10 = b.get 10 := dframe 10 (by decide) (by decide) (by decide) (by decide)
    rw [hv,←CommandSpec.as_decode];exact bval
  · exact dsp.trans h.stack.symm
  · exact dra.trans savedRA
  · exact ds0.trans saved0
  · exact ds1.trans saved1
  · intro r hr
    have hr8 : r.val < 8 ∨ 17 < r.val := by omega
    have hr10 : r.val < 10 ∨ 17 < r.val := by omega
    have ne (k : Reg) (hk : k.val = 1 ∨ k.val = 2 ∨ k.val = 5 ∨ k.val = 8 ∨ k.val = 9) : r ≠ k := by
      intro he;have hv := congrArg Fin.val he;omega
    exact (dframe r (ne 1 (by decide)) (ne 2 (by decide)) (ne 8 (by decide)) (ne 9 (by decide))).trans
      ((bframe r (ne 1 (by decide)) (ne 5 (by decide)) hr10).trans (aframe r (ne 2 (by decide)) hr8))

end E5R.Thermostat.Wire
