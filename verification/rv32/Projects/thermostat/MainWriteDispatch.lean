import Projects.thermostat.MainWriteReady
import Projects.thermostat.MainWriteResult
import Projects.thermostat.BodyResponseView
namespace E5R.Thermostat.MainWriteDispatch
open E5R E5R.Thermostat

/-- Actual successful poll-return dispatch and response extraction. The unused
    cache byte at result+15 remains unconstrained. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp sp ct len used status : Word)
    (hp : c.pc=0x8000196c#32) (h8 : c.get 8=fp) (h2 : c.get 2=sp) (h18 : c.get 18=1#32)
    (hm : Memory.Block B fp 1332) (ha : fp.toNat%4=0)
    (hv : BodyMemory.At ram (fp+1316#32) ct len used status) (hst : status.toNat<65536) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001710#32 ∧
      d.get 12=ct ∧ d.get 11=len ∧ d.get 20=used ∧ d.get 10=status ∧ d.get 13=0#32 ∧
      d.get 9=sp+3304#32 ∧ d.get 24=0xfffffffe#32 ∧
      (∀ r : Reg, r≠12 → r≠11 → r≠20 → r≠10 → r≠6 → r≠9 → r≠24 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  have flag : ram (fp+1330#32)=0#8 := by
    simpa only [BitVec.add_assoc,show (1316#32+14#32)=1330#32 by decide +kernel] using BodyResponseView.extra hv
  obtain ⟨a,ta,pa,a13,_,fa,ka⟩ := MainWriteReady.contract B c ram fp h8 h18 hm ha flag hp
  have aw (r : Reg) (h13 : r≠13) (h9 : r≠9) : a.get r=c.get r := fa r h13 h9
  have ctWord : ramRead ram (fp+1316#32) .w=ct := by
    simpa only [Nat.mul_zero,BitVec.add_zero,ite_true] using BodyResponseView.word hv ⟨0,by decide⟩
  have lenWord : ramRead ram (fp+1320#32) .w=len := by
    simpa only [show (4*1 : Nat)=4 by decide,BitVec.add_assoc,show (1316#32+4#32)=1320#32 by decide +kernel,
      show (1 : Nat)≠0 by decide,ite_false,ite_true] using BodyResponseView.word hv ⟨1,by decide⟩
  have usedWord : ramRead ram (fp+1324#32) .w=used := by
    simpa only [show (4*2 : Nat)=8 by decide,BitVec.add_assoc,show (1316#32+8#32)=1324#32 by decide +kernel,
      show (2 : Nat)≠0 by decide,show (2 : Nat)≠1 by decide,ite_false] using BodyResponseView.word hv ⟨2,by decide⟩
  have statusHalf : extend .h false (ramRead ram (fp+1328#32) .h)=status := by
    simpa only [BitVec.add_assoc,show (1316#32+12#32)=1328#32 by decide +kernel] using BodyResponseView.half hv hst
  obtain ⟨d,td,pd,d12,d11,d20,d10,_,d9,d24,fd,kd⟩ := MainWriteResult.contract B a ram fp sp ct len used status
    ((aw 8 (by decide) (by decide)).trans h8) ((aw 2 (by decide) (by decide)).trans h2) hm ha ctWord lenWord usedWord statusHalf pa
  refine ⟨d,ta.trans td,pd,d12,d11,d20,d10,?_,d9,d24,?_,kd.trans ka⟩
  · exact (fd 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a13
  · intro r h12 h11 h20 h10 h6 h9 h24 h13
    exact (fd r h12 h11 h20 h10 h6 h9 h24).trans (aw r h13 h9)
end E5R.Thermostat.MainWriteDispatch
