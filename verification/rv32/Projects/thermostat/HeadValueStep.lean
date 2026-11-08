import Projects.thermostat.HeadValueLoad
import Projects.thermostat.HeadValueClass
import Projects.thermostat.HeadValueState
import Projects.thermostat.HeadMethodMath
namespace E5R.Thermostat.HeadValueStep
open E5R E5R.Thermostat HttpRequestSpec

/-- Actual field-byte load, derived nonzero slice remainder and byte class. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (pos finish length : Nat)
    (hp : c.pc=0x8000307c#32) (state : HeadValueState.At c buf pos finish length)
    (hi : pos<finish) (hn : finish≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) :
    let b := ram (buf+BitVec.ofNat 32 pos)
    ∃ n d, 4≤n ∧ n≤9 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if isFieldByte b.toNat then 0x80003074#32 else 0x8000342c#32) ∧
      HeadValueState.At d buf pos finish length ∧ (∀ r : Reg, r≠30 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let b := ram (buf+BitVec.ofNat 32 pos)
  obtain ⟨a,load,pc,value,tab,frame,csr⟩ := HeadValueLoad.contract B c ram (buf+BitVec.ofNat 32 pos) (BitVec.ofNat 32 (length-pos)) b
    state.ptr state.rawRemaining (HeadMethodMath.nonzero (length-pos) (by omega) (by omega))
    (Memory.block_access mem (off := pos) (by decide) (by change pos+1≤length;omega)) rfl hp
  obtain ⟨n,d,nlo,nhi,classify,pc2,frame2,csr2⟩ := HeadValueClass.contract B a ram b pc value tab
  have finalFrame (r : Reg) (h30 : r≠30) (h12 : r≠12) : d.get r=c.get r := (frame2 r h12).trans (frame r h30 h12)
  exact ⟨3+n,d,by omega,by omega,load.trans classify,pc2,
    ⟨(finalFrame 10 (by decide) (by decide)).trans state.ptr,(finalFrame 13 (by decide) (by decide)).trans state.remaining,
      (finalFrame 31 (by decide) (by decide)).trans state.rawRemaining⟩,finalFrame,csr2.trans csr⟩
end E5R.Thermostat.HeadValueStep
