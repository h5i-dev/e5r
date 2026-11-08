import Projects.thermostat.MainServeNextCallTwo
import Projects.thermostat.MainRamCall264
namespace E5R.Thermostat.MainServeNextCopyTwo
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) := MainRamCopy264.memory ram sp 992 1062

/-- Actual common Next array staging call and full memcpy return. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc=0x80000afe#32) (h2 : c.get 2=sp) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 362 ⟨c,ram⟩ ⟨d,memory ram sp⟩ ∧ d.pc=0x80000b1a#32 ∧ d.get 2=sp ∧
      HeadSaved.CoreAt d (MainRamCall264.values c 0x80000b1a#32) ∧ d.sameCsr c := by
  obtain ⟨a,call,apc,a10,a11,a12,a1,ar,ac⟩ := MainServeNextCallTwo.contract B c ram sp h2 hp
  exact MainRamCall264.contract B c a ram sp 0x80000b1a#32 992 1062 (by decide) (by decide) (by decide)
    call apc h2 a10 a11 a12 a1 (fun r h1 h10 h11 h12 => ar r h10 h11 h12 h1) ac (by decide +kernel) stack aligned
end E5R.Thermostat.MainServeNextCopyTwo
