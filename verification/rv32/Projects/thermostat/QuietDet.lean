import Projects.thermostat.QuietLoad
namespace E5R.Thermostat.QuietDet
open E5R E5R.Thermostat

def Good : Instr → Bool
  | .load _ _ rd _ _ => rd.val != 0
  | _ => true

/-- Existing deterministic semantics suffices exactly when a normal load does
    not discard its result. The premise is checked on the decoded instruction. -/
theorem promote {B : Board} {img : List Segment} {c d : Core} {ram after : Word → BitVec 8} {i : Instr} {len : Word}
    (hal : c.pc.getLsbD 0=false) (hf : fetchDecode img c.pc=some (i,len)) (good : Good i=true)
    (h : DetStep B img ⟨c,ram⟩ ⟨d,after⟩) : Quiet.Step B img ⟨c,ram⟩ ⟨d,after⟩ := by
  cases i
  case load w signed rd rs off =>
    exact QuietLoad.promote hal hf (by simpa only [Good,bne_iff_ne,ne_eq] using good) h
  all_goals exact QuietExec.promote_nonload hal hf (by trivial) h

/-- Drop-in proof bridge for checked generation of quiet variants. A discarded
    normal load fails the automatic decoded-instruction side condition. -/
theorem step_of {B : Board} {img : List Segment} {m : Machine} {i : Instr} {len : Word} {c : Core} {ram : Word → BitVec 8}
    (hal : m.core.pc.getLsbD 0=false) (hf : fetchDecode img m.core.pc=some (i,len))
    (he : ∀ o, interp B img o (exec m.core len i) m.ram 0 []=.ok c ram [])
    (good : Good i=true := by first | rfl | simp_all [E5R.Thermostat.QuietDet.Good]) : Quiet.Step B img m ⟨c,ram⟩ := by
  exact promote hal hf good (detStep_of hal hf he)
end E5R.Thermostat.QuietDet

namespace E5R.Thermostat.Quiet
open E5R

theorem Step.det_quiet {B img m d} (h : Step B img m d) : Step B img m d := h
theorem Steps.det_quiet {B img n m d} (h : Steps B img n m d) : Steps B img n m d := h
end E5R.Thermostat.Quiet
