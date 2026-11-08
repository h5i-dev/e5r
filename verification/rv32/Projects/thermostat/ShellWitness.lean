import Projects.thermostat.ShellExecute
import Projects.thermostat.Witness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace E5R.Thermostat.ShellWitness
open E5R E5R.Thermostat

def core : Core := { Witness.core with
    pc := 0x80000622
    x := (fun r => if r = 2 then 0x80020050 else if r = 23 then 0x80010000 else 0) }
def ram (a : Word) : BitVec 8 :=
  if a = 0x80010008 ∨ a = 0x8001000a then 200
  else if a = 0x80020059 then 1
  else if a = 0x8002005a then 2
  else if a = 0x8002005b then 3
  else if a = 0x8002005c then 1 else 0

theorem valid_caller : ShellCall.Pre Witness.board core ram 0x80020000 true Spec.initial (.relay 3 true) := by
  rw [show Witness.board = (⟨2147507992,0x81000000-2147507992,[]⟩ : Board) by
    unfold Witness.board;rw [ThermostatImage.image_rwBase]]
  constructor <;> (try simp only [Memory.Block,Encoding.SnapshotAt,Encoding.CommandAt]) <;> decide +kernel

theorem real_write_call :
    ∃ n d r, n ≤ 99 ∧ DetSteps Witness.board img n ⟨core,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80000678 ∧ Encoding.SnapshotAt r (core.get 23+4#32) Spec.initial := by
  obtain ⟨n,d,r,hn,hr,hpc,_,_,_,_,hs,_,_,_,_⟩ := ShellExecute.contract Witness.board core ram 0x80020000 true Spec.initial (.relay 3 true) valid_caller
  exact ⟨n,d,r,hn,hr,hpc,hs⟩
end E5R.Thermostat.ShellWitness
