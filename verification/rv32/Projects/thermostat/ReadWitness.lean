import Projects.thermostat.ReadCallSite
import Projects.thermostat.ReadAcquire
import Projects.thermostat.ReadEngine
import Projects.thermostat.Witness
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ReadWitness
open E5R E5R.Thermostat

def core : Core := { Witness.core with
  pc := 0x80001a12
  x := fun r => if r = 2 then 0x80ffeb90 else if r = 8 then 0x80fff814 else if r = 9 then 0x80ffebbc else 0}

def ram (a : Word) : BitVec 8 :=
  if a = 0x80ffebbc ∨ a = 0x80ffebbd ∨ a = 0x80ffebbe ∨ a = 0x80ffebbf then 255
  else if a = 0x80ffebc4 ∨ a = 0x80ffebc6 then 200
  else if a = 0x80fffb10 then 4 else 0

theorem valid_caller : ReadCallSite.Pre Witness.board core ram Spec.initial := by
  have hb : Witness.board = (⟨2147507992,0x81000000-2147507992,[]⟩ : Board) := by
    unfold Witness.board;rw [ThermostatImage.image_rwBase]
  rw [hb]
  constructor <;> (try simp only [Memory.Block,Encoding.SnapshotAt,Encoding.CommandAt]) <;> decide +kernel

theorem actual_read :
    ∃ n d r, n ≤ 100 ∧ DetSteps Witness.board img n ⟨core,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80001a38 ∧ Outcome.At r 0x80fffd38 (.ok ⟨none,Spec.initial⟩) ∧
      Encoding.SnapshotAt r 0x80ffebc0 Spec.initial := by
  obtain ⟨n,d,r,hn,hr,hpc,_,_,_,_,hout,hstate,_,_⟩ :=
    ReadCallSite.contract Witness.board core ram Spec.initial valid_caller
  exact ⟨n,d,r,hn,hr,hpc,hout,hstate⟩

def freeCore : Core := core.goto 0x80001a08

def freeRam (a : Word) : BitVec 8 :=
  if a = 0x80ffebbc ∨ a = 0x80ffebbd ∨ a = 0x80ffebbe ∨ a = 0x80ffebbf then 0 else ram a

theorem valid_free_caller : ReadAcquire.Pre Witness.board freeCore freeRam Spec.initial := by
  have hb : Witness.board = (⟨2147507992,0x81000000-2147507992,[]⟩ : Board) := by
    unfold Witness.board;rw [ThermostatImage.image_rwBase]
  rw [hb]
  constructor <;> (try simp only [Memory.Block,Encoding.SnapshotAt,Encoding.CommandAt]) <;> decide +kernel

theorem actual_acquired_read :
    ∃ n d r, n ≤ 104 ∧ DetSteps Witness.board img n ⟨freeCore,freeRam⟩ ⟨d,r⟩ ∧
      d.pc = 0x80001a38 ∧ Outcome.At r 0x80fffd38 (.ok ⟨none,Spec.initial⟩) ∧
      Encoding.SnapshotAt r 0x80ffebc0 Spec.initial ∧ ramRead r 0x80ffebbc .w = 0xffffffff#32 := by
  obtain ⟨n,d,r,hn,hr,hpc,_,_,_,_,hout,hstate,hborrow,_⟩ :=
    ReadAcquire.contract Witness.board freeCore freeRam Spec.initial valid_free_caller
  exact ⟨n,d,r,hn,hr,hpc,hout,hstate,hborrow⟩


theorem actual_completed_read :
    ∃ n d r, n ≤ 194 ∧ DetSteps Witness.board img n ⟨freeCore,freeRam⟩ ⟨d,r⟩ ∧
      d.pc = 0x80001b5e#32 ∧ Encoding.SnapshotAt r 0x80ffebc0#32 Spec.initial ∧
      ramRead r 0x80ffebbc#32 .w = 0#32 ∧ Encoding.SnapshotAt r 0x80fffd38#32 Spec.initial ∧
      Engine.InvariantAt r 0x80ffebbc#32 := by
  obtain ⟨n,d,r,hn,hr,hp,hi⟩ := ReadEngine.contract_inv Witness.board freeCore freeRam Spec.initial
    valid_free_caller Spec.initial_inv
  exact ⟨n,d,r,hn,hr,hp.pc,hp.state,hp.released,hp.reply,hi⟩

end E5R.Thermostat.ReadWitness
