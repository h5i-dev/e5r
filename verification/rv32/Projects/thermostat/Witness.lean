import Projects.thermostat.Kernel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace E5R.Thermostat.Witness
open E5R E5R.Thermostat

-- A concrete valid caller demonstrates that the universal contract is usable.
def board : Board := ⟨ThermostatImage.image.rwBase,0x81000000-ThermostatImage.image.rwBase,[]⟩
def core : Core :=
  ⟨0x80000052,(fun r => if r = 1 then 0x90000000 else if r = 2 then 0x80020040
    else if r = 10 then 0x80010020 else if r = 11 then 0x80010000
    else if r = 12 then 0x80010002 else if r = 13 then 0x80010010 else 0),
    false,false,3,0,0,0,0,0,false⟩
def ram (a : Word) : BitVec 8 :=
  if a = 0x80010000 then 1
  else if a = 0x80010006 ∨ a = 0x80010008 then 200
  else if a = 0x80010010 then 2
  else if a = 0x80010011 then 3
  else if a = 0x80010012 then 1 else 0

theorem valid_caller : Call.Pre board core ram true Spec.initial (.relay 3 true) := by
  rw [show board = (⟨2147507992,0x81000000-2147507992,[]⟩ : Board) by
    unfold board;rw [ThermostatImage.image_rwBase]]
  constructor <;> (try simp only [Memory.Block,Encoding.SnapshotAt,Encoding.CommandAt,Call.Separate]) <;> decide +kernel

theorem actual_relay_call :
    ∃ n m, n ≤ 81 ∧ DetSteps board img n ⟨core,ram⟩ m ∧
      Call.Post core ram m (Spec.transition true Spec.initial (.relay 3 true)) :=
  Kernel.transition_contract board core ram true Spec.initial (.relay 3 true) valid_caller
end E5R.Thermostat.Witness
