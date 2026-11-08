import Projects.thermostat.MainChunkCode
import Projects.thermostat.UartPoll
namespace E5R.Thermostat.MainChunkRbr
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

theorem load (c : Core) (ram : Word → BitVec 8) (o : Oracle)
    (hp : c.pc=0x80000e80#32) (hu : c.get 19=0x10000000#32) :
    Observed.stepInstr B img ⟨c,ram⟩ o =
      ⟨.ok (c.wr 11 (UartPoll.byte (o 0)) 0x80000e84#32) ram [],
        [⟨0x10000000#32,.b,UartPoll.byte (o 0),0⟩]⟩ := by
  have hk := UartPlatform.load ⟨c,ram⟩ o 11 19 0#32 4#32 0x10000000#32 UartPlatform.data
    (by rw [hp];decide) (by rw [hp];exact cc2147487360)
    (by rw [hu];decide +kernel) (by decide +kernel) UartPlatform.data_device rfl rfl
  have hv : devVal .b (o 0)=UartPoll.byte (o 0) := rfl
  simpa only [hv,hp,UartPoll.extend_byte,show 0x80000e80#32+4#32=0x80000e84#32 by decide +kernel] using hk

theorem step (c : Core) (ram : Word → BitVec 8) (datum : Word)
    (hp : c.pc=0x80000e80#32) (hu : c.get 19=0x10000000#32) :
    Observed.Step B img ⟨c,ram⟩ ⟨c.wr 11 (UartPoll.byte datum) 0x80000e84#32,ram⟩
      [⟨0x10000000#32,.b,UartPoll.byte datum,0⟩] [] := by
  have hk := load c ram (fun _ => datum) hp hu
  have hs : Observed.Step B img ⟨c,ram⟩ ⟨c.wr 11 (UartPoll.byte datum) 0x80000e84#32,ram⟩
      (Observed.stepInstr B img ⟨c,ram⟩ (fun _ => datum)).reads [] :=
    .instr (fun _ => datum) (by rw [hk])
  simpa only [hk] using hs
end E5R.Thermostat.MainChunkRbr
