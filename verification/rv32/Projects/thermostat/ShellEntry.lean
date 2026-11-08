import Projects.thermostat.Upper
import Projects.thermostat.ShellCode
import Projects.thermostat.Kernel
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ShellEntry
open E5R E5R.Thermostat

def setup (c : Core) : Core :=
  let c1 := c.wr 20 (c.get 23+4#32) 0x80000626
  let c2 := c1.wr 10 (c.get 2+24#32) 0x80000628
  let c3 := c2.wr 11 (c.get 2+9#32) 0x8000062c
  let c4 := c3.wr 13 (c.get 2+10#32) 0x80000630
  let c5 := c4.wr 12 (c.get 23+4#32) 0x80000632
  let c6 := c5.wr 1 0x80001632 0x80000636
  c6.wr 1 0x8000063a 0x80001e26

theorem setup_contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000622) : DetSteps B img 7 ⟨c,ram⟩ ⟨setup c,ram⟩ := by
  apply run_sound
  simp [run,hp,s2147485218,s2147485222,s2147485224,s2147485228,s2147485232,s2147485234,s2147485238,
    exec_opimm,exec_op,exec_auipc,exec_jalr,alu,jump,Core.wr,Core.get_zero,setup]

theorem setup_upper (c : Core) : Upper.Frame c (setup c) := by
  intro r hr
  have hn1 := Upper.ne_low r hr 1 (by decide)
  have hn10 := Upper.ne_low r hr 10 (by decide)
  have hn11 := Upper.ne_low r hr 11 (by decide)
  have hn12 := Upper.ne_low r hr 12 (by decide)
  have hn13 := Upper.ne_low r hr 13 (by decide)
  have hn20 := Upper.ne_low r hr 20 (by decide)
  simp [setup,Core.wr_get_ne,hn1,hn10,hn11,hn12,hn13,hn20]
end E5R.Thermostat.ShellEntry
