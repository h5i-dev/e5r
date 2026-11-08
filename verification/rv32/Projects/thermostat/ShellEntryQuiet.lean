-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ShellEntry
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ProofQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.ShellEntry
theorem setup_contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000622) : Quiet.Steps B img 7 ⟨c,ram⟩ ⟨setup c,ram⟩ := by
  apply E5R.Thermostat.run_sound_quiet
  simp [run,hp,s2147485218,s2147485222,s2147485224,s2147485228,s2147485232,s2147485234,s2147485238,
    exec_opimm,exec_op,exec_auipc,exec_jalr,alu,jump,Core.wr,Core.get_zero,setup]

end E5R.Thermostat.ShellEntry
