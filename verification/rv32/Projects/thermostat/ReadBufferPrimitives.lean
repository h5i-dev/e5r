import Projects.thermostat.ReadBuffer
import Projects.thermostat.ReadDispatch
import Projects.thermostat.ReadMarshal
import Projects.thermostat.ReadState
import Projects.thermostat.ReadRestore
namespace E5R.Thermostat.ReadBuffer
open E5R E5R.Thermostat

theorem ne_low (r q : Reg) (hr : Live r) (hq : q.val<20) : r≠q := by
  intro he;subst r;rcases hr with h|h|h <;> subst q <;> omega

theorem dispatch (c : Core) (ram : Word → BitVec 8) : Frame c (ReadDispatch.next c ram) := by
  intro r hr;rcases hr with h|h|h <;> subst r <;> simp [ReadDispatch.next,Core.wr_get_ne]

theorem marshal (c : Core) (ram : Word → BitVec 8) : Frame c (ReadMarshal.execute c ram).core := by
  intro r hr;rcases hr with h|h|h <;> subst r <;> simp [ReadMarshal.execute,Core.wr_get_ne]

theorem state (c : Core) (ram : Word → BitVec 8) : Frame c (ReadState.execute c ram).core := by
  intro r hr;rcases hr with h|h|h <;> subst r <;> simp [ReadState.execute,Core.wr_get_ne]

theorem restore (c : Core) (ram : Word → BitVec 8) : Frame c (ReadRestore.execute c ram).core := by
  intro r hr;rcases hr with h|h|h <;> subst r <;> simp [ReadRestore.execute,Core.wr_get_ne]
end E5R.Thermostat.ReadBuffer
