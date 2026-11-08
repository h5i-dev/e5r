import Projects.thermostat.FirstPoll
import Projects.thermostat.UartPoll
import Projects.thermostat.Infinite
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.Blocking
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

theorem stack_available : Memory.Block B 0x80ff0000#32 65536 := by
  change Memory.Block UartPlatform.board 0x80ff0000#32 65536
  unfold UartPlatform.board QemuVirtRv32.board Memory.Block
  rw [ThermostatImage.image_rwBase]
  decide +kernel

theorem wr_current (c : Core) (r : Reg) : c.wr r (c.get r) c.pc = c := by
  unfold Core.wr Core.set
  by_cases hz : r.val = 0
  · simp [hz]
  · simp only [hz,ite_false]
    have hv : c.get r = c.x r := by simp [Core.get,hz]
    rw [hv]
    have he : (fun i => if i = r then c.x r else c.x i) = c.x := by
      funext i
      by_cases hi : i = r <;> simp [hi]
    rw [he]

theorem normalize (c : Core) (hp : c.pc = 0x80000ba2#32) (hz : c.get 10 = 0#32) : UartPoll.rx0 c = c := by
  unfold UartPoll.rx0
  rw [←hp,←hz]
  exact wr_current c 10

/-- From the actual ELF reset entry on its generated QEMU board, there is an
    infinite original-platform execution emitting no output. A forever-zero
    LSR is permitted by the existing environment model. This rules out an
    unconditional eventual-response claim; it does not rule out progress under
    complete-input/readiness/scheduling assumptions. -/
theorem no_response_from_reset (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000000#32) (hmpp : c.mpp = 0 ∨ c.mpp = 3) :
    ∃ g : Nat → Machine, g 0 = ⟨c,ram⟩ ∧ Infinite.NoWrites B img g := by
  obtain ⟨d,r,hr,hready⟩ := FirstPoll.reset_contract B c ram hp hmpp stack_available
  have h0 : UartPoll.rxForever d r 0 = (⟨d,r⟩ : Machine) := by
    change (⟨UartPoll.rx0 d,r⟩ : Machine) = _
    rw [normalize d hready.pc hready.zero]
  exact Infinite.prepend hr (UartPoll.rxForever d r) h0 (UartPoll.rx_forever_erased d r hready.uart)

theorem arbitrarily_long_no_output (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000000#32) (hmpp : c.mpp = 0 ∨ c.mpp = 3) :
    ∃ g : Nat → Machine, g 0 = ⟨c,ram⟩ ∧
      (∀ n, E5R.Reach B img (fun m => m = (⟨c,ram⟩ : Machine)) (g n) []) := by
  obtain ⟨g,h0,hg⟩ := no_response_from_reset c ram hp hmpp
  exact ⟨g,h0,Infinite.reachable h0 hg⟩
end E5R.Thermostat.Blocking
