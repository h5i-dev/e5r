import Projects.thermostat.PackedFetch
import Projects.thermostat.Observed
import Theories.Board.QemuVirtRv32
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.UartPlatform
open E5R E5R.Thermostat

def board : Board := QemuVirtRv32.board ThermostatImage.image.rwBase
def lsr : DevReg := ⟨0x10000005,"uart0.lsr",true,false,1⟩
def data : DevReg := ⟨0x10000000,"uart0.rbr_thr_dll",true,true,1⟩

theorem rom_none (a : Nat) (h : a+1 ≤ 0x80000000) : romRead? img a 1 false = none := by
  rw [PackedFetch.ro_eq]
  simp only [romRead?,romRead?.go,romByte?,List.find?]
  have h0 : decide (0x80000000 ≤ a) = false := by simp;omega
  have h1 : decide (0x8000030e ≤ a) = false := by simp;omega
  have h2 : decide (0x800056a8 ≤ a) = false := by simp;omega
  simp only [Nat.add_zero,h0,h1,h2,Bool.false_and]
  rfl

theorem outside (a : Word) (h : a.toNat < 0x80000000) : board.inRam a 1 = false := by
  unfold board QemuVirtRv32.board Board.inRam
  rw [ThermostatImage.image_rwBase]
  have hn : ¬2147507992 ≤ a.toNat := by omega
  simp [hn]

theorem lsr_device : board.device? 0x10000005#32 = some lsr := rfl
theorem data_device : board.device? 0x10000000#32 = some data := rfl

/-- A faithful observed byte load, on the unchanged QEMU board declaration.
    The oracle remains arbitrary; no ready/input/progress property is assumed. -/
theorem load (m : Machine) (o : Oracle) (rd rs : Reg) (off len a : Word) (d : DevReg)
    (hal : m.core.pc.getLsbD 0 = false)
    (hf : fetchDecode img m.core.pc = some (.load .b false rd rs off,len))
    (ha : m.core.get rs+off = a) (hbelow : a.toNat+1 ≤ 0x80000000)
    (hd : board.device? a = some d) (hr : d.read = true) (hw : d.width = 1) :
    Observed.stepInstr board img m o =
      ⟨.ok (m.core.wr rd (extend .b false (devVal .b (o 0))) (m.core.pc+len)) m.ram [],
        [⟨a,.b,devVal .b (o 0),0⟩]⟩ := by
  rw [Observed.stepInstr_of hal hf,exec_load,ha]
  unfold Observed.interp
  have e1 : ¬(a.toNat%Width.b.bytes ≠ 0) := by simp [Width.bytes,Nat.mod_one]
  have e2 : board.inRam a Width.b.bytes = false := outside a (by omega)
  have e3 : romRead? img a.toNat Width.b.bytes false = none := rom_none a.toNat hbelow
  have e4 : (d.read && decide (Width.b.bytes = d.width)) = true := by simp [hr,hw,Width.bytes]
  rw [ite_eq_right_of_eq_false _ _ (eq_false e1),e2,ite_eq_right (by decide),ite_eq_right (by decide),e3]
  simp only [hd,e4,ite_true]
  rfl
end E5R.Thermostat.UartPlatform
