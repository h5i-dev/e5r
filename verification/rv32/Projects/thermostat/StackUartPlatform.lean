import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option maxRecDepth 3000
namespace E5R.Thermostat.StackUartPlatform
open E5R E5R.Thermostat
abbrev board := StackBoard.board

theorem outside (a : Word) (below : a.toNat<0x80000000) : board.inRam a 1=false := by
  cases found : board.inRam a 1 with
  | false => rfl
  | true =>
    have large := StackBoard.included found
    rw [UartPlatform.outside a below] at large
    cases large

theorem lsr_device : board.device? 0x10000005#32=some UartPlatform.lsr := by
  rw [StackBoard.devices];exact UartPlatform.lsr_device

theorem data_device : board.device? 0x10000000#32=some UartPlatform.data := by
  rw [StackBoard.devices];exact UartPlatform.data_device

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
  have e3 : romRead? img a.toNat Width.b.bytes false = none := UartPlatform.rom_none a.toNat hbelow
  have e4 : (d.read && decide (Width.b.bytes = d.width)) = true := by simp [hr,hw,Width.bytes]
  rw [ite_eq_right_of_eq_false _ _ (eq_false e1),e2,ite_eq_right (by decide),ite_eq_right (by decide),e3]
  simp only [hd,e4,ite_true]
  rfl
end E5R.Thermostat.StackUartPlatform
