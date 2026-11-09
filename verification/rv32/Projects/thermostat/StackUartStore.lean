import Projects.thermostat.UartStore
import Projects.thermostat.ProtocolStreamSpec
import Projects.thermostat.StackUartPlatform
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackUartStore
open E5R E5R.Thermostat ProtocolStreamSpec 
abbrev B := StackBoard.board
theorem store (m : Machine) (o : Oracle) (rs1 rs2 : Reg) (off len a value : Word) (d : DevReg)
    (hal : m.core.pc.getLsbD 0=false)
    (hf : fetchDecode img m.core.pc=some (.store .b rs1 rs2 off,len))
    (ha : m.core.get rs1+off=a) (hv : m.core.get rs2=value) (hbelow : a.toNat<0x80000000)
    (hd : StackBoard.board.device? a=some d) (hw : d.write=true) (hb : d.width=1) :
    Observed.stepInstr StackBoard.board img m o =
      ⟨.ok (m.core.goto (m.core.pc+len)) m.ram [⟨a,devVal .b value⟩],[]⟩ := by
  rw [Observed.stepInstr_of hal hf,exec_store,ha,hv]
  unfold Observed.interp
  have e1 : ¬(a.toNat%Width.b.bytes≠0) := by simp [Width.bytes,Nat.mod_one]
  have e2 : StackBoard.board.inRam a Width.b.bytes=false := StackUartPlatform.outside a hbelow
  have e3 : (d.write && decide (Width.b.bytes=d.width))=true := by simp [hw,hb,Width.bytes]
  rw [ite_eq_right e1,e2,ite_eq_right (by decide),ite_eq_right (by decide)]
  simp only [hd,e3,ite_true]
  rfl
end E5R.Thermostat.StackUartStore
