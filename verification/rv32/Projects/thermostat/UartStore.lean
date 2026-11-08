import Projects.thermostat.UartPlatform
namespace E5R.Thermostat.UartStore
open E5R E5R.Thermostat

/-- Faithful observed device-byte store; the existing board/interpreter
    determines the event and RAM remains unchanged for every oracle. -/
theorem store (m : Machine) (o : Oracle) (rs1 rs2 : Reg) (off len a value : Word) (d : DevReg)
    (hal : m.core.pc.getLsbD 0=false)
    (hf : fetchDecode img m.core.pc=some (.store .b rs1 rs2 off,len))
    (ha : m.core.get rs1+off=a) (hv : m.core.get rs2=value) (hbelow : a.toNat<0x80000000)
    (hd : UartPlatform.board.device? a=some d) (hw : d.write=true) (hb : d.width=1) :
    Observed.stepInstr UartPlatform.board img m o =
      ⟨.ok (m.core.goto (m.core.pc+len)) m.ram [⟨a,devVal .b value⟩],[]⟩ := by
  rw [Observed.stepInstr_of hal hf,exec_store,ha,hv]
  unfold Observed.interp
  have e1 : ¬(a.toNat%Width.b.bytes≠0) := by simp [Width.bytes,Nat.mod_one]
  have e2 : UartPlatform.board.inRam a Width.b.bytes=false := UartPlatform.outside a hbelow
  have e3 : (d.write && decide (Width.b.bytes=d.width))=true := by simp [hw,hb,Width.bytes]
  rw [ite_eq_right e1,e2,ite_eq_right (by decide),ite_eq_right (by decide)]
  simp only [hd,e3,ite_true]
  rfl
end E5R.Thermostat.UartStore
