import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option autoImplicit false
namespace E5R.Thermostat.QuietByteLoad
open E5R E5R.Thermostat

/-- One actual checked LBU from RAM. Decode, PC alignment and RAM access are
    explicit obligations; arbitrary device reads cannot satisfy this contract. -/
theorem contract (B : Board) (img : List Segment) (c : Core) (ram : Word → BitVec 8)
    (pc base off : Word) (rd rs : Reg) (byte : BitVec 8)
    (hp : c.pc=pc) (halign : pc.getLsbD 0=false) (nonzero : rd.val≠0)
    (fetched : fetchDecode img pc=some (.load .b false rd rs off,4#32)) (source : c.get rs=base)
    (memory : B.inRam (base+off) 1=true) (data : ram (base+off)=byte) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=pc+4#32 ∧ d.get rd=BitVec.ofNat 32 byte.toNat ∧
      (∀ r : Reg, r≠rd → d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.wr rd (BitVec.ofNat 32 byte.toNat) (pc+4#32)
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];exact halign) (by rw [hp];exact fetched) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    rw [exec_load,source,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) memory,Memory.load_byte,data,hp]
    rfl
  exact ⟨d,.single step,rfl,Core.wr_get_self _ _ _ _ nonzero,fun r neq => Core.wr_get_ne _ _ _ _ _ neq,Core.sameCsr_wr _ _ _ _⟩
end E5R.Thermostat.QuietByteLoad
