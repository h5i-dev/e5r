-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Boot
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.Boot
theorem mask_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000000) (hm : c.mpp = 0 ∨ c.mpp = 3) :
    Quiet.Steps B img 2 ⟨c,ram⟩ ⟨masked c,ram⟩ := by
  let c1 : Core := { c with pc := 0x80000004, mieReg := 0 }
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact bt2147483648) fun o => ?_
    simp only [exec,execCsr,csrRead,csrWrite,csrMie,csrMstatus,Core.set_zero]
    rw [hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨masked c,ram⟩ := by
    refine QuietDet.step_of (by change (0x80000004 : Word).getLsbD 0 = false;decide) bt2147483652 fun o => ?_
    change interp B img o (exec c1 4 (.csr .rc 0 (.imm 8) csrMstatus)) ram 0 [] = _
    rw [clear_mie_exec c1 (by simpa [c1] using hm)]
    rfl
  exact .step s0 (.single s1)

end E5R.Thermostat.Boot
namespace E5R.Thermostat.Boot
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000000) (hm : c.mpp = 0 ∨ c.mpp = 3) :
    Quiet.Steps B img 11 ⟨c,ram⟩ ⟨mainEntry c,ram⟩ := by
  have h0 := E5R.Thermostat.Boot.mask_quiet B c ram hp hm
  let c0 := masked c
  let c1 := c0.wr 2 0x81000008 0x8000000c
  let c2 := c1.wr 2 0x81000000 0x80000010
  let c3 := c2.wr 5 0x80006010 0x80000014
  let c4 := c3.wr 5 0x80005f18 0x80000018
  let c5 := c4.wr 6 0x80006018 0x8000001c
  let c6 := c5.wr 6 0x80005f18 0x80000020
  let c7 := c6.goto 0x8000002c
  let c8 := c7.wr 1 0x8000102c 0x80000030
  let c9 := c8.wr 1 0x80000034 0x80000862

  have s0 : Quiet.Step B img ⟨c0,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by change (2147483656#32).getLsbD 0 = false;decide) bt2147483656 fun o => ?_
    have hpc : c0.pc = 2147483656 := by rfl
    rw [exec_auipc,hpc]
    rw [show (2147483656 : Word)+16777216#32 = (2164260872 : Word) by decide +kernel]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (2147483660#32).getLsbD 0 = false;decide) bt2147483660 fun o => ?_
    have hv : c1.get 2 = 0x81000008 := by simp [c0,c1,Core.wr_get]
    rw [exec_opimm,hv]
    simp only [alu]
    rw [show (2164260872 : Word)+4294967288#32 = (2164260864 : Word) by decide +kernel]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (2147483664#32).getLsbD 0 = false;decide) bt2147483664 fun o => ?_
    have hpc : c2.pc = 2147483664 := by rfl
    rw [exec_auipc,hpc]
    rw [show (2147483664 : Word)+24576#32 = (2147508240 : Word) by decide +kernel]
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (2147483668#32).getLsbD 0 = false;decide) bt2147483668 fun o => ?_
    have hv : c3.get 5 = 0x80006010 := by simp [c0,c1,c2,c3,Core.wr_get]
    rw [exec_opimm,hv]
    simp only [alu]
    rw [show (2147508240 : Word)+4294967048#32 = (2147507992 : Word) by decide +kernel]
    rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (2147483672#32).getLsbD 0 = false;decide) bt2147483672 fun o => ?_
    have hpc : c4.pc = 2147483672 := by rfl
    rw [exec_auipc,hpc]
    rw [show (2147483672 : Word)+24576#32 = (2147508248 : Word) by decide +kernel]
    rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (2147483676#32).getLsbD 0 = false;decide) bt2147483676 fun o => ?_
    have hv : c5.get 6 = 0x80006018 := by simp [c0,c1,c2,c3,c4,c5,Core.wr_get]
    rw [exec_opimm,hv]
    simp only [alu]
    rw [show (2147508248 : Word)+4294967040#32 = (2147507992 : Word) by decide +kernel]
    rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (2147483680#32).getLsbD 0 = false;decide) bt2147483680 fun o => ?_
    have hv5 : c6.get 5 = 0x80005f18 := by simp [c0,c1,c2,c3,c4,c5,c6,Core.wr_get]
    have hv6 : c6.get 6 = 0x80005f18 := by simp [c0,c1,c2,c3,c4,c5,c6,Core.wr_get]
    rw [exec_branch,hv5,hv6]
    have ht : taken .geu 0x80005f18 0x80005f18 = true := by decide +kernel
    rw [ht]
    simp only [ite_true]
    have hpc : c6.pc+12#32 = 0x8000002c := by change (0x80000020 : Word)+12#32 = _;decide +kernel
    rw [hpc,jump_ok c6 _ (by decide)]
    rfl
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (2147483692#32).getLsbD 0 = false;decide) bt2147483692 fun o => ?_
    have hpc : c7.pc = 2147483692 := by rfl
    rw [exec_auipc,hpc]
    rw [show (2147483692 : Word)+4096#32 = (2147487788 : Word) by decide +kernel]
    rfl
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (2147483696#32).getLsbD 0 = false;decide) bt2147483696 fun o => ?_
    have hv : c8.get 1 = 0x8000102c := by simp [c0,c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get]
    rw [exec_jalr,hv]
    rw [show ((0x8000102c : Word)+0xfffff836#32) &&& ~~~1 = (0x80000862 : Word) by decide +kernel]
    rfl
  have h1 : Quiet.Steps B img 9 ⟨masked c,ram⟩ ⟨mainEntry c,ram⟩ := .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.single s8))))))))
  exact h0.trans h1

end E5R.Thermostat.Boot
