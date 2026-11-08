-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CopyTwoFinal
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.CopyTwoFinal
theorem contract_quiet (c : Core) (ram : Word → BitVec 8) (sp dst : Word)
    (hp : c.pc=0x80005280#32)
    (h2 : c.get 2=sp)
    (h5 : c.get 5=2#32)
    (h6 : c.get 6=0x80005bc0#32)
    (h11 : c.get 11=0x80005ba6#32)
    (h14 : c.get 14=dst)
    (h16 : c.get 16=16#32)
    (h17 : c.get 17=0x676e6172#32)
    (hm : Memory.Block UartPlatform.board sp 16) (hd : Memory.Block UartPlatform.board dst 4) (ha : dst.toNat%4=0) :
    ∃ d, Quiet.Steps UartPlatform.board img 19 ⟨c,ram⟩ ⟨d,ramWrite (scratch ram sp) dst (UnalignedCopyData.lastPayload true) .w⟩ ∧
      d.pc=0x800052f0#32 ∧
      (∀ r : Reg, r≠5 → r≠6 → r≠7 → r≠16 → r≠17 → r≠28 → r≠29 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 7 (0x1#32) 0x80005282#32
  let r1 := ramWrite ram (sp+8#32) (0) .b
  let c2 := c1.goto 0x80005286#32
  let r2 := ramWrite r1 (sp+6#32) (0) .b
  let c3 := c2.goto 0x8000528a#32
  let c4 := c3.goto 0x800052a2#32
  let c5 := c4.wr 7 (0x65#32) 0x800052a6#32
  let c6 := c5.wr 5 (0x22#32) 0x800052aa#32
  let r3 := ramWrite r2 (sp+8#32) (0x65#32) .b
  let c7 := c6.goto 0x800052ae#32
  let c8 := c7.wr 5 (0x2200#32) 0x800052b0#32
  let c9 := c8.wr 29 (0x2#32) 0x800052b2#32
  let c10 := c9.wr 28 (sp+6#32) 0x800052b6#32
  let c11 := c10.wr 30 (0x0#32) 0x800052ba#32
  let c12 := c11.goto 0x800052d6#32
  let c13 := c12.wr 6 (0xfffffff0#32) 0x800052da#32
  let c14 := c13.wr 5 (0x2265#32) 0x800052dc#32
  let c15 := c14.wr 6 (0x10#32) 0x800052e0#32
  let c16 := c15.wr 16 (0x676e#32) 0x800052e4#32
  let c17 := c16.wr 17 (0x22650000#32) 0x800052e8#32
  let c18 := c17.wr 16 (0x2265676e#32) 0x800052ec#32
  let r4 := ramWrite r3 (dst) (0x2265676e#32) .w
  let c19 := c18.goto 0x800052f0#32
  have s0 : Quiet.Step UartPlatform.board img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504768) fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rw [hp]
    rfl
  have s1 : Quiet.Step UartPlatform.board img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine QuietDet.step_of (by change (0x80005282#32).getLsbD 0=false;decide) cp2147504770 fun o => ?_
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_store,v2,Core.get_zero]
    rw [interp_store_ram (B := UartPlatform.board) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 8) (by decide) (by decide))]
    rfl
  have s2 : Quiet.Step UartPlatform.board img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine QuietDet.step_of (by change (0x80005286#32).getLsbD 0=false;decide) cp2147504774 fun o => ?_
    have v2 : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_store,v2,Core.get_zero]
    rw [interp_store_ram (B := UartPlatform.board) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 6) (by decide) (by decide))]
    rfl
  have s3 : Quiet.Step UartPlatform.board img ⟨c3,r2⟩ ⟨c4,r2⟩ := by
    refine QuietDet.step_of (by change (0x8000528a#32).getLsbD 0=false;decide) cp2147504778 fun o => ?_
    have v5 : c3.get 5=2#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    have v7 : c3.get 7=0x1#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_branch,v5,v7,show taken .ne (2#32) (0x1#32)=true by decide +kernel]
    simp only [ite_true,ite_false]
    change interp UartPlatform.board img o (jump c3 0x800052a2#32) r2 0 [] = _
    rw [jump_ok _ _ (by decide)]
    rfl
  have s4 : Quiet.Step UartPlatform.board img ⟨c4,r2⟩ ⟨c5,r2⟩ := by
    refine QuietDet.step_of (by change (0x800052a2#32).getLsbD 0=false;decide) cp2147504802 fun o => ?_
    have v6 : c4.get 6=0x80005bc0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_load,v6]
    have haddr : 0x80005bc0#32+4#32=0x80005bc4#32 := by decide +kernel
    rw [haddr,interp_load_rom (B := UartPlatform.board) (img := img) (w := .b) o (by exact Nat.mod_one _) (by unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) rfl (by change romRead? img 2147507140 1 false=some 0x65#32;rw [PackedData.read_byte 2147507140 (by decide) (by decide)];decide +kernel)]
    rfl
  have s5 : Quiet.Step UartPlatform.board img ⟨c5,r2⟩ ⟨c6,r2⟩ := by
    refine QuietDet.step_of (by change (0x800052a6#32).getLsbD 0=false;decide) cp2147504806 fun o => ?_
    have v6 : c5.get 6=0x80005bc0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_load,v6]
    have haddr : 0x80005bc0#32+5#32=0x80005bc5#32 := by decide +kernel
    rw [haddr,interp_load_rom (B := UartPlatform.board) (img := img) (w := .b) o (by exact Nat.mod_one _) (by unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) rfl (by change romRead? img 2147507141 1 false=some 0x22#32;rw [PackedData.read_byte 2147507141 (by decide) (by decide)];decide +kernel)]
    rfl
  have s6 : Quiet.Step UartPlatform.board img ⟨c6,r2⟩ ⟨c7,r3⟩ := by
    refine QuietDet.step_of (by change (0x800052aa#32).getLsbD 0=false;decide) cp2147504810 fun o => ?_
    have v2 : c6.get 2=sp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    have v7 : c6.get 7=0x65#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_store,v2,v7]
    rw [interp_store_ram (B := UartPlatform.board) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 8) (by decide) (by decide))]
    rfl
  have s7 : Quiet.Step UartPlatform.board img ⟨c7,r3⟩ ⟨c8,r3⟩ := by
    refine QuietDet.step_of (by change (0x800052ae#32).getLsbD 0=false;decide) cp2147504814 fun o => ?_
    have v5 : c7.get 5=0x22#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_opimm,v5]
    rfl
  have s8 : Quiet.Step UartPlatform.board img ⟨c8,r3⟩ ⟨c9,r3⟩ := by
    refine QuietDet.step_of (by change (0x800052b0#32).getLsbD 0=false;decide) cp2147504816 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s9 : Quiet.Step UartPlatform.board img ⟨c9,r3⟩ ⟨c10,r3⟩ := by
    refine QuietDet.step_of (by change (0x800052b2#32).getLsbD 0=false;decide) cp2147504818 fun o => ?_
    have v2 : c9.get 2=sp := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_opimm,v2]
    rfl
  have s10 : Quiet.Step UartPlatform.board img ⟨c10,r3⟩ ⟨c11,r3⟩ := by
    refine QuietDet.step_of (by change (0x800052b6#32).getLsbD 0=false;decide) cp2147504822 fun o => ?_
    have v11 : c10.get 11=0x80005ba6#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_opimm,v11]
    rfl
  have s11 : Quiet.Step UartPlatform.board img ⟨c11,r3⟩ ⟨c12,r3⟩ := by
    refine QuietDet.step_of (by change (0x800052ba#32).getLsbD 0=false;decide) cp2147504826 fun o => ?_
    have v30 : c11.get 30=0x0#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_branch,v30,Core.get_zero,show taken .eq (0x0#32) (0)=true by decide +kernel]
    simp only [ite_true,ite_false]
    change interp UartPlatform.board img o (jump c11 0x800052d6#32) r3 0 [] = _
    rw [jump_ok _ _ (by decide)]
    rfl
  have s12 : Quiet.Step UartPlatform.board img ⟨c12,r3⟩ ⟨c13,r3⟩ := by
    refine QuietDet.step_of (by change (0x800052d6#32).getLsbD 0=false;decide) cp2147504854 fun o => ?_
    have v16 : c12.get 16=16#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_op,Core.get_zero,v16]
    rfl
  have s13 : Quiet.Step UartPlatform.board img ⟨c13,r3⟩ ⟨c14,r3⟩ := by
    refine QuietDet.step_of (by change (0x800052da#32).getLsbD 0=false;decide) cp2147504858 fun o => ?_
    have v5 : c13.get 5=0x2200#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    have v7 : c13.get 7=0x65#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_op,v5,v7]
    rfl
  have s14 : Quiet.Step UartPlatform.board img ⟨c14,r3⟩ ⟨c15,r3⟩ := by
    refine QuietDet.step_of (by change (0x800052dc#32).getLsbD 0=false;decide) cp2147504860 fun o => ?_
    have v6 : c14.get 6=0xfffffff0#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_opimm,v6]
    rfl
  have s15 : Quiet.Step UartPlatform.board img ⟨c15,r3⟩ ⟨c16,r3⟩ := by
    refine QuietDet.step_of (by change (0x800052e0#32).getLsbD 0=false;decide) cp2147504864 fun o => ?_
    have v17 : c15.get 17=0x676e6172#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    have v16 : c15.get 16=16#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_op,v17,v16]
    rfl
  have s16 : Quiet.Step UartPlatform.board img ⟨c16,r3⟩ ⟨c17,r3⟩ := by
    refine QuietDet.step_of (by change (0x800052e4#32).getLsbD 0=false;decide) cp2147504868 fun o => ?_
    have v5 : c16.get 5=0x2265#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    have v6 : c16.get 6=0x10#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_op,v5,v6]
    rfl
  have s17 : Quiet.Step UartPlatform.board img ⟨c17,r3⟩ ⟨c18,r3⟩ := by
    refine QuietDet.step_of (by change (0x800052e8#32).getLsbD 0=false;decide) cp2147504872 fun o => ?_
    have v17 : c17.get 17=0x22650000#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    have v16 : c17.get 16=0x676e#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_op,v17,v16]
    rfl
  have s18 : Quiet.Step UartPlatform.board img ⟨c18,r3⟩ ⟨c19,r4⟩ := by
    refine QuietDet.step_of (by change (0x800052ec#32).getLsbD 0=false;decide) cp2147504876 fun o => ?_
    have v14 : c18.get 14=dst := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    have v16 : c18.get 16=0x2265676e#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h11,h14,h16,h17]
    rw [exec_store,v14,v16]
    rw [BitVec.add_zero]
    rw [interp_store_ram (B := UartPlatform.board) (img := img) (w := .w) o ha (by simpa only [BitVec.add_zero] using Memory.block_access hd (off := 0) (by decide) (by decide))]
    rfl
  have run : Quiet.Steps UartPlatform.board img 19 ⟨c,ram⟩ ⟨c19,r4⟩ := .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.step s16 (.step s17 (.single s18))))))))))))))))))
  refine ⟨c19,?_,rfl,?_,by rfl⟩
  · simpa only [r1,r2,r3,r4,scratch,payload_eq,show (0 : Word)=0#32 from rfl] using run
  · intro r h5 h6 h7 h16 h17 h28 h29 h30
    simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h5,h6,h7,h16,h17,h28,h29,h30]

end E5R.Thermostat.CopyTwoFinal
