-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ReadReplyFlags
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.ReadReplyFlags
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (fp : Word)
    (hp : c.pc=0x80001ba2#32) (h8 : c.get 8=fp) (h22 : c.get 22=1#32)
    (hm : Memory.Block B fp 753) :
    Quiet.Steps B img 4 ⟨c,ram⟩ ⟨c.goto 0x80001704#32,memory ram fp⟩ := by
  let a := c.goto 0x80001ba6#32
  let b := a.goto 0x80001baa#32
  let z := b.goto 0x80001bae#32
  let r1 := ramWrite ram (fp+708#32) 1#32 .b
  let r2 := ramWrite r1 (fp+748#32) 1#32 .b
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,r1⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact rr2147490722) fun o => ?_
    rw [exec_store,h8,h22,interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 708) (by decide) (by decide)),hp]
    rfl
  have s1 : Quiet.Step B img ⟨a,r1⟩ ⟨b,r2⟩ := by
    refine QuietDet.step_of (by change (0x80001ba6#32).getLsbD 0=false;decide) rr2147490726 fun o => ?_
    have a8 : a.get 8=fp := h8
    have a22 : a.get 22=1#32 := h22
    rw [exec_store,a8,a22,interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 748) (by decide) (by decide))]
    rfl
  have s2 : Quiet.Step B img ⟨b,r2⟩ ⟨z,memory ram fp⟩ := by
    refine QuietDet.step_of (by change (0x80001baa#32).getLsbD 0=false;decide) rr2147490730 fun o => ?_
    have b8 : b.get 8=fp := h8
    have b22 : b.get 22=1#32 := h22
    rw [exec_store,b8,b22,interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 752) (by decide) (by decide))]
    rfl
  have s3 : Quiet.Step B img ⟨z,memory ram fp⟩ ⟨c.goto 0x80001704#32,memory ram fp⟩ := by
    refine QuietDet.step_of (by change (0x80001bae#32).getLsbD 0=false;decide) rr2147490734 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump z (0x80001bae#32+0xfffffb56#32)) (memory ram fp) 0 [] = _
    rw [show (0x80001bae#32+0xfffffb56#32)=0x80001704#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact .step s0 (.step s1 (.step s2 (.single s3)))

end E5R.Thermostat.ReadReplyFlags
