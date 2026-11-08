import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadVersionSave
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+28#32) (targetEnd) .w) (sp+24#32) (targetStart) .w) (sp+32#32) (mask) .w) (sp+40#32) (n) .w) (sp+36#32) (maxHead) .w) (sp+44#32) (buf) .w) (sp+52#32) (dst) .w) (sp+48#32) (length) .w) (sp+20#32) (methodEnd) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp targetEnd targetStart mask n maxHead buf dst length methodEnd : Word) (h2 : c.get 2=sp) (h18 : c.get 18=targetEnd) (h29 : c.get 29=targetStart) (h5 : c.get 5=mask) (h14 : c.get 14=n) (h16 : c.get 16=maxHead) (h11 : c.get 11=buf) (h10 : c.get 10=dst) (h12 : c.get 12=length) (h17 : c.get 17=methodEnd)
(hm : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80002e2c#32) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,memory ram sp targetEnd targetStart mask n maxHead buf dst length methodEnd⟩ ∧ d.pc=0x80002e3e#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram (sp+28#32) (targetEnd) .w
  let c1 := c.goto 0x80002e2e#32
  let r2 := ramWrite r1 (sp+24#32) (targetStart) .w
  let c2 := c1.goto 0x80002e30#32
  let r3 := ramWrite r2 (sp+32#32) (mask) .w
  let c3 := c2.goto 0x80002e32#32
  let r4 := ramWrite r3 (sp+40#32) (n) .w
  let c4 := c3.goto 0x80002e34#32
  let r5 := ramWrite r4 (sp+36#32) (maxHead) .w
  let c5 := c4.goto 0x80002e36#32
  let r6 := ramWrite r5 (sp+44#32) (buf) .w
  let c6 := c5.goto 0x80002e38#32
  let r7 := ramWrite r6 (sp+52#32) (dst) .w
  let c7 := c6.goto 0x80002e3a#32
  let r8 := ramWrite r7 (sp+48#32) (length) .w
  let c8 := c7.goto 0x80002e3c#32
  let r9 := ramWrite r8 (sp+20#32) (methodEnd) .w
  let c9 := c8.goto 0x80002e3e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495468) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 r1 [],[]⟩
    have v2 : c.get 2=sp := by simp [Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    have vv : c.get 18=targetEnd := by simp [Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    rw [exec_store,v2,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 7 ha)
      (Memory.block_access hm (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
    refine Quiet.step_of (by change (0x80002e2e#32).getLsbD 0=false;decide) hh2147495470 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) r1 0 [] [] = ⟨.ok c2 r2 [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    have vv : c1.get 29=targetStart := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    rw [exec_store,v2,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 6 ha)
      (Memory.block_access hm (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r2⟩ ⟨c3,r3⟩ := by
    refine Quiet.step_of (by change (0x80002e30#32).getLsbD 0=false;decide) hh2147495472 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r2 0 [] [] = ⟨.ok c3 r3 [],[]⟩
    have v2 : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    have vv : c2.get 5=mask := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    rw [exec_store,v2,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 8 ha)
      (Memory.block_access hm (off := 32) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r3⟩ ⟨c4,r4⟩ := by
    refine Quiet.step_of (by change (0x80002e32#32).getLsbD 0=false;decide) hh2147495474 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r3 0 [] [] = ⟨.ok c4 r4 [],[]⟩
    have v2 : c3.get 2=sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    have vv : c3.get 14=n := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    rw [exec_store,v2,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 10 ha)
      (Memory.block_access hm (off := 40) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r4⟩ ⟨c5,r5⟩ := by
    refine Quiet.step_of (by change (0x80002e34#32).getLsbD 0=false;decide) hh2147495476 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r4 0 [] [] = ⟨.ok c5 r5 [],[]⟩
    have v2 : c4.get 2=sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    have vv : c4.get 16=maxHead := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    rw [exec_store,v2,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 9 ha)
      (Memory.block_access hm (off := 36) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r5⟩ ⟨c6,r6⟩ := by
    refine Quiet.step_of (by change (0x80002e36#32).getLsbD 0=false;decide) hh2147495478 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r5 0 [] [] = ⟨.ok c6 r6 [],[]⟩
    have v2 : c5.get 2=sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    have vv : c5.get 11=buf := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    rw [exec_store,v2,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 11 ha)
      (Memory.block_access hm (off := 44) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r6⟩ ⟨c7,r7⟩ := by
    refine Quiet.step_of (by change (0x80002e38#32).getLsbD 0=false;decide) hh2147495480 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r6 0 [] [] = ⟨.ok c7 r7 [],[]⟩
    have v2 : c6.get 2=sp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    have vv : c6.get 10=dst := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    rw [exec_store,v2,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 13 ha)
      (Memory.block_access hm (off := 52) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r7⟩ ⟨c8,r8⟩ := by
    refine Quiet.step_of (by change (0x80002e3a#32).getLsbD 0=false;decide) hh2147495482 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r7 0 [] [] = ⟨.ok c8 r8 [],[]⟩
    have v2 : c7.get 2=sp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    have vv : c7.get 12=length := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    rw [exec_store,v2,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
      (Memory.block_access hm (off := 48) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r8⟩ ⟨c9,r9⟩ := by
    refine Quiet.step_of (by change (0x80002e3c#32).getLsbD 0=false;decide) hh2147495484 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r8 0 [] [] = ⟨.ok c9 r9 [],[]⟩
    have v2 : c8.get 2=sp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    have vv : c8.get 17=methodEnd := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
    rw [exec_store,v2,vv,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 5 ha)
      (Memory.block_access hm (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c9,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.single t8)))))))),rfl,?_ ,by rfl⟩
  · intro reg ;simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h18,h29,h5,h14,h16,h11,h10,h12,h17]
end E5R.Thermostat.HeadVersionSave
