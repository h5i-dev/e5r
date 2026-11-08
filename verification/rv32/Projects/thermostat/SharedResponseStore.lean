import Projects.thermostat.SharedResponseCode
import Projects.thermostat.Memory
namespace E5R.Thermostat.SharedResponseStore
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp fp io0 io1 io2 saved status mimeLength mime close methodMinus used : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (fp+108#32) (io0) .w) (fp+112#32) (io1) .w) (fp+124#32) (io2) .w) (fp+128#32) (mime) .w) (fp+132#32) (mimeLength) .w) (fp+136#32) (used) .w) (fp+140#32) (status) .h) (fp+142#32) (close) .b) (sp+20#32) (saved) .w) (fp+143#32) (saved) .b) (fp+145#32) (0) .b) (fp+146#32) (alu .sltu methodMinus 1#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp fp io0 io1 io2 saved status mimeLength mime close methodMinus used : Word)
    (hp : c.pc=0x80001740#32)
    (h2 : c.get 2=sp)
    (h5 : c.get 5=io2)
    (h6 : c.get 6=saved)
    (h8 : c.get 8=fp)
    (h10 : c.get 10=status)
    (h11 : c.get 11=mimeLength)
    (h12 : c.get 12=mime)
    (h13 : c.get 13=close)
    (h14 : c.get 14=methodMinus)
    (h16 : c.get 16=io0)
    (h17 : c.get 17=io1)
    (h20 : c.get 20=used)
    (hm : Memory.Block B fp 148) (ha : fp.toNat%4=0) (hs : Memory.Block B sp 24) (hsa : sp.toNat%4=0) :
    ∃ d, DetSteps B img 13 ⟨c,ram⟩ ⟨d,memory ram sp fp io0 io1 io2 saved status mimeLength mime close methodMinus used⟩ ∧ d.pc=0x80001772#32 ∧
      d.get 12=alu .sltu methodMinus 1#32 ∧ (∀ r : Reg, r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80001744#32
  let r1 := ramWrite ram (fp+108#32) (io0) .w
  let c2 := c1.goto 0x80001748#32
  let r2 := ramWrite r1 (fp+112#32) (io1) .w
  let c3 := c2.goto 0x8000174c#32
  let r3 := ramWrite r2 (fp+124#32) (io2) .w
  let c4 := c3.goto 0x80001750#32
  let r4 := ramWrite r3 (fp+128#32) (mime) .w
  let c5 := c4.wr 12 (alu .sltu methodMinus 1#32) 0x80001754#32
  let c6 := c5.goto 0x80001758#32
  let r5 := ramWrite r4 (fp+132#32) (mimeLength) .w
  let c7 := c6.goto 0x8000175c#32
  let r6 := ramWrite r5 (fp+136#32) (used) .w
  let c8 := c7.goto 0x80001760#32
  let r7 := ramWrite r6 (fp+140#32) (status) .h
  let c9 := c8.goto 0x80001764#32
  let r8 := ramWrite r7 (fp+142#32) (close) .b
  let c10 := c9.goto 0x80001766#32
  let r9 := ramWrite r8 (sp+20#32) (saved) .w
  let c11 := c10.goto 0x8000176a#32
  let r10 := ramWrite r9 (fp+143#32) (saved) .b
  let c12 := c11.goto 0x8000176e#32
  let r11 := ramWrite r10 (fp+145#32) (0) .b
  let c13 := c12.goto 0x80001772#32
  let r12 := ramWrite r11 (fp+146#32) (alu .sltu methodMinus 1#32) .b
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact sr2147489600) fun o => ?_
    have vbase : c.get 8=fp := by simp [Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    have vval : c.get 16=io0 := by simp [Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    rw [exec_store,vbase,vval,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 27 ha) (Memory.block_access hm (off := 108) (by decide) (by decide))]
    rw [hp]
    rfl
  have s1 : DetStep B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
    refine detStep_of (by change (0x80001744#32).getLsbD 0=false;decide) sr2147489604 fun o => ?_
    have vbase : c1.get 8=fp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    have vval : c1.get 17=io1 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    rw [exec_store,vbase,vval,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 28 ha) (Memory.block_access hm (off := 112) (by decide) (by decide))]
    rfl
  have s2 : DetStep B img ⟨c2,r2⟩ ⟨c3,r3⟩ := by
    refine detStep_of (by change (0x80001748#32).getLsbD 0=false;decide) sr2147489608 fun o => ?_
    have vbase : c2.get 8=fp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    have vval : c2.get 5=io2 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    rw [exec_store,vbase,vval,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 31 ha) (Memory.block_access hm (off := 124) (by decide) (by decide))]
    rfl
  have s3 : DetStep B img ⟨c3,r3⟩ ⟨c4,r4⟩ := by
    refine detStep_of (by change (0x8000174c#32).getLsbD 0=false;decide) sr2147489612 fun o => ?_
    have vbase : c3.get 8=fp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    have vval : c3.get 12=mime := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    rw [exec_store,vbase,vval,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 32 ha) (Memory.block_access hm (off := 128) (by decide) (by decide))]
    rfl
  have s4 : DetStep B img ⟨c4,r4⟩ ⟨c5,r4⟩ := by
    refine detStep_of (by change (0x80001750#32).getLsbD 0=false;decide) sr2147489616 fun o => ?_
    have v14 : c4.get 14=methodMinus := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    rw [exec_opimm,v14];rfl
  have s5 : DetStep B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    refine detStep_of (by change (0x80001754#32).getLsbD 0=false;decide) sr2147489620 fun o => ?_
    have vbase : c5.get 8=fp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    have vval : c5.get 11=mimeLength := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    rw [exec_store,vbase,vval,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 33 ha) (Memory.block_access hm (off := 132) (by decide) (by decide))]
    rfl
  have s6 : DetStep B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    refine detStep_of (by change (0x80001758#32).getLsbD 0=false;decide) sr2147489624 fun o => ?_
    have vbase : c6.get 8=fp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    have vval : c6.get 20=used := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    rw [exec_store,vbase,vval,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 34 ha) (Memory.block_access hm (off := 136) (by decide) (by decide))]
    rfl
  have s7 : DetStep B img ⟨c7,r6⟩ ⟨c8,r7⟩ := by
    refine detStep_of (by change (0x8000175c#32).getLsbD 0=false;decide) sr2147489628 fun o => ?_
    have vbase : c7.get 8=fp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    have vval : c7.get 10=status := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    rw [exec_store,vbase,vval,interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned fp 70 (by omega)) (Memory.block_access hm (off := 140) (by decide) (by decide))]
    rfl
  have s8 : DetStep B img ⟨c8,r7⟩ ⟨c9,r8⟩ := by
    refine detStep_of (by change (0x80001760#32).getLsbD 0=false;decide) sr2147489632 fun o => ?_
    have vbase : c8.get 8=fp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    have vval : c8.get 13=close := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    rw [exec_store,vbase,vval,interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 142) (by decide) (by decide))]
    rfl
  have s9 : DetStep B img ⟨c9,r8⟩ ⟨c10,r9⟩ := by
    refine detStep_of (by change (0x80001764#32).getLsbD 0=false;decide) sr2147489636 fun o => ?_
    have vbase : c9.get 2=sp := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    have vval : c9.get 6=saved := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    rw [exec_store,vbase,vval,interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 5 hsa) (Memory.block_access hs (off := 20) (by decide) (by decide))]
    rfl
  have s10 : DetStep B img ⟨c10,r9⟩ ⟨c11,r10⟩ := by
    refine detStep_of (by change (0x80001766#32).getLsbD 0=false;decide) sr2147489638 fun o => ?_
    have vbase : c10.get 8=fp := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    have vval : c10.get 6=saved := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    rw [exec_store,vbase,vval,interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 143) (by decide) (by decide))]
    rfl
  have s11 : DetStep B img ⟨c11,r10⟩ ⟨c12,r11⟩ := by
    refine detStep_of (by change (0x8000176a#32).getLsbD 0=false;decide) sr2147489642 fun o => ?_
    have vbase : c11.get 8=fp := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    rw [exec_store,vbase,Core.get_zero,interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 145) (by decide) (by decide))]
    rfl
  have s12 : DetStep B img ⟨c12,r11⟩ ⟨c13,r12⟩ := by
    refine detStep_of (by change (0x8000176e#32).getLsbD 0=false;decide) sr2147489646 fun o => ?_
    have vbase : c12.get 8=fp := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    have vval : c12.get 12=alu .sltu methodMinus 1#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h5,h6,h8,h10,h11,h12,h13,h14,h16,h17,h20]
    rw [exec_store,vbase,vval,interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 146) (by decide) (by decide))]
    rfl
  refine ⟨c13,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.single s12)))))))))))),rfl,?_,?_,by rfl⟩
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro reg hr;simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,hr]
end E5R.Thermostat.SharedResponseStore
