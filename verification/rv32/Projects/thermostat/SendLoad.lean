import Projects.thermostat.SendCode
import Projects.thermostat.QuietRam
import Projects.thermostat.StoreRead
import Projects.thermostat.ResponseHeadBodyMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SendLoad
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (obj tx io ctptr : Word) :=
  ramWrite (ramWrite (ramWrite (ram) (obj+16#32) (io) .w) (obj+0#32) (tx+192#32) .w) (obj+4#32) (832#32) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj tx io ctptr : Word) (ctlen status body : Nat) (close head : Bool) (h8 : c.get 8=obj) (hm : Memory.Block B obj 89) (ha : obj.toNat%4=0) (hcap : ramRead ram (obj+12#32) .w=1024#32) (hio : ramRead ram (obj+24#32) .w=io) (htx : ramRead ram (obj+8#32) .w=tx) (hct : ramRead ram (obj+28#32) .w=ctptr) (hlen : ramRead ram (obj+32#32) .w=BitVec.ofNat 32 ctlen) (hbody : ramRead ram (obj+36#32) .w=BitVec.ofNat 32 body) (hstatus : extend .h false (ramRead ram (obj+40#32) .h)=BitVec.ofNat 32 status) (hclose : extend .b false (ramRead ram (obj+42#32) .b)=ResponseHeadBodyMath.boolWord close) (hhead : extend .b false (ramRead ram (obj+46#32) .b)=ResponseHeadBodyMath.boolWord head)
    (hp : c.pc=0x8000036a#32) :
    ∃ d, Quiet.Steps B img 16 ⟨c,ram⟩ ⟨d,memory ram obj tx io ctptr⟩ ∧ d.pc=0x8000039c#32 ∧
      d.get 10=1024#32 ∧ d.get 11=BitVec.ofNat 32 body ∧ d.get 12=tx+192#32 ∧ d.get 19=tx ∧ d.get 13=ctptr ∧ d.get 14=BitVec.ofNat 32 ctlen ∧ d.get 21=BitVec.ofNat 32 status ∧ d.get 22=ResponseHeadBodyMath.boolWord close ∧ d.get 23=ResponseHeadBodyMath.boolWord head ∧ d.get 20=832#32 ∧ (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠19 → r≠13 → r≠14 → r≠21 → r≠22 → r≠23 → r≠20 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (1024#32) 0x8000036c#32
  let c2 := c1.wr 11 (io) 0x8000036e#32
  let c3 := c2.wr 12 (191#32) 0x80000372#32
  let r1 := ramWrite ram (obj+16#32) (io) .w
  let c4 := c3.goto 0x80000374#32
  let c5 := c4.goto 0x80000378#32
  let c6 := c5.wr 19 (tx) 0x8000037c#32
  let c7 := c6.wr 13 (ctptr) 0x8000037e#32
  let c8 := c7.wr 14 (BitVec.ofNat 32 ctlen) 0x80000380#32
  let c9 := c8.wr 11 (BitVec.ofNat 32 body) 0x80000382#32
  let c10 := c9.wr 21 (BitVec.ofNat 32 status) 0x80000386#32
  let c11 := c10.wr 22 (ResponseHeadBodyMath.boolWord close) 0x8000038a#32
  let c12 := c11.wr 23 (ResponseHeadBodyMath.boolWord head) 0x8000038e#32
  let c13 := c12.wr 12 (tx+192#32) 0x80000392#32
  let c14 := c13.wr 20 (832#32) 0x80000396#32
  let r2 := ramWrite r1 (obj+0#32) (tx+192#32) .w
  let c15 := c14.goto 0x80000398#32
  let r3 := ramWrite r2 (obj+4#32) (832#32) .w
  let c16 := c15.goto 0x8000039c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact se2147484522) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=obj := by simp [Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))]
    rw [hcap];first | rfl | (rw [hp]; rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000036c#32).getLsbD 0=false;decide) se2147484524 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=obj := by simp [c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 6 ha) (Memory.block_access hm (off := 24) (by decide) (by decide))]
    rw [hio];first | rfl | (rw [hp]; rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000036e#32).getLsbD 0=false;decide) se2147484526 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x80000372#32).getLsbD 0=false;decide) se2147484530 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v8 : c3.get 8=obj := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    have v11 : c3.get 11=io := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_store,v8,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x80000374#32).getLsbD 0=false;decide) se2147484532 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v12 : c4.get 12=191#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    have v10 : c4.get 10=1024#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_branch,v12,v10,show taken .geu 191#32 1024#32=false by decide];simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r1⟩ := by
    refine Quiet.step_of (by change (0x80000378#32).getLsbD 0=false;decide) se2147484536 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r1 0 [] [] = ⟨.ok c6 r1 [],[]⟩
    have v8 : c5.get 8=obj := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))]
    have he : ramRead r1 (obj+8#32) .w=ramRead ram (obj+8#32) .w := StoreRead.other ram (obj+8#32) (obj+16#32) io .w .w (StoreWords.offsets obj 8 4 16 4 (by decide) (by decide) (by decide))
    rw [he]
    rw [htx];first | rfl | (rw [hp]; rfl)
  have t6 : Quiet.Step B img ⟨c6,r1⟩ ⟨c7,r1⟩ := by
    refine Quiet.step_of (by change (0x8000037c#32).getLsbD 0=false;decide) se2147484540 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r1 0 [] [] = ⟨.ok c7 r1 [],[]⟩
    have v8 : c6.get 8=obj := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 7 ha) (Memory.block_access hm (off := 28) (by decide) (by decide))]
    have he : ramRead r1 (obj+28#32) .w=ramRead ram (obj+28#32) .w := StoreRead.other ram (obj+28#32) (obj+16#32) io .w .w (StoreWords.offsets obj 28 4 16 4 (by decide) (by decide) (by decide))
    rw [he]
    rw [hct];first | rfl | (rw [hp]; rfl)
  have t7 : Quiet.Step B img ⟨c7,r1⟩ ⟨c8,r1⟩ := by
    refine Quiet.step_of (by change (0x8000037e#32).getLsbD 0=false;decide) se2147484542 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r1 0 [] [] = ⟨.ok c8 r1 [],[]⟩
    have v8 : c7.get 8=obj := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 8 ha) (Memory.block_access hm (off := 32) (by decide) (by decide))]
    have he : ramRead r1 (obj+32#32) .w=ramRead ram (obj+32#32) .w := StoreRead.other ram (obj+32#32) (obj+16#32) io .w .w (StoreWords.offsets obj 32 4 16 4 (by decide) (by decide) (by decide))
    rw [he]
    rw [hlen];first | rfl | (rw [hp]; rfl)
  have t8 : Quiet.Step B img ⟨c8,r1⟩ ⟨c9,r1⟩ := by
    refine Quiet.step_of (by change (0x80000380#32).getLsbD 0=false;decide) se2147484544 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r1 0 [] [] = ⟨.ok c9 r1 [],[]⟩
    have v8 : c8.get 8=obj := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 9 ha) (Memory.block_access hm (off := 36) (by decide) (by decide))]
    have he : ramRead r1 (obj+36#32) .w=ramRead ram (obj+36#32) .w := StoreRead.other ram (obj+36#32) (obj+16#32) io .w .w (StoreWords.offsets obj 36 4 16 4 (by decide) (by decide) (by decide))
    rw [he]
    rw [hbody];first | rfl | (rw [hp]; rfl)
  have t9 : Quiet.Step B img ⟨c9,r1⟩ ⟨c10,r1⟩ := by
    refine Quiet.step_of (by change (0x80000382#32).getLsbD 0=false;decide) se2147484546 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r1 0 [] [] = ⟨.ok c10 r1 [],[]⟩
    have v8 : c9.get 8=obj := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned obj 20 (by omega)) (Memory.block_access hm (off := 40) (by decide) (by decide))]
    have he : ramRead r1 (obj+40#32) .h=ramRead ram (obj+40#32) .h := StoreRead.other ram (obj+40#32) (obj+16#32) io .h .w (StoreWords.offsets obj 40 2 16 4 (by decide) (by decide) (by decide))
    rw [he]
    rw [hstatus];first | rfl | (rw [hp]; rfl)
  have t10 : Quiet.Step B img ⟨c10,r1⟩ ⟨c11,r1⟩ := by
    refine Quiet.step_of (by change (0x80000386#32).getLsbD 0=false;decide) se2147484550 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r1 0 [] [] = ⟨.ok c11 r1 [],[]⟩
    have v8 : c10.get 8=obj := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 42) (by decide) (by decide))]
    have he : ramRead r1 (obj+42#32) .b=ramRead ram (obj+42#32) .b := StoreRead.other ram (obj+42#32) (obj+16#32) io .b .w (StoreWords.offsets obj 42 1 16 4 (by decide) (by decide) (by decide))
    rw [he]
    rw [hclose];first | rfl | (rw [hp]; rfl)
  have t11 : Quiet.Step B img ⟨c11,r1⟩ ⟨c12,r1⟩ := by
    refine Quiet.step_of (by change (0x8000038a#32).getLsbD 0=false;decide) se2147484554 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r1 0 [] [] = ⟨.ok c12 r1 [],[]⟩
    have v8 : c11.get 8=obj := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 46) (by decide) (by decide))]
    have he : ramRead r1 (obj+46#32) .b=ramRead ram (obj+46#32) .b := StoreRead.other ram (obj+46#32) (obj+16#32) io .b .w (StoreWords.offsets obj 46 1 16 4 (by decide) (by decide) (by decide))
    rw [he]
    rw [hhead];first | rfl | (rw [hp]; rfl)
  have t12 : Quiet.Step B img ⟨c12,r1⟩ ⟨c13,r1⟩ := by
    refine Quiet.step_of (by change (0x8000038e#32).getLsbD 0=false;decide) se2147484558 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r1 0 [] [] = ⟨.ok c13 r1 [],[]⟩
    have v19 : c12.get 19=tx := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_opimm,v19];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r1⟩ ⟨c14,r1⟩ := by
    refine Quiet.step_of (by change (0x80000392#32).getLsbD 0=false;decide) se2147484562 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r1 0 [] [] = ⟨.ok c14 r1 [],[]⟩
    have v10 : c13.get 10=1024#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r1⟩ ⟨c15,r2⟩ := by
    refine Quiet.step_of (by change (0x80000396#32).getLsbD 0=false;decide) se2147484566 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r1 0 [] [] = ⟨.ok c15 r2 [],[]⟩
    have v8 : c14.get 8=obj := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    have v12 : c14.get 12=tx+192#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_store,v8,v12,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 0 ha) (Memory.block_access hm (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r2⟩ ⟨c16,r3⟩ := by
    refine Quiet.step_of (by change (0x80000398#32).getLsbD 0=false;decide) se2147484568 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r2 0 [] [] = ⟨.ok c16 r3 [],[]⟩
    have v8 : c15.get 8=obj := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    have v20 : c15.get 20=832#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_store,v8,v20,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned obj 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c16,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.single t15))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · intro reg h10 h11 h12 h19 h13 h14 h21 h22 h23 h20;simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h12,h19,h13,h14,h21,h22,h23,h20]
end E5R.Thermostat.SendLoad
