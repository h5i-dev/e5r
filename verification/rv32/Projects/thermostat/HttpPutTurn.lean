import Projects.thermostat.HttpPutCode
import Projects.thermostat.ObservedByte
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpPutTurn
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (src dst pos cap finish : Word) (v : BitVec 8) :=
  ramWrite (ram) (dst+pos) (v.setWidth 32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst pos cap finish : Word) (v : BitVec 8) (last : Bool)
    (h10 : c.get 10=dst) (h11 : c.get 11=cap) (h13 : c.get 13=src)
    (h15 : c.get 15=pos) (h16 : c.get 16=finish) (hne : cap≠pos)
    (hs : ReadBytes.Byte B img ram src v) (hm : B.inRam (dst+pos) 1=true)
    (ht : taken .ne (src+1#32) finish=(!last))
    (hp : c.pc=0x8000414e#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,memory ram src dst pos cap finish v⟩ ∧ d.pc=(if last then 0x80004166#32 else 0x8000414e#32) ∧
      d.get 17=v.setWidth 32 ∧ d.get 5=dst+pos ∧ d.get 13=src+1#32 ∧ d.get 15=pos+1#32 ∧ (∀ r : Reg, r≠17 → r≠5 → r≠13 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80004152#32
  let c2 := c1.wr 17 (v.setWidth 32) 0x80004156#32
  let c3 := c2.wr 5 (dst+pos) 0x8000415a#32
  let c4 := c3.wr 13 (src+1#32) 0x8000415c#32
  let r1 := ramWrite ram (dst+pos) (v.setWidth 32) .b
  let c5 := c4.goto 0x80004160#32
  let c6 := c5.wr 15 (pos+1#32) 0x80004162#32
  let c7 := c6.goto (if last then 0x80004166#32 else 0x8000414e#32)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hp2147500366) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,h11,h15,show taken .eq cap pos=false by simp [taken,hne]]
    simp only [Bool.false_eq_true,ite_false];rw [hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80004152#32).getLsbD 0=false;decide) hp2147500370 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have hv : c1.get 13=src := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16]
    rw [exec_load,hv,BitVec.add_zero,ObservedByte.load hs o _ 0 [] [],ReadBytes.extend_byte];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80004156#32).getLsbD 0=false;decide) hp2147500374 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=dst := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16]
    have v15 : c2.get 15=pos := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16]
    rw [exec_op,v10,v15];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000415a#32).getLsbD 0=false;decide) hp2147500378 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have hv : c3.get 13=src := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x8000415c#32).getLsbD 0=false;decide) hp2147500380 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v5 : c4.get 5=dst+pos := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16]
    have v17 : c4.get 17=v.setWidth 32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16]
    rw [exec_store,v5,v17,BitVec.add_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hm];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r1⟩ := by
    refine Quiet.step_of (by change (0x80004160#32).getLsbD 0=false;decide) hp2147500384 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r1 0 [] [] = ⟨.ok c6 r1 [],[]⟩
    have hv : c5.get 15=pos := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16]
    rw [exec_opimm,hv];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r1⟩ ⟨c7,r1⟩ := by
    refine Quiet.step_of (by change (0x80004162#32).getLsbD 0=false;decide) hp2147500386 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r1 0 [] [] = ⟨.ok c7 r1 [],[]⟩
    have v13 : c6.get 13=src+1#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16]
    have v16 : c6.get 16=finish := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16]
    rw [exec_branch,v13,v16,ht]
    cases last with
    | false =>
      simp only [Bool.not_false,ite_true]
      rw [show c6.pc=0x80004162#32 by rfl,show 0x80004162#32+0xffffffec#32=0x8000414e#32 by decide +kernel]
      change Observed.interp B img o (jump c6 0x8000414e#32) r1 0 [] [] = _
      rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
    | true => rfl
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16]
  · intro reg h17 h5 h13 h15;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h13,h15,h16,h17,h5,h13,h15]
end E5R.Thermostat.HttpPutTurn
