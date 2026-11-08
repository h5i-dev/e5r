import Projects.thermostat.ReleaseCode
import Projects.thermostat.Encoding
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ReleaseBorrow
open E5R E5R.Thermostat

def result (ram : Word → BitVec 8) (eng : Word) := ramWrite ram eng (ramRead ram eng .w+1#32) .w

theorem released (ram : Word → BitVec 8) (eng : Word) (hb : ramRead ram eng .w = 0xffffffff#32) :
    ramRead (result ram eng) eng .w = 0#32 := by
  unfold result
  rw [ramRead_ramWrite_w,hb]
  decide +kernel

theorem frame (ram : Word → BitVec 8) (eng x : Word)
    (hx : ∀ i : Fin 4, x ≠ eng+BitVec.ofNat 32 i.val) : result ram eng x = ram x := by
  apply ramWrite_w_other
  intro k hk
  exact hx ⟨k,hk⟩

theorem snapshot (ram : Word → BitVec 8) (eng : Word) (s : Spec.Snapshot)
    (hs : Encoding.SnapshotAt ram (eng+4#32) s) : Encoding.SnapshotAt (result ram eng) (eng+4#32) s := by
  intro i
  rw [frame ram eng _ (by
    intro j he
    simp only [BitVec.add_assoc,BitVec.add_right_inj] at he
    have hn := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat] at hn
    have hi := i.isLt
    have hj := j.isLt
    omega)]
  exact hs i

/-- On refusal the real handler releases its mutable borrow without applying. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000648) (he : Memory.Block B (c.get 23) 14)
    (ha : (c.get 23).toNat % 4 = 0) :
    ∃ d, DetSteps B img 3 ⟨c,ram⟩ ⟨d,result ram (c.get 23)⟩ ∧ d.pc = 0x80000652 ∧
      d.get 2 = c.get 2 ∧ d.get 20 = c.get 20 ∧ d.get 23 = c.get 23 ∧ d.sameCsr c := by
  let eng := c.get 23
  let v := ramRead ram eng .w
  let c1 := c.wr 11 v 0x8000064c
  let c2 := c1.wr 11 (v+1#32) 0x8000064e
  let d := c2.goto 0x80000652
  have hr : B.inRam eng 4 = true := by
    simpa using Memory.block_access (B := B) (p := eng) (n := 14) (off := 0) (width := 4) he (by decide) (by decide)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact u2147485256) fun o => ?_
    rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) (a := eng) o ha hr,hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000064c : Word).getLsbD 0 = false;decide) u2147485260 fun o => ?_
    have hv : c1.get 11 = v := by simp [c1,Core.wr_get]
    rw [exec_opimm,hv]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨d,result ram eng⟩ := by
    refine detStep_of (by change (0x8000064e : Word).getLsbD 0 = false;decide) u2147485262 fun o => ?_
    have hs : c2.get 23 = eng := by simp [c2,c1,eng,Core.wr_get_ne]
    have hv : c2.get 11 = v+1#32 := by simp [c2,Core.wr_get]
    rw [exec_store,hs,hv,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .w) (a := eng) (v := v+1#32) o ha hr]
    rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,?_,?_,by rfl⟩
  all_goals simp [d,c2,c1,Core.wr_get_ne]
end E5R.Thermostat.ReleaseBorrow
