import Projects.thermostat.TransitionRead
import Projects.thermostat.Outcome
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.Unauthorized
open E5R E5R.Thermostat

def tag (kind : Fin 3) : Fin 5 := match kind.val with
 | 0 => ⟨0,by decide⟩ | 1 => ⟨2,by decide⟩ | _ => ⟨3,by decide⟩
def entry (kind : Fin 3) : Word := match kind.val with
 | 0 => 0x800000d6 | 1 => 0x800000fe | _ => 0x80000078

theorem dispatch_entry (kind : Fin 3) : Dispatch.entry (tag kind) = entry kind := by
  have hi := kind.isLt
  have hc : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 := by omega
  rcases hc with h|h|h <;> simp [Dispatch.entry,tag,entry,h]
  all_goals decide +kernel

theorem enter (B : Board) (c : Core) (ram : Word → BitVec 8) (kind : Fin 3)
    (hp : c.pc = entry kind) (hr : B.inRam (c.get 11) 1 = true) (ha : ram (c.get 11) = 0#8) :
    ∃ d, DetSteps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x8000011c ∧
      (∀ r : Reg, r ≠ 11 → d.get r = c.get r) ∧ d.sameCsr c := by
  have hi := kind.isLt
  have hc : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 := by omega
  rcases hc with hkind|hkind|hkind
  · have hp' : c.pc = 0x800000d6 := by simpa [entry,hkind] using hp
    let c1 := c.wr 11 0#32 0x800000da
    let d := c1.goto 0x8000011c
    have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine detStep_of (by rw [hp'];decide) (by rw [hp'];exact d2147483862) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ha,hp']
      rfl
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
      refine detStep_of (by change (0x800000da : Word).getLsbD 0 = false;decide) d2147483866 fun o => ?_
      have hv : c1.get 11 = 0#32 := by simp [c1,Core.wr_get]
      rw [exec_branch,hv,Core.get_zero,ite_eq_left (by decide +kernel),jump_ok _ _ (by change (0x8000011c : Word).getLsbD 0 = false;decide)]
      rfl
    refine ⟨d,.step s0 (.single s1),rfl,?_,?_⟩
    · intro r h; simp [d,c1,Core.wr_get_ne,h]
    · exact (Core.sameCsr_goto _ _).trans (Core.sameCsr_wr _ _ _ _)
  · have hp' : c.pc = 0x800000fe := by simpa [entry,hkind] using hp
    let c1 := c.wr 11 0#32 0x80000102
    let d := c1.goto 0x8000011c
    have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine detStep_of (by rw [hp'];decide) (by rw [hp'];exact d2147483902) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ha,hp']
      rfl
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
      refine detStep_of (by change (0x80000102 : Word).getLsbD 0 = false;decide) d2147483906 fun o => ?_
      have hv : c1.get 11 = 0#32 := by simp [c1,Core.wr_get]
      rw [exec_branch,hv,Core.get_zero,ite_eq_left (by decide +kernel),jump_ok _ _ (by change (0x8000011c : Word).getLsbD 0 = false;decide)]
      rfl
    refine ⟨d,.step s0 (.single s1),rfl,?_,?_⟩
    · intro r h; simp [d,c1,Core.wr_get_ne,h]
    · exact (Core.sameCsr_goto _ _).trans (Core.sameCsr_wr _ _ _ _)
  · have hp' : c.pc = 0x80000078 := by simpa [entry,hkind] using hp
    let c1 := c.wr 11 0#32 0x8000007c
    let d := c1.goto 0x8000011c
    have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine detStep_of (by rw [hp'];decide) (by rw [hp'];exact d2147483768) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ha,hp']
      rfl
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
      refine detStep_of (by change (0x8000007c : Word).getLsbD 0 = false;decide) d2147483772 fun o => ?_
      have hv : c1.get 11 = 0#32 := by simp [c1,Core.wr_get]
      rw [exec_branch,hv,Core.get_zero,ite_eq_left (by decide +kernel),jump_ok _ _ (by change (0x8000011c : Word).getLsbD 0 = false;decide)]
      rfl
    refine ⟨d,.step s0 (.single s1),rfl,?_,?_⟩
    · intro r h; simp [d,c1,Core.wr_get_ne,h]
    · exact (Core.sameCsr_goto _ _).trans (Core.sameCsr_wr _ _ _ _)

/-- Full entry-to-return proof of all three unauthorized command arms.
    The kernel does not read the command payload or the snapshot on these paths. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (kind : Fin 3)
    (hp : c.pc = 0x80000052) (hstack : Stack.Accessible B (Stack.base c))
    (hcmdRam : B.inRam (c.get 13) 1 = true) (hcmd : ram (c.get 13) = BitVec.ofNat 8 (tag kind).val)
    (haRam : B.inRam (c.get 11) 1 = true) (ha : ram (c.get 11) = 0#8)
    (hout0 : B.inRam (c.get 10) 1 = true) (hout10 : B.inRam (c.get 10+10#32) 1 = true)
    (hsepCmd : TransitionRead.Separate c (c.get 13) 1)
    (hsepActor : TransitionRead.Separate c (c.get 11) 1)
    (hsepOut : TransitionRead.Separate c (c.get 10) 20) :
    ∃ n d ram', n ≤ 30 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram'⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 2 = c.get 2 ∧
      Outcome.At ram' (c.get 10) (.error .forbidden) ∧
      (∀ i : Fin 7, d.get (Stack.reg i) = c.get (Stack.reg i)) ∧ d.sameCsr c ∧
      (∀ x, (∀ k : Fin 20, x ≠ c.get 10 + BitVec.ofNat 32 k.val) →
        (∀ i : Fin 7, ∀ j : Fin 4,
          x ≠ Stack.base c + BitVec.ofNat 32 (60-4*i.val) + BitVec.ofNat 32 j.val) → ram' x = ram x) := by
  obtain ⟨cp,hpRun,hpPc,hpSp,hpRegs,hpCsr⟩ := Stack.prologue B c ram hp hstack
  have hcTag : Stack.save c ram (c.get 13) = BitVec.ofNat 8 (tag kind).val := by
    rw [Stack.save_frame c ram _ (by intro i j;simpa using hsepCmd ⟨0,by decide⟩ i j)]
    exact hcmd
  have haTag : Stack.save c ram (c.get 11) = 0#8 := by
    rw [Stack.save_frame c ram _ (by intro i j;simpa using hsepActor ⟨0,by decide⟩ i j)]
    exact ha
  have h13 : cp.get 13 = c.get 13 := hpRegs 13 (by decide)
  obtain ⟨nd,cd,hdBound,hdRun,hdPc,hdRegs,hdCsr⟩ := Dispatch.contract B cp (Stack.save c ram) (tag kind) hpPc
    (by simpa [h13] using hcmdRam) (by simpa [h13] using hcTag)
  have hdArgs (r : Reg) (h2 : r ≠ 2) (h14 : r ≠ 14) (h15 : r ≠ 15) : cd.get r = c.get r :=
    (hdRegs r h14 h15).trans (hpRegs r h2)
  have hdSp : cd.get 2 = Stack.base c := (hdRegs 2 (by decide) (by decide)).trans hpSp
  have hdActor : cd.get 11 = c.get 11 := hdArgs 11 (by decide) (by decide) (by decide)
  obtain ⟨ce,heRun,hePc,heRegs,heCsr⟩ := enter B cd (Stack.save c ram) kind
    (by simpa [dispatch_entry] using hdPc) (by simpa [hdActor] using haRam) (by simpa [hdActor] using haTag)
  have heOut : ce.get 10 = c.get 10 := (heRegs 10 (by decide)).trans (hdArgs 10 (by decide) (by decide) (by decide))
  have heSp : ce.get 2 = Stack.base c := (heRegs 2 (by decide)).trans hdSp
  obtain ⟨cb,hbRun,hbPc,hbSp,hbCsr⟩ := Errors.forbidden B ce (Stack.save c ram) hePc
    (by simpa [heOut] using hout0) (by simpa [heOut] using hout10)
  rw [heOut] at hbRun
  let outRam := Errors.result (Stack.save c ram) (c.get 10) .forbidden
  have hSaved : ∀ i : Fin 7,
      ramRead outRam (Stack.base c + BitVec.ofNat 32 (60-4*i.val)) .w = c.get (Stack.reg i) := by
    intro i
    calc
      ramRead outRam (Stack.base c + BitVec.ofNat 32 (60-4*i.val)) .w =
          ramRead (Stack.save c ram) (Stack.base c + BitVec.ofNat 32 (60-4*i.val)) .w := by
        apply ramRead_w_congr
        intro k hk
        apply Errors.result_frame
        · simpa using Ne.symm (hsepOut ⟨0,by decide⟩ i ⟨k,hk⟩)
        · simpa using Ne.symm (hsepOut ⟨10,by decide⟩ i ⟨k,hk⟩)
      _ = c.get (Stack.reg i) := Stack.saved_word c ram i
  obtain ⟨d,hfRun,hfPc,hfSp,hfSaved,hfRegs,hfCsr⟩ := Stack.epilogue B c cb outRam hbPc (hbSp.trans heSp) hstack hSaved
  refine ⟨8+nd+2+4+9,d,outRam,by omega,?_,hfPc,hfSp,?_,hfSaved,?_,?_⟩
  · exact (((hpRun.trans hdRun).trans heRun).trans hbRun).trans hfRun
  · exact Outcome.error _ _ _
  · exact hfCsr.trans (hbCsr.trans (heCsr.trans (hdCsr.trans hpCsr)))
  · intro x hxOut hxStack
    have hx0 : x ≠ c.get 10 := by simpa using hxOut ⟨0,by decide⟩
    have hx10 : x ≠ c.get 10+10#32 := by simpa using hxOut ⟨10,by decide⟩
    exact (Errors.result_frame (Stack.save c ram) (c.get 10) x .forbidden hx0 hx10).trans
      (Stack.save_frame c ram x hxStack)

end E5R.Thermostat.Unauthorized
