import Projects.thermostat.Stack
import Projects.thermostat.Dispatch
import Projects.thermostat.ReadBody

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.TransitionRead
open E5R E5R.Thermostat

/-- A caller-owned block is disjoint from the seven saved register words. -/
def Separate (c : Core) (p : Word) (n : Nat) : Prop :=
  ∀ k : Fin n, ∀ i : Fin 7, ∀ j : Fin 4,
    p + BitVec.ofNat 32 k.val ≠ Stack.base c + BitVec.ofNat 32 (60-4*i.val) + BitVec.ofNat 32 j.val

theorem saved_snapshot (c : Core) (ram : Word → BitVec 8) (p : Word) (s : Spec.Snapshot)
    (hs : Encoding.SnapshotAt ram p s) (hsep : Separate c p 10) :
    Encoding.SnapshotAt (Stack.save c ram) p s := by
  intro k
  rw [Stack.save_frame c ram _ (hsep k)]
  exact hs k

/-- Full entry-to-return theorem for Read, with arbitrary register/CSR contents,
    arbitrary RAM, and arbitrary separated input/output/stack addresses. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (hp : c.pc = 0x80000052) (hstack : Stack.Accessible B (Stack.base c))
    (hcmdRam : B.inRam (c.get 13) 1 = true) (hcmd : ram (c.get 13) = 4#8)
    (hsRam : Apply.HalfBlock B (c.get 12)) (hoRam : Apply.HalfBlock B (c.get 10+10#32))
    (htagRam : B.inRam (c.get 10) 1 = true)
    (hs : Encoding.SnapshotAt ram (c.get 12) s)
    (hsepCmd : Separate c (c.get 13) 1) (hsepState : Separate c (c.get 12) 10)
    (hsepOut : Separate c (c.get 10) 20) :
    ∃ n d ram', n ≤ 37 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram'⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 2 = c.get 2 ∧
      Encoding.OptionAt ram' (c.get 10) none ∧
      Encoding.SnapshotAt ram' (c.get 10+10#32) s ∧
      (∀ i : Fin 7, d.get (Stack.reg i) = c.get (Stack.reg i)) ∧
      d.sameCsr c ∧
      (∀ x, (∀ k : Fin 20, x ≠ c.get 10 + BitVec.ofNat 32 k.val) →
        (∀ i : Fin 7, ∀ j : Fin 4,
          x ≠ Stack.base c + BitVec.ofNat 32 (60-4*i.val) + BitVec.ofNat 32 j.val) → ram' x = ram x) := by
  obtain ⟨cp,hpRun,hpPc,hpSp,hpRegs,hpCsr⟩ := Stack.prologue B c ram hp hstack
  have hcTag : Stack.save c ram (c.get 13) = 4#8 := by
    rw [Stack.save_frame c ram _ (by
      intro i j
      simpa using hsepCmd ⟨0,by decide⟩ i j)]
    exact hcmd
  have h13 : cp.get 13 = c.get 13 := hpRegs 13 (by decide)
  obtain ⟨nd,cd,hdBound,hdRun,hdPc,hdRegs,hdCsr⟩ := Dispatch.contract B cp (Stack.save c ram) ⟨4,by decide⟩ hpPc
    (by simpa [h13] using hcmdRam) (by simpa [h13] using hcTag)
  have hdArgs (r : Reg) (h2 : r ≠ 2) (h14 : r ≠ 14) (h15 : r ≠ 15) : cd.get r = c.get r :=
    (hdRegs r h14 h15).trans (hpRegs r h2)
  have hdSp : cd.get 2 = Stack.base c := (hdRegs 2 (by decide) (by decide)).trans hpSp
  obtain ⟨cb,hbRun,hbPc,hbRegs,hbCsr⟩ := ReadBody.contract B cd (Stack.save c ram) (c.get 12) (c.get 10)
    (by simpa [Dispatch.entry] using hdPc)
    (hdArgs 12 (by decide) (by decide) (by decide))
    (hdArgs 10 (by decide) (by decide) (by decide)) hsRam hoRam htagRam
  let outRam := ReadBody.result (Stack.save c ram) (c.get 12) (c.get 10)
  have hbSp : cb.get 2 = Stack.base c :=
    (hbRegs 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdSp
  have hSaved : ∀ i : Fin 7,
      ramRead outRam (Stack.base c + BitVec.ofNat 32 (60-4*i.val)) .w = c.get (Stack.reg i) := by
    intro i
    calc
      ramRead outRam (Stack.base c + BitVec.ofNat 32 (60-4*i.val)) .w =
          ramRead (Stack.save c ram) (Stack.base c + BitVec.ofNat 32 (60-4*i.val)) .w := by
        apply ramRead_w_congr
        intro k hk
        apply ReadBody.frame
        intro l
        exact Ne.symm (hsepOut l i ⟨k,hk⟩)
      _ = c.get (Stack.reg i) := Stack.saved_word c ram i
  obtain ⟨d,heRun,hePc,heSp,heSaved,heRegs,heCsr⟩ := Stack.epilogue B c cb outRam hbPc hbSp hstack hSaved
  refine ⟨8+nd+13+9,d,outRam,by omega,?_,hePc,heSp,?_,?_,heSaved,?_,?_⟩
  · exact ((hpRun.trans hdRun).trans hbRun).trans heRun
  · exact ReadBody.none _ _ _
  · exact ReadBody.reply _ _ _ s (saved_snapshot c ram (c.get 12) s hs hsepState)
  · exact heCsr.trans (hbCsr.trans (hdCsr.trans hpCsr))
  · intro x hxOut hxStack
    exact (ReadBody.frame (Stack.save c ram) (c.get 12) (c.get 10) x hxOut).trans
      (Stack.save_frame c ram x hxStack)

end E5R.Thermostat.TransitionRead
