import Projects.thermostat.RelayPatch
import Projects.thermostat.RelayWork
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RelayBody
open E5R E5R.Thermostat

theorem patch_frame (ram : Word → BitVec 8) (src sp x : Word) (idx : BitVec 8) (on : Bool)
    (hi : idx.toNat < 4) (hx : ∀ i : Fin 36, x ≠ sp+BitVec.ofNat 32 i.val) :
    RelayPatch.result ram src sp idx on x = ram x := by
  have hp : x ≠ (sp+24#32)+BitVec.ofNat 32 idx.toNat := by
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨24+idx.toNat,by omega⟩
  unfold RelayPatch.result
  rw [ramPut_ne _ hp]
  apply Scratch.copy_frame
  intro i
  have hi' := i.isLt
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨24+i.val,by omega⟩

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (idx : BitVec 8) (on : Bool)
    (hp : c.pc = 0x800001be) (hidx : c.get 11 = BitVec.ofNat 32 idx.toNat) (hi : idx.toNat < 4)
    (hs : Encoding.SnapshotAt ram (c.get 12) s) (hstate : Memory.Block B (c.get 12) 10)
    (haState : (c.get 12).toNat % 2 = 0) (hstack : Memory.Block B (c.get 2) 64)
    (haStack : (c.get 2).toNat % 4 = 0) (honRam : B.inRam (c.get 13+2#32) 1 = true)
    (hon : ram (c.get 13+2#32) = Encoding.boolByte on)
    (hout : Memory.Block B (c.get 10) 20) (haOut : (c.get 10).toNat % 2 = 0)
    (hsep : ∀ i : Fin 20, ∀ j : Fin 64, c.get 10+BitVec.ofNat 32 i.val ≠ c.get 2+BitVec.ofNat 32 j.val) :
    ∃ d r, DetSteps B img 52 ⟨c,ram⟩ ⟨d,r⟩ ∧ d.pc = 0x800001ac ∧
      d.get 2 = c.get 2 ∧ d.sameCsr c ∧
      Outcome.At r (c.get 10) (.ok ⟨some (Scratch.patched s idx on),Scratch.patched s idx on⟩) ∧
      (∀ x, (∀ i : Fin 20, x ≠ c.get 10+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 36, x ≠ c.get 2+BitVec.ofNat 32 i.val) → r x = ram x) ∧ Upper.Frame c d := by
  obtain ⟨cp,hpRun,hpPc,hpSp,hpOut,hpCsr,hpSnap,hpUpper⟩ := RelayPatch.contract_full B c ram s idx on hp hidx hi hs hstate haState hstack haStack honRam hon
  let rp := RelayPatch.result ram (c.get 12) (c.get 2) idx on
  obtain ⟨cw,hwRun,hwPc,hwSp,hwOut,hwCsr,hwUpper⟩ := RelayWork.contract_full B cp rp hpPc
    (by simpa only [hpSp] using hstack) (by simpa only [hpSp] using haStack)
    (by simpa only [hpOut] using hout) (by simpa only [hpOut] using haOut)
  rw [hpSp,hpOut] at hwRun
  let rwk := RelayWork.result rp (c.get 2) (c.get 10)
  have hwSp' := hwSp.trans hpSp
  have hwOut' := hwOut.trans hpOut
  obtain ⟨co,hoRun,hoPc,hoSp,hoOut,hoCsr,hoUpper⟩ := RelayOutput.contract_full B cw rwk hwPc
    (by simpa only [hwSp'] using hstack) (by simpa only [hwSp'] using haStack)
    (by simpa only [hwOut'] using hout) (by simpa only [hwOut'] using haOut)
  rw [hwSp',hwOut'] at hoRun
  let ro := RelayOutput.result rwk rwk (c.get 2+4#32) (c.get 10)
  obtain ⟨hfirst,hsecond,htail⟩ := RelayWork.ready rp (c.get 2) (c.get 10) (Scratch.patched s idx on) hpSnap hsep
  refine ⟨co,ro,(hpRun.trans hwRun).trans hoRun,hoPc,hoSp.trans hwSp',hoCsr.trans (hwCsr.trans hpCsr),?_,?_,?_⟩
  · exact RelayOutput.source rwk (c.get 2+4#32) (c.get 10) (Scratch.patched s idx on) hfirst hsecond htail
  · intro x hx hsx
    exact (RelayOutput.frame rwk rwk (c.get 2+4#32) (c.get 10) x (fun i => hx ⟨i.val,by have := i.isLt;omega⟩)).trans
      ((RelayWork.frame rp (c.get 2) (c.get 10) x hx hsx).trans (patch_frame ram (c.get 12) (c.get 2) x idx on hi hsx))
  · exact (Upper.trans (Upper.trans hpUpper hwUpper) hoUpper)
end E5R.Thermostat.RelayBody
