-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ApplyCall
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ApplyQuiet
import Projects.thermostat.ApplyWrapperQuiet
import Projects.thermostat.ProofQuiet
import Projects.thermostat.ApplyCallSetupQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.ApplyCall
theorem setup_contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x800006da) : Quiet.Steps B img 5 ⟨c,ram⟩ ⟨setup c,ram⟩ := by
  exact ApplyCallSetupQuiet.contract B c ram hp

end E5R.Thermostat.ApplyCall
namespace E5R.Thermostat.ApplyCall
theorem contract_tight_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (s : Spec.Snapshot) (w : Option Spec.Snapshot) (h : Pre B c ram p s w) :
    ∃ n d r, n ≤ 27 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ d.pc = 0x800006ea ∧
      d.get 2 = c.get 2 ∧ d.get 20 = c.get 20 ∧ d.get 23 = c.get 23 ∧ d.sameCsr c ∧
      Encoding.SnapshotAt r (p+104#32) (Spec.apply s w) ∧
      (∀ x, (∀ i : Fin 124, x ≠ p+BitVec.ofNat 32 i.val) → r x = ram x) ∧
      (∀ rr : Reg, rr ≠ 1 → rr ≠ 2 → rr ≠ 10 → rr ≠ 11 → rr ≠ 12 → rr ≠ 13 → rr ≠ 14 → rr ≠ 15 → d.get rr = c.get rr) ∧
      ramRead r (p+84#32) .w = ramRead ram (p+84#32) .w := by
  obtain ⟨hsp,hout,hstate,hwrite,hsaved⟩ := pointers c p h.sp
  let rs := savedRam c ram
  have hrSave : B.inRam (ApplyWrapper.saved (setup c)) 4 = true := by
    rw [hsaved]
    exact Memory.block_access (B := B) (p := p) (n := 128) (off := 76) (width := 4) h.arena (by decide) (by decide)
  have haSave : (ApplyWrapper.saved (setup c)).toNat % 4 = 0 := by
    rw [hsaved];exact Memory.word_aligned p 19 h.align
  have hstateAt : Encoding.SnapshotAt rs ((entry c).get 11) s := by
    rw [hstate]
    intro i
    change savedRam c ram (c.get 20+BitVec.ofNat 32 i.val) = Encoding.snapshotByte s i
    rw [saved_frame c ram p _ h.sp (fun j => h.stateSep i ⟨76+j.val,by have := j.isLt;omega⟩)]
    exact h.stateAt i
  have hwriteFrame : ∀ i : Fin 10, rs ((p+94#32)+BitVec.ofNat 32 i.val) = ram ((p+94#32)+BitVec.ofNat 32 i.val) := by
    intro i
    apply saved_frame c ram p _ h.sp
    intro j
    have hi := i.isLt
    have hj := j.isLt
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using ShellCall.offset_ne p (94+i.val) (76+j.val) (by omega) (by omega) (by omega)
  have hwriteAt : Encoding.OptionAt rs ((entry c).get 12) w := by
    rw [hwrite]
    cases w with
    | none =>
      have hf := hwriteFrame ⟨0,by decide⟩
      have hf' : rs (p+94#32) = ram (p+94#32) := by simpa using hf
      exact hf'.trans h.writeAt
    | some sw => intro i;exact (hwriteFrame i).trans (h.writeAt i)
  have htag : B.inRam ((entry c).get 12) 1 = true := by
    rw [hwrite]
    exact Memory.block_access (B := B) (p := p) (n := 128) (off := 94) (width := 1) h.arena (by decide) (by decide)
  have hstateHalf : Apply.HalfBlock B ((entry c).get 11) := by
    rw [hstate];exact Memory.half_block h.stateRam h.stateAlign
  have hwriteHalf : Apply.HalfBlock B ((entry c).get 12) := by
    rw [hwrite]
    exact Memory.half_block (Memory.sub_block (B := B) (p := p) (n := 128) (off := 94) (m := 10) h.arena (by decide) (by decide))
      (Memory.half_aligned p 47 (by have := h.align;omega))
  have houtHalf : Apply.HalfBlock B ((entry c).get 10) := by
    rw [hout]
    exact Memory.half_block (Memory.sub_block (B := B) (p := p) (n := 128) (off := 104) (m := 10) h.arena (by decide) (by decide))
      (Memory.half_aligned p 52 (by have := h.align;omega))
  have hsetup := E5R.Thermostat.ApplyCall.setup_contract_quiet B c ram h.pc
  have henter := E5R.Thermostat.ApplyWrapper.enter_quiet B (setup c) ram rfl hrSave haSave
  obtain ⟨na,ca,r,hn,haRun,haPc,haOut,haState,haFrame,haRegs,haCsr⟩ := E5R.Thermostat.Apply.source_contract_quiet B (entry c) rs s w rfl htag hstateHalf hwriteHalf houtHalf hstateAt hwriteAt
  have hpc : ca.pc = 0x80001e44 := by
    have hh := haPc
    change ca.pc = (ApplyWrapper.inner (setup c)).get 1 &&& ~~~1 at hh
    rw [ApplyWrapper.inner_ra] at hh
    exact hh
  have haSp : ca.get 2 = p+64#32 := (haRegs 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsp
  have haddr : ca.get 2+12#32 = p+76#32 := by rw [haSp];simp [BitVec.add_assoc]
  have hword : ramRead r (p+76#32) .w = 0x800006ea := by
    calc
      ramRead r (p+76#32) .w = ramRead rs (p+76#32) .w := by
        apply ramRead_w_congr
        intro k hk
        apply haFrame
        intro i
        rw [hout]
        have hi := i.isLt
        simpa only [BitVec.ofNat_add,BitVec.add_assoc] using ShellCall.offset_ne p (76+k) (104+i.val) (by omega) (by omega) (by omega)
      _ = 0x800006ea := by
        unfold rs savedRam ApplyWrapper.save
        rw [hsaved,ramRead_ramWrite_w]
        simp [setup,Core.wr_get]
  obtain ⟨d,hsRun,hsPc,hsSp,hsRegs,hsCsr⟩ := E5R.Thermostat.ApplyWrapper.suffix_quiet B ca r hpc
    (by rw [haddr];simpa only [hsaved] using hrSave)
    (by rw [haddr];simpa only [hsaved] using haSave)
    (by rw [haddr];exact hword)
  have hr20 : ca.get 20 = c.get 20 := by
    rw [haRegs 20 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [entry,ApplyWrapper.inner,setup,Core.wr_get_ne]
  have hr23 : ca.get 23 = c.get 23 := by
    rw [haRegs 23 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [entry,ApplyWrapper.inner,setup,Core.wr_get_ne]
  refine ⟨5+4+na+3,d,r,by omega,((hsetup.trans henter).trans haRun).trans hsRun,hsPc,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hsSp,haSp,h.sp];simp [BitVec.add_assoc]
  · exact (hsRegs 20 (by decide) (by decide)).trans hr20
  · exact (hsRegs 23 (by decide) (by decide)).trans hr23
  · exact hsCsr.trans (haCsr.trans (by rfl))
  · simpa only [hout] using haState
  · intro x hx
    rw [haFrame x (by
      intro i
      rw [hout]
      have hi := i.isLt
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨104+i.val,by omega⟩)]
    exact saved_frame c ram p x h.sp (fun i => hx ⟨76+i.val,by have := i.isLt;omega⟩)
  · intro rr h1 h2 h10 h11 h12 h13 h14 h15
    have hi : (entry c).get rr = c.get rr := by
      change (ApplyWrapper.inner (setup c)).get rr = c.get rr
      rw [ApplyWrapper.inner_reg (setup c) rr h1 h2]
      exact setup_reg c rr h1 h10 h11 h12
    exact (hsRegs rr h1 h2).trans ((haRegs rr h11 h12 h13 h14 h15).trans hi)
  · apply ramRead_w_congr
    intro k hk
    rw [haFrame _ (by
      intro i
      rw [hout]
      have hi := i.isLt
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using ShellCall.offset_ne p (84+k) (104+i.val) (by omega) (by omega) (by omega))]
    apply saved_frame c ram p _ h.sp
    intro i
    have hi := i.isLt
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using ShellCall.offset_ne p (84+k) (76+i.val) (by omega) (by omega) (by omega)

end E5R.Thermostat.ApplyCall
