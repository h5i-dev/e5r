import Projects.thermostat.ShellCall
import Projects.thermostat.BufferRegs
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ShellCall
open E5R E5R.Thermostat

theorem contract_io (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram p admin s cmd) :
    ∃ n d r, n ≤ 95 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x8000063a ∧ d.get 2 = c.get 2 ∧ d.get 20 = c.get 23+4#32 ∧ d.sameCsr c ∧
      Outcome.At r (p+104#32) (Spec.transition admin s cmd) ∧
      Encoding.SnapshotAt r (c.get 23+4#32) s ∧
      (∀ x, (∀ i : Fin 124, x ≠ p+BitVec.ofNat 32 i.val) → r x = ram x) ∧ Upper.Frame c d ∧ BufferRegs.Frame c d := by
  obtain ⟨hsp,hbase,hout,hactor,hstate,hcmd,hsaved⟩ := pointers c p h.sp
  have hsaveRam : B.inRam (Wrapper.saved (ShellEntry.setup c)) 4 = true := by
    rw [hsaved]
    exact Memory.block_access (B := B) (p := p) (n := 128) (off := 76) (width := 4) h.arena (by decide) (by decide)
  have hsaveAlign : (Wrapper.saved (ShellEntry.setup c)).toNat % 4 = 0 := by
    rw [hsaved];exact Memory.word_aligned p 19 h.align
  have hsetup := ShellEntry.setup_contract B c ram h.pc
  have hwrap := Wrapper.enter B (ShellEntry.setup c) ram rfl hsaveRam hsaveAlign
  obtain ⟨nk,m,hnk,hkr,hpost⟩ := Kernel.transition_contract B (entry c) (savedRam c ram) admin s cmd
    (establishes_pre B c ram p admin s cmd h)
  have hret : m.core.pc = 0x80001e32 := by
    have hh := hpost.pc
    change m.core.pc = (Wrapper.inner (ShellEntry.setup c)).get 1 &&& ~~~1 at hh
    rw [Wrapper.inner_ra] at hh
    exact hh
  have hmsp : m.core.get 2 = p+64#32 := hpost.sp.trans hsp
  have hword : ramRead m.ram (p+76#32) .w = 0x8000063a := by
    calc
      ramRead m.ram (p+76#32) .w = ramRead (savedRam c ram) (p+76#32) .w := by
        apply ramRead_w_congr
        intro k hk
        apply hpost.frame
        · intro i
          rw [hout]
          have hi := i.isLt
          simpa only [BitVec.ofNat_add,BitVec.add_assoc] using offset_ne p (76+k) (104+i.val) (by omega) (by omega) (by omega)
        · intro i
          rw [hbase]
          have hi := i.isLt
          simpa only [BitVec.ofNat_add,BitVec.add_assoc] using offset_ne p (76+k) i.val (by omega) (by omega) (by omega)
      _ = 0x8000063a := by
        unfold savedRam Wrapper.save
        rw [hsaved,ramRead_ramWrite_w]
        simp [ShellEntry.setup,Core.wr_get]
  have hsuffixAddr : m.core.get 2+12#32 = p+76#32 := by rw [hmsp];simp [BitVec.add_assoc]
  obtain ⟨d,hsRun,hsPc,hsSp,hsRegs,hsCsr⟩ := Wrapper.suffix B m.core m.ram hret
    (by rw [hsuffixAddr];simpa only [hsaved] using hsaveRam)
    (by rw [hsuffixAddr];simpa only [hsaved] using hsaveAlign)
    (by rw [hsuffixAddr];exact hword)
  have hframe : ∀ x, (∀ i : Fin 124, x ≠ p+BitVec.ofNat 32 i.val) → m.ram x = ram x := by
    intro x hx
    rw [hpost.frame x (by
      intro i
      rw [hout]
      have hi := i.isLt
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨104+i.val,by omega⟩) (by
      intro i
      rw [hbase]
      exact hx ⟨i.val,by have := i.isLt;omega⟩)]
    exact saved_frame c ram p x h.sp (fun i => hx ⟨76+i.val,by have := i.isLt;omega⟩)
  refine ⟨7+4+nk+3,d,m.ram,by omega,((hsetup.trans hwrap).trans hkr).trans hsRun,hsPc,?_,?_,?_,?_,?_,hframe,?_,?_⟩
  · rw [hsSp,hmsp,h.sp];simp [BitVec.add_assoc]
  · have hh := hpost.saved ⟨5,by decide⟩
    change m.core.get 20 = (entry c).get 20 at hh
    rw [hsRegs 20 (by decide) (by decide),hh]
    change (Wrapper.inner (ShellEntry.setup c)).get 20 = c.get 23+4#32
    rw [Wrapper.inner_reg (ShellEntry.setup c) 20 (by decide) (by decide)]
    simp [ShellEntry.setup,Core.wr_get]
  · exact hsCsr.trans (hpost.csr.trans (by rfl))
  · simpa only [hout] using hpost.outcome
  · intro i
    rw [hframe _ (fun j => h.stateSep i ⟨j.val,by have := j.isLt;omega⟩)]
    exact h.stateAt i
  · intro r hr
    exact (hsRegs r (Upper.ne_low r hr 1 (by decide)) (Upper.ne_low r hr 2 (by decide))).trans
      ((hpost.upper r hr).trans ((Wrapper.inner_upper (ShellEntry.setup c) r hr).trans (ShellEntry.setup_upper c r hr)))

  · constructor
    · have hh := hpost.saved ⟨3,by decide⟩
      change m.core.get 18 = (entry c).get 18 at hh
      rw [hsRegs 18 (by decide) (by decide),hh]
      change (Wrapper.inner (ShellEntry.setup c)).get 18 = c.get 18
      rw [Wrapper.inner_reg (ShellEntry.setup c) 18 (by decide) (by decide)]
      simp [ShellEntry.setup,Core.wr_get_ne]
    · have hh := hpost.saved ⟨4,by decide⟩
      change m.core.get 19 = (entry c).get 19 at hh
      rw [hsRegs 19 (by decide) (by decide),hh]
      change (Wrapper.inner (ShellEntry.setup c)).get 19 = c.get 19
      rw [Wrapper.inner_reg (ShellEntry.setup c) 19 (by decide) (by decide)]
      simp [ShellEntry.setup,Core.wr_get_ne]
    · have hh := hpost.saved ⟨1,by decide⟩
      change m.core.get 8 = (entry c).get 8 at hh
      rw [hsRegs 8 (by decide) (by decide),hh]
      change (Wrapper.inner (ShellEntry.setup c)).get 8 = c.get 8
      rw [Wrapper.inner_reg (ShellEntry.setup c) 8 (by decide) (by decide)]
      simp [ShellEntry.setup,Core.wr_get_ne]
    · have hh := hpost.saved ⟨2,by decide⟩
      change m.core.get 9 = (entry c).get 9 at hh
      rw [hsRegs 9 (by decide) (by decide),hh]
      change (Wrapper.inner (ShellEntry.setup c)).get 9 = c.get 9
      rw [Wrapper.inner_reg (ShellEntry.setup c) 9 (by decide) (by decide)]
      simp [ShellEntry.setup,Core.wr_get_ne]
    · exact (hsRegs 22 (by decide) (by decide)).trans
        ((hpost.upper 22 (by decide)).trans
          ((Wrapper.inner_upper (ShellEntry.setup c) 22 (by decide)).trans (ShellEntry.setup_upper c 22 (by decide))))
end E5R.Thermostat.ShellCall
