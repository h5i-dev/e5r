import Projects.thermostat.QuietExec
namespace E5R.Thermostat.QuietLoad
open E5R E5R.Thermostat
open QuietEffect

theorem extend_zero (w : Width) (signed : Bool) : extend w signed (devVal w 0#32)=0#32 := by
  cases w <;> cases signed <;> decide +kernel

theorem extend_one (w : Width) (signed : Bool) : extend w signed (devVal w 1#32)=1#32 := by
  cases w <;> cases signed <;> decide +kernel

/-- A used normal load cannot both accept arbitrary device input and have the
    same successful result for every oracle. Discarded loads are excluded. -/
theorem source (B : Board) (img : List Segment) (c d : Core) (ram after : Word → BitVec 8)
    (w : Width) (signed : Bool) (rd : Reg) (a next : Word) (hrd : rd.val≠0)
    (h : ∀ o, interp B img o (.load w a false (fun v => .done (c.wr rd (extend w signed v) next))) ram 0 []=.ok d after []) :
    B.inRam a w.bytes=true ∨ ∃ v, romRead? img a.toNat w.bytes false=some v := by
  by_cases hin : B.inRam a w.bytes=true
  · exact Or.inl hin
  · have hout : B.inRam a w.bytes=false := Bool.eq_false_iff.mpr hin
    cases rom : romRead? img a.toNat w.bytes false with
    | some value => exact Or.inr ⟨value,rfl⟩
    | none =>
      exfalso
      have h0 := h (fun _ => 0#32)
      have h1 := h (fun _ => 1#32)
      by_cases hal : a.toNat%w.bytes=0
      · cases device : B.device? a with
        | none => simp [interp,hal,hout,rom,device] at h0
        | some dev =>
          by_cases access : (dev.read && decide (w.bytes=dev.width))=true
          · simp only [interp,hal,ne_eq,not_true_eq_false,ite_false,hout,Bool.false_eq_true,rom,device,access,ite_true] at h0 h1
            have hc := (Result.ok.inj (h0.trans h1.symm)).1
            have hv := congrArg (fun k : Core => k.get rd) hc
            rw [Core.wr_get_self _ _ _ _ hrd,Core.wr_get_self _ _ _ _ hrd,extend_zero,extend_one] at hv
            exact (by decide : (0#32 : Word)≠1#32) hv
          · simp [interp,hal,hout,rom,device,access] at h0
      · simp [interp,hal] at h0

/-- Sound promotion of a deterministic load when its destination is used. -/
theorem promote {B : Board} {img : List Segment} {c d : Core} {ram after : Word → BitVec 8}
    {w : Width} {signed : Bool} {rd rs : Reg} {off len : Word}
    (hal : c.pc.getLsbD 0=false) (hf : fetchDecode img c.pc=some (.load w signed rd rs off,len))
    (hrd : rd.val≠0) (h : DetStep B img ⟨c,ram⟩ ⟨d,after⟩) : Quiet.Step B img ⟨c,ram⟩ ⟨d,after⟩ := by
  have all (o : Oracle) : interp B img o (exec c len (.load w signed rd rs off)) ram 0 []=.ok d after [] := by
    have hs := stepInstr_of (B := B) (img := img) (m := (⟨c,ram⟩ : Machine)) (o := o) hal hf
    exact hs.symm.trans (h o)
  have hs := source B img c d ram after w signed rd (c.get rs+off) (c.pc+len) hrd (by intro o;simpa only [exec_load] using all o)
  apply QuietEffect.promote hal hf _ h
  exact .load (Or.inr hs) (fun _ => .done _)
end E5R.Thermostat.QuietLoad
