import Projects.thermostat.ShellCall
import Projects.thermostat.ShellDecision
namespace E5R.Thermostat.ShellExecute
open E5R E5R.Thermostat

/-- Real write-handler call plus Result dispatch. Every refused command reaches
    the error arm; only a successful transition reaches the apply arm. -/
theorem contract_tight (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (h : ShellCall.Pre B c ram p admin s cmd) :
    ∃ n d r, n ≤ 99 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = (if ShellDecision.success (Spec.transition admin s cmd) then 0x80000678 else 0x80000648) ∧
      d.get 2 = c.get 2 ∧ d.get 20 = c.get 23+4#32 ∧ d.sameCsr c ∧
      Outcome.At r (p+104#32) (Spec.transition admin s cmd) ∧
      Encoding.SnapshotAt r (c.get 23+4#32) s ∧
      (∀ x, (∀ i : Fin 124, x ≠ p+BitVec.ofNat 32 i.val) → r x = ram x) ∧ Upper.Frame c d ∧ d.get 10 = BitVec.ofNat 32 (r (p+104#32)).toNat ∧ d.get 21 = BitVec.ofNat 32 (r (p+114#32)).toNat := by
  obtain ⟨n,dc,r,hn,hr,hpc,hsp,hstate,hcsr,hout,hsnap,hframe,hupper⟩ := ShellCall.contract_tight B c ram p admin s cmd h
  have hptr : dc.get 2+24#32 = p+104#32 := by rw [hsp,h.sp];simp [BitVec.add_assoc]
  obtain ⟨d,hd,hpc',hregs,hcsr',hfirst,hReplyFirst⟩ := ShellDecision.contract B dc r (Spec.transition admin s cmd) hpc
    (by rw [hptr];exact Memory.sub_block h.arena (by decide) (by decide))
    (by rw [hptr];exact hout)
  refine ⟨n+4,d,r,by omega,hr.trans hd,hpc',(hregs 2 (by decide) (by decide) (by decide)).trans hsp,
    (hregs 20 (by decide) (by decide) (by decide)).trans hstate,hcsr'.trans hcsr,hout,hsnap,hframe,?_,?_,?_⟩
  · intro r hr
    exact (hregs r (Upper.ne_low r hr 10 (by decide)) (Upper.ne_low r hr 11 (by decide))
      (Upper.ne_low r hr 21 (by decide))).trans (hupper r hr)
  · simpa only [hptr] using hfirst
  · have hptrReply : dc.get 2+34#32 = p+114#32 := by rw [hsp,h.sp];simp [BitVec.add_assoc]
    simpa only [hptrReply] using hReplyFirst

/-- The original 128-byte frame remains available for existing clients. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (h : ShellCall.Pre B c ram p admin s cmd) :
    ∃ n d r, n ≤ 99 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = (if ShellDecision.success (Spec.transition admin s cmd) then 0x80000678 else 0x80000648) ∧
      d.get 2 = c.get 2 ∧ d.get 20 = c.get 23+4#32 ∧ d.sameCsr c ∧
      Outcome.At r (p+104#32) (Spec.transition admin s cmd) ∧
      Encoding.SnapshotAt r (c.get 23+4#32) s ∧
      (∀ x, (∀ i : Fin 128, x ≠ p+BitVec.ofNat 32 i.val) → r x = ram x) ∧ Upper.Frame c d ∧ d.get 10 = BitVec.ofNat 32 (r (p+104#32)).toNat ∧ d.get 21 = BitVec.ofNat 32 (r (p+114#32)).toNat := by
  obtain ⟨n,d,r,hn,hr,hpc,hsp,hs,hcsr,hout,hsnap,hframe,hupper,hfirst,hreply⟩ := contract_tight B c ram p admin s cmd h
  refine ⟨n,d,r,hn,hr,hpc,hsp,hs,hcsr,hout,hsnap,?_,hupper,hfirst,hreply⟩
  intro x hx
  exact hframe x (fun i => hx ⟨i.val,by have := i.isLt;omega⟩)

end E5R.Thermostat.ShellExecute
