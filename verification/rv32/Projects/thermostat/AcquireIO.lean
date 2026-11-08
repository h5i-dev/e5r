import Projects.thermostat.Acquire
import Projects.thermostat.EngineIO
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Acquire
open E5R E5R.Thermostat

theorem contract_io (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram p admin s cmd) :
    ∃ n d r, n ≤ 175 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Engine.Post c d ram r p s (Spec.transition admin s cmd) ∧ Engine.TopSame p ram r ∧ BufferRegs.Frame c d ∧
      (∀ err, Spec.transition admin s cmd = .error err → d.get 10 = BitVec.ofNat 32 (Errors.code err).toNat) := by
  have hr := available B c ram h.pc h.engineRam h.engineAlign h.available
  obtain ⟨n,d,r,hn,hr',hp,htop,hbuf,herr⟩ := Engine.contract_io B (acquired c) (result ram (c.get 23)) p admin s cmd
    (establishes_pre B c ram p admin s cmd h)
  have htop' : Engine.TopSame p ram r := by
    intro k
    rw [htop k]
    apply frame
    intro i
    exact Ne.symm (h.engineSep ⟨i.val,by have := i.isLt;omega⟩ ⟨124+k.val,by have := k.isLt;omega⟩)
  refine ⟨4+n,d,r,by omega,hr.trans hr',?_,htop',?_,herr⟩
  · have heng : (acquired c).get 23 = c.get 23 := by simp [acquired,Core.wr_get_ne]
    have hsp : (acquired c).get 2 = c.get 2 := by simp [acquired,Core.wr_get_ne]
    refine ⟨hp.pc,hp.sp.trans hsp,by simpa only [heng] using hp.statePtr,
      hp.enginePtr.trans heng,hp.csr.trans (by rfl),by simpa only [heng] using hp.state,
      by simpa only [heng] using hp.released,hp.reply,?_⟩
    intro x hxa hxe
    rw [hp.frame x hxa (by simpa only [heng] using hxe)]
    apply frame
    intro i
    exact hxe ⟨i.val,by have := i.isLt;omega⟩

  · constructor
    · exact hbuf.capacity |>.trans (by simp [acquired,Core.wr_get_ne])
    · exact hbuf.pointer |>.trans (by simp [acquired,Core.wr_get_ne])
    · exact hbuf.future |>.trans (by simp [acquired,Core.wr_get_ne])
    · exact hbuf.response |>.trans (by simp [acquired,Core.wr_get_ne])
    · exact hbuf.completion |>.trans (by simp [acquired,Core.wr_get_ne])
end E5R.Thermostat.Acquire
