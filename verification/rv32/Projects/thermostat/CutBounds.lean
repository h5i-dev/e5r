import Projects.thermostat.FirmwareStream
import Projects.thermostat.PanicLoop
set_option autoImplicit false
namespace E5R.Thermostat.CutBounds
open E5R E5R.Thermostat

def Pc (c : Core) : Prop :=
  (0x800007ea≤c.pc.toNat ∧ c.pc.toNat<0x8000080a) ∨ (0x80000b9e≤c.pc.toNat ∧ c.pc.toNat≤0x80000fbe)

theorem uart {c ram g suffix} (h : UartTxPhase.At c ram g suffix) : Pc c := by
  cases h with
  | loading _ _ live | before _ _ live | emitting _ _ live | branch _ _ live =>
    unfold Pc
    rw [live.pc]
    decide +kernel
  | polling _ _ live =>
    rcases live.waiting with pc|pc|pc|pc|pc
    all_goals unfold Pc;rw [pc];decide +kernel

theorem send {call : SendPhase.Call} {m g} (h : SendPhase.Active call m g) : Pc m.core := by
  cases h with
  | head _ _ _ live | body _ _ _ _ _ _ live => exact uart live.2.2.1

theorem receive {m g} (h : ReceivePhases.Active m g) : Pc m.core := by
  rcases h with header|length|chunk
  · cases header with
    | polling _ _ live _ =>
      rcases live.waiting with pc|pc|pc|pc
      all_goals unfold Pc;rw [pc];decide +kernel
    | rbr _ _ live _ => unfold Pc;rw [live.pc];decide +kernel
  · cases length with
    | polling _ _ _ live _ =>
      rcases live.waiting with pc|pc|pc|pc
      all_goals unfold Pc;rw [pc];decide +kernel
    | rbr _ _ _ live _ => unfold Pc;rw [live.pc];decide +kernel
  · cases chunk with
    | polling _ _ live _ =>
      rcases live.waiting with pc|pc|pc|pc|pc
      all_goals unfold Pc;rw [pc];decide +kernel
    | rbr _ _ live _ => unfold Pc;rw [live.pc];decide +kernel

theorem active {m g} (h : FirmwareStream.At m g) : Pc m.core := by
  rcases h with read|normal|refusal
  · exact receive read
  · obtain ⟨original,before,response,served,used,json,close,headOnly,ready,live,pending⟩ := normal
    exact send live
  · obtain ⟨original,before,s,served,status,ready,live,pending⟩ := refusal
    exact send live

theorem excludes_spin {c} (h : Pc c) : ¬PanicLoop.At c := by
  unfold Pc at h
  intro panic
  rcases panic with pc|pc|pc
  all_goals simp only [pc,BitVec.toNat_ofNat,Nat.reduceMod] at h;omega

theorem envelope {m g} (h : ReactiveEnvelope.Envelope FirmwareStream.At m g) : ¬PanicLoop.At m.core := by
  obtain ⟨mask,n,last,quiet,post⟩ := h
  intro panic
  exact excludes_spin (active post) (PanicLoop.quiet panic quiet)

theorem reachable {m evs} (actual : E5R.Reach UartPlatform.board img FirmwareStream.Reset m evs) : ¬PanicLoop.At m.core := by
  obtain ⟨safe,reads,g,path,env,trace⟩ := FirmwareStream.platform_prefix actual
  exact envelope env
/-- The reusable receive cuts expose the real persisted snapshot, free
    borrow and invariant, including while another request is incomplete. -/
theorem receive_commit {m g} (h : ReceivePhases.Active m g) :
    AppState.At m.ram g.snapshot ∧ Spec.Inv g.snapshot ∧ m.core.get 2=0x80ffeb90#32 := by
  rcases h with header|length|chunk
  · cases header with
    | polling eq _ live _ | rbr eq _ live _ => subst g;exact ⟨live.stable.app,live.stable.invariant,live.stable.sp⟩
  · cases length with
    | polling eq _ _ live _ | rbr eq _ _ live _ => subst g;exact ⟨live.state.stable.app,live.state.stable.invariant,live.state.stable.sp⟩
  · cases chunk with
    | polling eq context live _ | rbr eq context live _ => subst g;exact ⟨context.app,context.invariant,live.live.stackPtr⟩

theorem send_sp {call : SendPhase.Call} {m g} (h : SendPhase.Active call m g) : m.core.get 2=call.frame+96#32 := by
  cases h with
  | head stage anchor prepared live =>
    have frame := live.2.2.2.1
    exact (frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((prepared.keep 2 (by decide) (by simp)).trans ((stage.keep 2 (by decide) (by simp)).trans stage.post.x2))
  | body stage headCore headRam anchor headDone prepared live =>
    have frame := live.2.2.2.1
    exact (frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((prepared.keep 2 (by decide) (by simp)).trans ((headDone.keep 2 (by decide) (by simp)).trans
        ((stage.keep 2 (by decide) (by simp)).trans stage.post.x2)))

/-- Actual UART cuts have one of two fixed, bounded stack pointers. This is
    distinct from an all-intermediate-SP claim before/reset initialization. -/
theorem active_sp {m g} (h : FirmwareStream.At m g) :
    m.core.get 2=0x80ffeb90#32 ∨ m.core.get 2=0x80ffeb60#32 := by
  rcases h with read|normal|refusal
  · exact Or.inl (receive_commit read).2.2
  · obtain ⟨original,before,response,served,used,json,close,headOnly,ready,live,pending⟩ := normal
    exact Or.inr (by simpa only [NormalSendPhase.call,show 0x80ffeb00#32+96#32=0x80ffeb60#32 by decide +kernel] using send_sp live)
  · obtain ⟨original,before,s,served,status,ready,live,pending⟩ := refusal
    exact Or.inr (by simpa only [RefusalSendPhase.call,show 0x80ffeb00#32+96#32=0x80ffeb60#32 by decide +kernel] using send_sp live)

end E5R.Thermostat.CutBounds
