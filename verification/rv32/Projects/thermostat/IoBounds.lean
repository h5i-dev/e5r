import Projects.thermostat.FirmwareStream
set_option autoImplicit false
namespace E5R.Thermostat.IoBounds
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def Reads (log : List Observed.Read) : Prop := ∀ r∈log,
  (r.addr=0x10000000#32 ∨ r.addr=0x10000005#32) ∧ r.width=.b

def Writes (events : List Event) : Prop := ∀ e∈events,e.addr=0x10000000#32 ∧ e.val.toNat<256

def Exec (m : Machine) (o : Oracle) : Prop := ∀ d after evs reads,
  Observed.stepInstr B img m o=⟨.ok d after evs,reads⟩ → Reads reads ∧ Writes evs

theorem no_reads : Reads [] := fun _ h => by cases h

theorem no_writes : Writes [] := fun _ h => by cases h

theorem lsr {log} (h : log=[] ∨ ∃ value,log=[⟨0x10000005#32,.b,value,0⟩]) : Reads log := by
  rcases h with rfl|⟨value,rfl⟩
  · exact no_reads
  · intro r member
    have same := List.mem_singleton.mp member
    subst r
    exact ⟨Or.inr rfl,rfl⟩

theorem rbr (value : Word) : Reads [⟨0x10000000#32,.b,value,0⟩] := by
  intro r member
  have same := List.mem_singleton.mp member
  subst r
  exact ⟨Or.inl rfl,rfl⟩

theorem thr (byte : BitVec 8) : Writes [⟨0x10000000#32,UartTxByte.word byte⟩] := by
  intro e member
  have same := List.mem_singleton.mp member
  subst e
  refine ⟨rfl,?_⟩
  simp only [UartTxByte.word,BitVec.toNat_setWidth]
  have bound := byte.isLt
  omega

theorem of_eq {m o c ram evs log} (step : Observed.stepInstr B img m o=⟨.ok c ram evs,log⟩)
    (reads : Reads log) (writes : Writes evs) : Exec m o := by
  intro d after events found actual
  rw [step] at actual
  cases actual
  exact ⟨reads,writes⟩

theorem uart {c ram g suffix} (h : UartTxPhase.At c ram g suffix) (o : Oracle) : Exec ⟨c,ram⟩ o := by
  cases h with
  | loading _ _ live =>
    obtain ⟨step,post⟩ := UartTxReactive.load live
    exact of_eq (step o) no_reads no_writes
  | polling _ _ live =>
    obtain ⟨d,log,step,post,only,rest⟩ := UartTxReactive.polling_next live o
    exact of_eq step (lsr only) no_writes
  | before _ _ live =>
    obtain ⟨step,post⟩ := UartTxReactive.increment live
    exact of_eq (step o) no_reads no_writes
  | @emitting src byte rest p phase queue live =>
    obtain ⟨step,post⟩ := UartTxReactive.emit live o
    exact of_eq step no_reads (thr byte)
  | branch _ _ live =>
    obtain ⟨d,step,post⟩ := UartTxReactive.branch live
    exact of_eq (step o) no_reads no_writes

theorem send {call : SendPhase.Call} {m g} (h : SendPhase.Active call m g) (o : Oracle) : Exec m o := by
  cases h with
  | head _ _ _ live | body _ _ _ _ _ _ live => exact uart live.2.2.1 o

theorem receive {m g} (h : ReceivePhases.Active m g) (o : Oracle) : Exec m o := by
  rcases h with header|length|chunk
  · cases header with
    | polling _ _ live _ =>
      obtain ⟨d,log,step,post,only,rest⟩ := HeaderReactive.polling_next live o
      exact of_eq step (lsr only) no_writes
    | rbr _ _ live _ =>
      obtain ⟨step,post⟩ := HeaderReactive.rbr_next live o
      exact of_eq step (rbr _) no_writes
  · cases length with
    | polling _ _ _ live _ =>
      obtain ⟨d,log,step,post,only,rest⟩ := LengthReactive.polling_next live o
      exact of_eq step (lsr only) no_writes
    | rbr _ _ _ live _ =>
      obtain ⟨step,post⟩ := LengthReactive.rbr_next live o
      exact of_eq step (rbr _) no_writes
  · cases chunk with
    | polling _ _ live _ =>
      obtain ⟨d,log,step,post,only,rest⟩ := ChunkReactive.polling_next live o
      exact of_eq step (lsr only) no_writes
    | rbr _ _ live _ =>
      obtain ⟨step,post⟩ := ChunkReactive.rbr_next live o
      exact of_eq step (rbr _) no_writes

theorem cut {m g} (h : FirmwareStream.At m g) (o : Oracle) : Exec m o := by
  rcases h with read|normal|refusal
  · exact receive read o
  · obtain ⟨original,before,response,served,used,json,close,headOnly,ready,live,pending⟩ := normal
    exact send live o
  · obtain ⟨original,before,s,served,status,ready,live,pending⟩ := refusal
    exact send live o

/-- Quiet certificates exclude all MMIO observations, not just the projected
    RBR/THR bytes. Active instruction cases admit only RBR/LSR and byte THR. -/
theorem one {m g d reads evs} (h : ReactiveEnvelope.Envelope FirmwareStream.At m g)
    (actual : Observed.Step B img m d reads evs) : Reads reads ∧ Writes evs := by
  obtain ⟨mask,n,last,quiet,post⟩ := h
  cases quiet with
  | refl =>
    cases actual with
    | instr o value =>
      apply cut post o
      cases found : Observed.stepInstr B img _ o with
      | mk result log => simpa only [found] using congrArg (fun value => Observed.Result.mk value log) value
    | irq code enabled branch => simp [irqEnabled,mask] at enabled
  | step first rest =>
    obtain ⟨rfl,rfl,rfl⟩ := QuietPrefix.unique_step first mask actual
    exact ⟨no_reads,no_writes⟩

theorem observed {m reads evs} (actual : Observed.Reach B img FirmwareStream.Reset m reads evs) : Reads reads ∧ Writes evs := by
  induction actual with
  | init => exact ⟨no_reads,no_writes⟩
  | @step m d oldReads reads oldEvs evs path step ih =>
    obtain ⟨g,env,trace,safe⟩ := FirmwareStream.observed_prefix path
    obtain ⟨newReads,newWrites⟩ := one env step
    refine ⟨?_,?_⟩
    · intro r member
      rcases List.mem_append.mp member with old|last
      · exact ih.1 r old
      · exact newReads r last
    · intro e member
      rcases List.mem_append.mp member with old|last
      · exact ih.2 e old
      · exact newWrites e last

theorem platform {m evs} (actual : E5R.Reach B img FirmwareStream.Reset m evs) : Writes evs ∧
    ∃ reads,Observed.Reach B img FirmwareStream.Reset m reads evs ∧ Reads reads := by
  obtain ⟨reads,path⟩ := Observed.reach_complete actual
  have bounds := observed path
  exact ⟨bounds.2,reads,path,bounds.1⟩
end E5R.Thermostat.IoBounds
