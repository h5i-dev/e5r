-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.EngineIO
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ApplyCallQuiet
import Projects.thermostat.MarshalIOQuiet
import Projects.thermostat.ReleaseBorrowRegsQuiet
import Projects.thermostat.ReplyRestoreIOQuiet
import Projects.thermostat.ShellExecuteIOQuiet
import Projects.thermostat.StateStoreQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.Engine
theorem prepare_io_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (res : Spec.Success)
    (h : Pre B c ram p admin s cmd) (hres : Spec.transition admin s cmd = .ok res) :
    ∃ n d r, n ≤ 151 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Pending c d ram r p s res ∧ TopSame p ram r ∧ BufferRegs.Frame c d := by
  obtain ⟨n0,c0,r0,hn0,hr0,hpc0,hsp0,hstate0,hcsr0,hout0,hsnap0,hframe0,hupper0,hfirst0,hreply0,hbuf0⟩ :=
    E5R.Thermostat.ShellExecute.contract_io_quiet B c ram p admin s cmd h.toPre
  have hsp0' : c0.get 2 = p+80#32 := hsp0.trans h.sp
  have houtPtr : c0.get 2+24#32 = p+104#32 := by rw [hsp0'];simp [BitVec.add_assoc]
  have hreplyPtr : c0.get 2+34#32 = p+114#32 := by rw [hsp0'];simp [BitVec.add_assoc]
  have hwritePtr : c0.get 2+14#32 = p+94#32 := by rw [hsp0'];simp [BitVec.add_assoc]
  have heng0 : c0.get 23 = c.get 23 := hupper0 23 (by decide)
  have hout : Outcome.At r0 (p+104#32) (.ok res) := by rw [← hres];exact hout0
  have hreply : Encoding.SnapshotAt r0 (c0.get 2+34#32) res.reply := by
    rw [hreplyPtr]
    simpa [BitVec.add_assoc] using hout.2
  have hfirst : byteOf (c0.get 10) 0 = r0 (c0.get 2+24#32) := by
    rw [houtPtr,hfirst0,← Memory.load_byte]
    exact Marshal.byte_load _ _
  have hreplyFirst : byteOf (c0.get 21) 0 = r0 (c0.get 2+34#32) := by
    rw [hreplyPtr,hreply0,← Memory.load_byte]
    exact Marshal.byte_load _ _
  have hmarshalMem : Memory.Block B (c0.get 2) 44 := by
    rw [hsp0']
    exact Memory.sub_block (B := B) (p := p) (n := 128) (off := 80) (m := 44) h.arena (by decide) (by decide)
  have hspAlign : (c0.get 2).toNat % 4 = 0 := by rw [hsp0'];exact Memory.word_aligned p 20 h.align
  let rm := Marshal.result r0 (c0.get 2) (c0.get 10)
  obtain ⟨cm,hrm,hpcm,hspm,hstatem,hengm,hcsrm,hcachem,hbufm⟩ := E5R.Thermostat.Marshal.contract_io_quiet B c0 r0
    (by simpa [hres,ShellDecision.success] using hpc0) hmarshalMem hspAlign res.reply hreply hreplyFirst
  have hframeM0 : TightFrame p r0 rm := by
    intro x hx
    apply Marshal.frame r0 (c0.get 2) (c0.get 10) x
    intro i
    rw [hsp0']
    have hi := i.isLt
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨80+i.val,by omega⟩
  have hframeM : TightFrame p ram rm := fun x hx => (hframeM0 x hx).trans (hframe0 x hx)
  have hwritem : Encoding.OptionAt rm (p+94#32) res.write := by
    simpa only [hwritePtr] using Marshal.source r0 (c0.get 2) (c0.get 10) res.write hfirst (by rw [houtPtr];exact hout.1)
  have hstateM : cm.get 20 = c.get 23+4#32 := hstatem.trans hstate0
  have hspM : cm.get 2 = p+80#32 := hspm.trans hsp0'
  have hengineM : cm.get 23 = c.get 23 := hengm.trans heng0
  have happly : ApplyCall.Pre B cm rm p s res.write := by
    refine ⟨hpcm,hspM,h.arena,h.align,?_,?_,?_,hwritem,?_⟩
    · simpa only [hstateM] using h.stateRam
    · simpa only [hstateM] using h.stateAlign
    · rw [hstateM]
      exact snapshot_frame (tight_weaken hframeM) h.engineSep s h.stateAt
    · rw [hstateM]
      exact h.stateSep
  obtain ⟨na,ca,ra,hna,hra,hpca,hspca,hstateca,hengca,hcsrca,hcomputed,hframea,hregsa,hworda⟩ :=
    E5R.Thermostat.ApplyCall.contract_tight_quiet B cm rm p s res.write happly
  have hcacheM : ReplyCache.At cm rm (p+80#32) res.reply := by
    have hh : ReplyCache.At cm rm (c0.get 2) res.reply := by exact hcachem
    rw [hsp0'] at hh
    exact hh
  have hcacheA : ReplyCache.At ca ra (p+80#32) res.reply := by
    apply ReplyCache.preserve cm ca rm ra (p+80#32) res.reply hcacheM
    · exact hregsa 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hregsa 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hregsa 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hregsa 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hregsa 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simpa [BitVec.add_assoc] using hworda
  have hframeA : TightFrame p ram ra := fun x hx => (hframea x hx).trans (hframeM x hx)
  refine ⟨n0+25+na,ca,ra,by omega,(hr0.trans hrm).trans hra,?_⟩
  refine ⟨⟨hpca,hspca.trans hspM,hstateca.trans hstateM,hengca.trans hengineM,
    hcsrca.trans (hcsrm.trans hcsr0),hcomputed,hcacheA,(word_frame (tight_weaken hframeA) h.engineSep).trans h.borrowed,tight_weaken hframeA⟩,tight_top hframeA,?_⟩
  exact ⟨(hregsa 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hbufm.capacity.trans hbuf0.capacity),
    (hregsa 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hbufm.pointer.trans hbuf0.pointer),
    (hregsa 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hbufm.future.trans hbuf0.future),
    (hregsa 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hbufm.response.trans hbuf0.response),
    (hregsa 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hbufm.completion.trans hbuf0.completion)⟩

end E5R.Thermostat.Engine
namespace E5R.Thermostat.Engine
theorem persist_io_quiet (B : Board) (c ca : Core) (ram ra : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (res : Spec.Success)
    (h : Pre B c ram p admin s cmd) (hpending : Pending c ca ram ra p s res) :
    ∃ d r, Quiet.Steps B img 20 ⟨ca,ra⟩ ⟨d,r⟩ ∧ Post c d ram r p s (.ok res) ∧ TopSame p ra r ∧ BufferRegs.Frame ca d := by
  have hmem : Memory.Block B (ca.get 2) 34 := by
    rw [hpending.sp]
    exact Memory.sub_block (B := B) (p := p) (n := 128) (off := 80) (m := 34) h.arena (by decide) (by decide)
  have hal : (ca.get 2).toNat % 4 = 0 := by rw [hpending.sp];exact Memory.word_aligned p 20 h.align
  have he : Memory.Block B (ca.get 23) 14 := by simpa only [hpending.enginePtr] using h.engineRam
  have hae : (ca.get 23).toNat % 4 = 0 := by simpa only [hpending.enginePtr] using h.engineAlign
  have hrel : ca.get 20 = ca.get 23+4#32 := by rw [hpending.statePtr,hpending.enginePtr]
  let rs := StateStore.result ra (ca.get 2) (ca.get 23)
  obtain ⟨cs,hrs,hpcs,hsps,hstates,hengs,hcsrs,hregss⟩ := E5R.Thermostat.StateStore.contract_quiet B ca ra hpending.pc hmem (by omega) he hae hrel
  have hspS : cs.get 2 = p+80#32 := hsps.trans hpending.sp
  have hengS : cs.get 23 = c.get 23 := hengs.trans hpending.enginePtr
  have hptr : ca.get 2+24#32 = p+104#32 := by rw [hpending.sp];simp [BitVec.add_assoc]
  have hstateS : Encoding.SnapshotAt rs (c.get 23+4#32) (Spec.apply s res.write) := by
    have hh := StateStore.source ra (ca.get 2) (ca.get 23) (Spec.apply s res.write)
      (by rw [hptr];exact hpending.computed)
    change Encoding.SnapshotAt rs (ca.get 23+4#32) (Spec.apply s res.write) at hh
    rw [hpending.enginePtr] at hh
    exact hh
  have hborrowS : ramRead rs (c.get 23) .w = 0#32 := by
    have hh := StateStore.released ra (ca.get 2) (ca.get 23)
      (by rw [hpending.enginePtr];exact hpending.borrowed)
    change ramRead rs (ca.get 23) .w = 0#32 at hh
    rw [hpending.enginePtr] at hh
    exact hh
  have hwordS : ramRead rs (p+84#32) .w = ramRead ra (p+84#32) .w := by
    apply ramRead_w_congr
    intro k hk
    apply StateStore.frame ra (ca.get 2) (ca.get 23)
    intro i
    rw [hpending.enginePtr]
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using Ne.symm (h.engineSep i ⟨84+k,by omega⟩)
  have hcacheS : ReplyCache.At cs rs (p+80#32) res.reply := by
    apply ReplyCache.preserve ca cs ra rs (p+80#32) res.reply hpending.cached
    · exact hregss 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hregss 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hregss 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hregss 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hregss 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simpa [BitVec.add_assoc] using hwordS
  have hmemR : Memory.Block B (cs.get 2) 34 := by simpa only [hsps] using hmem
  have halR : (cs.get 2).toNat % 4 = 0 := by simpa only [hsps] using hal
  let rr := ReplyRestore.result cs rs (cs.get 2)
  obtain ⟨cr,hrr,hpcr,hspr,hstater,hengr,hcsrr,hbufr⟩ := E5R.Thermostat.ReplyRestore.contract_io_quiet B cs rs hpcs hmemR halR
  have hptrR : cs.get 2+24#32 = p+104#32 := by rw [hspS];simp [BitVec.add_assoc]
  have hframeR : ArenaFrame p rs rr := by
    intro x hx
    apply ReplyRestore.frame cs rs (cs.get 2) x
    intro i
    rw [hptrR]
    have hi := i.isLt
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨104+i.val,by omega⟩
  have hstateR := snapshot_frame hframeR h.engineSep (Spec.apply s res.write) hstateS
  have hborrowR := (word_frame hframeR h.engineSep).trans hborrowS
  have hreplyR : Encoding.SnapshotAt rr (p+104#32) res.reply := by
    have hh := ReplyRestore.source cs rs (cs.get 2) res.reply
      (by rw [hspS];exact hcacheS)
    change Encoding.SnapshotAt rr (cs.get 2+24#32) res.reply at hh
    rw [hptrR] at hh
    exact hh
  have htop : TopSame p ra rr := by
    intro k
    change ReplyRestore.result cs rs (cs.get 2) _ = _
    rw [ReplyRestore.frame cs rs (cs.get 2) _ (by
      intro j
      rw [hptrR]
      have hk := k.isLt
      have hj := j.isLt
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using
        ShellCall.offset_ne p (124+k.val) (104+j.val) (by omega) (by omega) (by omega))]
    apply StateStore.frame ra (ca.get 2) (ca.get 23)
    intro i
    rw [hpending.enginePtr]
    exact Ne.symm (h.engineSep i ⟨124+k.val,by have := k.isLt;omega⟩)
  refine ⟨cr,rr,hrs.trans hrr,?_,htop,?_⟩
  · refine ⟨hpcr,(hspr.trans hspS).trans h.sp.symm,
      (hstater.trans hstates).trans hpending.statePtr,(hengr.trans hengs).trans hpending.enginePtr,
      hcsrr.trans (hcsrs.trans hpending.csr),hstateR,hborrowR,hreplyR,?_⟩
    intro x hxArena hxEngine
    rw [hframeR x hxArena]
    exact (StateStore.frame ra (ca.get 2) (ca.get 23) x (by simpa only [hpending.enginePtr] using hxEngine)).trans (hpending.frame x hxArena)

  · exact ⟨hbufr.capacity.trans (hregss 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
      hbufr.pointer.trans (hregss 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
      hbufr.future.trans (hregss 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),hbufr.response.trans (hregss 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),hbufr.completion.trans (hregss 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))⟩

end E5R.Thermostat.Engine
namespace E5R.Thermostat.Engine
theorem rejected_io_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (err : Spec.Error)
    (h : Pre B c ram p admin s cmd) (hres : Spec.transition admin s cmd = .error err) :
    ∃ n d r, n ≤ 102 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Post c d ram r p s (.error err) ∧ TopSame p ram r ∧ BufferRegs.Frame c d ∧ d.get 10 = BitVec.ofNat 32 (Errors.code err).toNat := by
  obtain ⟨n0,c0,r0,hn0,hr0,hpc0,hsp0,hstate0,hcsr0,hout0,hsnap0,hframe0,hupper0,hfirst0,hreply0,hbuf0⟩ :=
    E5R.Thermostat.ShellExecute.contract_io_quiet B c ram p admin s cmd h.toPre
  have heng0 : c0.get 23 = c.get 23 := hupper0 23 (by decide)
  have he : Memory.Block B (c0.get 23) 14 := by simpa only [heng0] using h.engineRam
  have hae : (c0.get 23).toNat % 4 = 0 := by simpa only [heng0] using h.engineAlign
  have hout : Outcome.At r0 (p+104#32) (.error err) := by rw [← hres];exact hout0
  have hborrow : ramRead r0 (c0.get 23) .w = 0xffffffff#32 := by
    rw [heng0]
    exact (word_frame (tight_weaken hframe0) h.engineSep).trans h.borrowed
  let rb := ReleaseBorrow.result r0 (c0.get 23)
  obtain ⟨d,hrb,hpcb,hspb,hstateb,hengb,hcsrb,hregsb⟩ := E5R.Thermostat.ReleaseBorrow.contract_regs_quiet B c0 r0
    (by simpa [hres,ShellDecision.success] using hpc0) he hae
  have hstate : Encoding.SnapshotAt rb (c.get 23+4#32) s := by
    have hh := ReleaseBorrow.snapshot r0 (c0.get 23) s (by rw [heng0];exact hsnap0)
    change Encoding.SnapshotAt rb (c0.get 23+4#32) s at hh
    rw [heng0] at hh
    exact hh
  have hreleased : ramRead rb (c.get 23) .w = 0#32 := by
    have hh := ReleaseBorrow.released r0 (c0.get 23) hborrow
    change ramRead rb (c0.get 23) .w = 0#32 at hh
    rw [heng0] at hh
    exact hh
  have hreply : ReplyAt rb p (.error err) := by
    exact (ReleaseBorrow.frame r0 (c0.get 23) (p+104#32) (by
      intro i
      rw [heng0]
      exact Ne.symm (h.engineSep ⟨i.val,by have := i.isLt;omega⟩ ⟨104,by decide⟩))).trans hout.2
  have htop : TopSame p ram rb := by
    intro k
    change ReleaseBorrow.result r0 (c0.get 23) _ = _
    rw [ReleaseBorrow.frame r0 (c0.get 23) _ (by
      intro i
      rw [heng0]
      exact Ne.symm (h.engineSep ⟨i.val,by have := i.isLt;omega⟩ ⟨124+k.val,by have := k.isLt;omega⟩))]
    exact tight_top hframe0 k
  refine ⟨n0+3,d,rb,by omega,hr0.trans hrb,?_,htop,?_,?_⟩
  · refine ⟨hpcb,hspb.trans hsp0,hstateb.trans hstate0,hengb.trans heng0,
      hcsrb.trans hcsr0,hstate,hreleased,hreply,?_⟩
    intro x hxArena hxEngine
    exact (ReleaseBorrow.frame r0 (c0.get 23) x (by
      intro i
      rw [heng0]
      exact hxEngine ⟨i.val,by have := i.isLt;omega⟩)).trans (tight_weaken hframe0 x hxArena)

  · exact ⟨(hregsb 18 (by decide)).trans hbuf0.capacity,(hregsb 19 (by decide)).trans hbuf0.pointer,
      (hregsb 8 (by decide)).trans hbuf0.future,(hregsb 9 (by decide)).trans hbuf0.response,(hregsb 22 (by decide)).trans hbuf0.completion⟩
  · rw [hregsb 10 (by decide),hfirst0,hout.2]

end E5R.Thermostat.Engine
namespace E5R.Thermostat.Engine
theorem contract_io_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram p admin s cmd) :
    ∃ n d r, n ≤ 171 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Post c d ram r p s (Spec.transition admin s cmd) ∧ TopSame p ram r ∧ BufferRegs.Frame c d ∧
      (∀ err, Spec.transition admin s cmd = .error err → d.get 10 = BitVec.ofNat 32 (Errors.code err).toNat) := by
  cases hres : Spec.transition admin s cmd with
  | error err =>
    obtain ⟨n,d,r,hn,td,hd,ht,hbuf,h10⟩ := E5R.Thermostat.Engine.rejected_io_quiet B c ram p admin s cmd err h hres
    refine ⟨n,d,r,by omega,td,hd,ht,hbuf,?_⟩
    intro other ho
    cases ho
    exact h10
  | ok res =>
    obtain ⟨n,a,ra,hn,ta,ha,ht,hbuf⟩ := E5R.Thermostat.Engine.prepare_io_quiet B c ram p admin s cmd res h hres
    obtain ⟨d,r,td,hd,ht',hbuf'⟩ := E5R.Thermostat.Engine.persist_io_quiet B c a ram ra p admin s cmd res h ha
    refine ⟨n+20,d,r,by omega,ta.trans td,hd,top_trans ht ht',BufferRegs.trans hbuf hbuf',?_⟩
    intro err he
    cases he

end E5R.Thermostat.Engine
