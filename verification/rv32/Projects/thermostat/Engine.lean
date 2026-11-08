import Projects.thermostat.ShellExecute
import Projects.thermostat.Marshal
import Projects.thermostat.ApplyCall
import Projects.thermostat.StateStore
import Projects.thermostat.ReleaseBorrow
import Projects.thermostat.ReplyRestore
set_option maxRecDepth 500
set_option maxHeartbeats 200000
namespace E5R.Thermostat.Engine
open E5R E5R.Thermostat

def ArenaFrame (p : Word) (ram ram' : Word → BitVec 8) : Prop :=
  ∀ x, (∀ i : Fin 128, x ≠ p+BitVec.ofNat 32 i.val) → ram' x = ram x

/-- The saved outer s11 word occupies the four bytes above the live arena. -/
def TopSame (p : Word) (ram ram' : Word → BitVec 8) : Prop :=
  ∀ k : Fin 4, ram' (p+BitVec.ofNat 32 (124+k.val)) = ram (p+BitVec.ofNat 32 (124+k.val))

def TightFrame (p : Word) (ram ram' : Word → BitVec 8) : Prop :=
  ∀ x, (∀ i : Fin 124, x ≠ p+BitVec.ofNat 32 i.val) → ram' x = ram x

theorem tight_weaken {p r r'} (h : TightFrame p r r') : ArenaFrame p r r' :=
  fun x hx => h x (fun i => hx ⟨i.val,by have := i.isLt;omega⟩)

theorem tight_top {p r r'} (h : TightFrame p r r') : TopSame p r r' := by
  intro k
  apply h
  intro i
  have hk := k.isLt
  have hi := i.isLt
  exact ShellCall.offset_ne p (124+k.val) i.val (by omega) (by omega) (by omega)

theorem top_trans {p r0 r1 r2} (h : TopSame p r0 r1) (k : TopSame p r1 r2) : TopSame p r0 r2 :=
  fun i => (k i).trans (h i)

theorem top_word {p ram ram'} (h : TopSame p ram ram') :
    ramRead ram' (p+124#32) .w = ramRead ram (p+124#32) .w := by
  apply ramRead_w_congr
  intro k hk
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using h ⟨k,hk⟩

def Separate (eng p : Word) : Prop :=
  ∀ i : Fin 14, ∀ j : Fin 128, eng+BitVec.ofNat 32 i.val ≠ p+BitVec.ofNat 32 j.val

theorem frame_trans {p r0 r1 r2} (h : ArenaFrame p r0 r1) (k : ArenaFrame p r1 r2) : ArenaFrame p r0 r2 :=
  fun x hx => (k x hx).trans (h x hx)

theorem word_frame {p eng ram ram'} (h : ArenaFrame p ram ram') (hs : Separate eng p) :
    ramRead ram' eng .w = ramRead ram eng .w := by
  apply ramRead_w_congr
  intro k hk
  apply h
  intro j
  exact hs ⟨k,by omega⟩ j

theorem snapshot_frame {p eng ram ram'} (h : ArenaFrame p ram ram') (hs : Separate eng p)
    (s : Spec.Snapshot) (he : Encoding.SnapshotAt ram (eng+4#32) s) :
    Encoding.SnapshotAt ram' (eng+4#32) s := by
  intro i
  rw [h _ (by
    intro j
    have hi := i.isLt
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hs ⟨4+i.val,by omega⟩ j)]
  exact he i

structure Pre (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) : Prop
    extends ShellCall.Pre B c ram p admin s cmd where
  engineRam : Memory.Block B (c.get 23) 14
  engineAlign : (c.get 23).toNat % 4 = 0
  engineSep : Separate (c.get 23) p
  borrowed : ramRead ram (c.get 23) .w = 0xffffffff#32

/-- Ready to persist: actual apply has computed a new state and the original
    transition reply is still cached in the caller's registers/stack. -/
structure Pending (before after : Core) (ram ram' : Word → BitVec 8) (p : Word)
    (s : Spec.Snapshot) (res : Spec.Success) : Prop where
  pc : after.pc = 0x800006ea
  sp : after.get 2 = p+80#32
  statePtr : after.get 20 = before.get 23+4#32
  enginePtr : after.get 23 = before.get 23
  csr : after.sameCsr before
  computed : Encoding.SnapshotAt ram' (p+104#32) (Spec.apply s res.write)
  cached : ReplyCache.At after ram' (p+80#32) res.reply
  borrowed : ramRead ram' (before.get 23) .w = 0xffffffff#32
  frame : ArenaFrame p ram ram'

/-- Actual transition + successful result extraction + apply, before persistence. -/
theorem prepare_full (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (res : Spec.Success)
    (h : Pre B c ram p admin s cmd) (hres : Spec.transition admin s cmd = .ok res) :
    ∃ n d r, n ≤ 151 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Pending c d ram r p s res ∧ TopSame p ram r := by
  obtain ⟨n0,c0,r0,hn0,hr0,hpc0,hsp0,hstate0,hcsr0,hout0,hsnap0,hframe0,hupper0,hfirst0,hreply0⟩ :=
    ShellExecute.contract_tight B c ram p admin s cmd h.toPre
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
  obtain ⟨cm,hrm,hpcm,hspm,hstatem,hengm,hcsrm,hcachem⟩ := Marshal.contract B c0 r0
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
    ApplyCall.contract_tight B cm rm p s res.write happly
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
    hcsrca.trans (hcsrm.trans hcsr0),hcomputed,hcacheA,(word_frame (tight_weaken hframeA) h.engineSep).trans h.borrowed,tight_weaken hframeA⟩,tight_top hframeA⟩

theorem prepare (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (res : Spec.Success)
    (h : Pre B c ram p admin s cmd) (hres : Spec.transition admin s cmd = .ok res) :
    ∃ n d r, n ≤ 151 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Pending c d ram r p s res := by
  obtain ⟨n,d,r,hn,hr,hp,_⟩ := prepare_full B c ram p admin s cmd res h hres
  exact ⟨n,d,r,hn,hr,hp⟩

def endPc : Except Spec.Error Spec.Success → Word
 | .error _ => 0x80000652 | .ok _ => 0x80000736

def ReplyAt (ram : Word → BitVec 8) (p : Word) : Except Spec.Error Spec.Success → Prop
 | .error err => ram (p+104#32) = Errors.code err
 | .ok res => Encoding.SnapshotAt ram (p+104#32) res.reply

/-- Concrete engine-body postcondition, immediately before response encoding. -/
structure Post (before after : Core) (ram ram' : Word → BitVec 8) (p : Word)
    (s : Spec.Snapshot) (res : Except Spec.Error Spec.Success) : Prop where
  pc : after.pc = endPc res
  sp : after.get 2 = before.get 2
  statePtr : after.get 20 = before.get 23+4#32
  enginePtr : after.get 23 = before.get 23
  csr : after.sameCsr before
  state : Encoding.SnapshotAt ram' (before.get 23+4#32) (Spec.commit s res)
  released : ramRead ram' (before.get 23) .w = 0#32
  reply : ReplyAt ram' p res
  frame : ∀ x, (∀ i : Fin 128, x ≠ p+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 14, x ≠ before.get 23+BitVec.ofNat 32 i.val) → ram' x = ram x

/-- Recover the precise 124-byte footprint without changing the old Post API. -/
theorem post_tight {c d ram ram' p s res} (h : Post c d ram ram' p s res)
    (ht : TopSame p ram ram') (x : Word)
    (ha : ∀ i : Fin 124, x ≠ p+BitVec.ofNat 32 i.val)
    (he : ∀ i : Fin 14, x ≠ c.get 23+BitVec.ofNat 32 i.val) : ram' x = ram x := by
  classical
  by_cases hf : ∀ i : Fin 128, x ≠ p+BitVec.ofNat 32 i.val
  · exact h.frame x hf he
  · have hex : ∃ i : Fin 128, x = p+BitVec.ofNat 32 i.val := by
      apply Classical.byContradiction
      intro hn
      apply hf
      intro i hi
      exact hn ⟨i,hi⟩
    obtain ⟨i,hi⟩ := hex
    have hlo : 124 ≤ i.val := by
      by_cases hn : i.val < 124
      · exact False.elim (ha ⟨i.val,hn⟩ hi)
      · omega
    have hk : i.val-124 < 4 := by have := i.isLt;omega
    have hh := ht ⟨i.val-124,hk⟩
    have hv : 124+(i.val-124) = i.val := by omega
    rw [hv,←hi] at hh
    exact hh

/-- The actual persistence and reply restoration after a successful apply. -/
theorem persist_full (B : Board) (c ca : Core) (ram ra : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (res : Spec.Success)
    (h : Pre B c ram p admin s cmd) (hpending : Pending c ca ram ra p s res) :
    ∃ d r, DetSteps B img 20 ⟨ca,ra⟩ ⟨d,r⟩ ∧ Post c d ram r p s (.ok res) ∧ TopSame p ra r := by
  have hmem : Memory.Block B (ca.get 2) 34 := by
    rw [hpending.sp]
    exact Memory.sub_block (B := B) (p := p) (n := 128) (off := 80) (m := 34) h.arena (by decide) (by decide)
  have hal : (ca.get 2).toNat % 4 = 0 := by rw [hpending.sp];exact Memory.word_aligned p 20 h.align
  have he : Memory.Block B (ca.get 23) 14 := by simpa only [hpending.enginePtr] using h.engineRam
  have hae : (ca.get 23).toNat % 4 = 0 := by simpa only [hpending.enginePtr] using h.engineAlign
  have hrel : ca.get 20 = ca.get 23+4#32 := by rw [hpending.statePtr,hpending.enginePtr]
  let rs := StateStore.result ra (ca.get 2) (ca.get 23)
  obtain ⟨cs,hrs,hpcs,hsps,hstates,hengs,hcsrs,hregss⟩ := StateStore.contract B ca ra hpending.pc hmem (by omega) he hae hrel
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
  obtain ⟨cr,hrr,hpcr,hspr,hstater,hengr,hcsrr⟩ := ReplyRestore.contract B cs rs hpcs hmemR halR
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
  refine ⟨cr,rr,hrs.trans hrr,?_,htop⟩
  refine ⟨hpcr,(hspr.trans hspS).trans h.sp.symm,
    (hstater.trans hstates).trans hpending.statePtr,(hengr.trans hengs).trans hpending.enginePtr,
    hcsrr.trans (hcsrs.trans hpending.csr),hstateR,hborrowR,hreplyR,?_⟩
  intro x hxArena hxEngine
  rw [hframeR x hxArena]
  exact (StateStore.frame ra (ca.get 2) (ca.get 23) x (by simpa only [hpending.enginePtr] using hxEngine)).trans (hpending.frame x hxArena)

theorem persist (B : Board) (c ca : Core) (ram ra : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (res : Spec.Success)
    (h : Pre B c ram p admin s cmd) (hpending : Pending c ca ram ra p s res) :
    ∃ d r, DetSteps B img 20 ⟨ca,ra⟩ ⟨d,r⟩ ∧ Post c d ram r p s (.ok res) := by
  obtain ⟨d,r,hr,hp,_⟩ := persist_full B c ca ram ra p admin s cmd res h hpending
  exact ⟨d,r,hr,hp⟩

/-- Refused commands release the borrow and leave the engine snapshot unchanged. -/
theorem rejected_full (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (err : Spec.Error)
    (h : Pre B c ram p admin s cmd) (hres : Spec.transition admin s cmd = .error err) :
    ∃ n d r, n ≤ 102 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Post c d ram r p s (.error err) ∧ TopSame p ram r := by
  obtain ⟨n0,c0,r0,hn0,hr0,hpc0,hsp0,hstate0,hcsr0,hout0,hsnap0,hframe0,hupper0,hfirst0,hreply0⟩ :=
    ShellExecute.contract_tight B c ram p admin s cmd h.toPre
  have heng0 : c0.get 23 = c.get 23 := hupper0 23 (by decide)
  have he : Memory.Block B (c0.get 23) 14 := by simpa only [heng0] using h.engineRam
  have hae : (c0.get 23).toNat % 4 = 0 := by simpa only [heng0] using h.engineAlign
  have hout : Outcome.At r0 (p+104#32) (.error err) := by rw [← hres];exact hout0
  have hborrow : ramRead r0 (c0.get 23) .w = 0xffffffff#32 := by
    rw [heng0]
    exact (word_frame (tight_weaken hframe0) h.engineSep).trans h.borrowed
  let rb := ReleaseBorrow.result r0 (c0.get 23)
  obtain ⟨d,hrb,hpcb,hspb,hstateb,hengb,hcsrb⟩ := ReleaseBorrow.contract B c0 r0
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
  refine ⟨n0+3,d,rb,by omega,hr0.trans hrb,?_,htop⟩
  refine ⟨hpcb,hspb.trans hsp0,hstateb.trans hstate0,hengb.trans heng0,
    hcsrb.trans hcsr0,hstate,hreleased,hreply,?_⟩
  intro x hxArena hxEngine
  exact (ReleaseBorrow.frame r0 (c0.get 23) x (by
    intro i
    rw [heng0]
    exact hxEngine ⟨i.val,by have := i.isLt;omega⟩)).trans (tight_weaken hframe0 x hxArena)

theorem rejected (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (err : Spec.Error)
    (h : Pre B c ram p admin s cmd) (hres : Spec.transition admin s cmd = .error err) :
    ∃ n d r, n ≤ 102 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Post c d ram r p s (.error err) := by
  obtain ⟨n,d,r,hn,hr,hp,_⟩ := rejected_full B c ram p admin s cmd err h hres
  exact ⟨n,d,r,hn,hr,hp⟩

/-- Complete concrete engine-body refinement for every typed command and actor.
    Success persists the computed state and reconstructs the original reply;
    errors preserve state. Both paths release the mutable borrow. -/
theorem contract_full (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram p admin s cmd) :
    ∃ n d r, n ≤ 171 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Post c d ram r p s (Spec.transition admin s cmd) ∧ TopSame p ram r := by
  cases hres : Spec.transition admin s cmd with
  | error err =>
    obtain ⟨n,d,r,hn,hr,hpost,htop⟩ := rejected_full B c ram p admin s cmd err h hres
    exact ⟨n,d,r,by omega,hr,hpost,htop⟩
  | ok res =>
    obtain ⟨n,ca,ra,hn,hr,hpending,htop0⟩ := prepare_full B c ram p admin s cmd res h hres
    obtain ⟨d,r,hr',hpost,htop1⟩ := persist_full B c ca ram ra p admin s cmd res h hpending
    exact ⟨n+20,d,r,by omega,hr.trans hr',hpost,top_trans htop0 htop1⟩

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram p admin s cmd) :
    ∃ n d r, n ≤ 171 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Post c d ram r p s (Spec.transition admin s cmd) := by
  obtain ⟨n,d,r,hn,hr,hp,_⟩ := contract_full B c ram p admin s cmd h
  exact ⟨n,d,r,hn,hr,hp⟩

def InvariantAt (ram : Word → BitVec 8) (eng : Word) : Prop :=
  ∃ s, Encoding.SnapshotAt ram (eng+4#32) s ∧ Spec.Inv s

/-- The invariant holds in the actual persisted RAM, not just a source commit. -/
theorem contract_inv (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram p admin s cmd)
    (hi : Spec.Inv s) :
    ∃ n d r, n ≤ 171 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Post c d ram r p s (Spec.transition admin s cmd) ∧ InvariantAt r (c.get 23) := by
  obtain ⟨n,d,r,hn,hr,hpost⟩ := contract B c ram p admin s cmd h
  exact ⟨n,d,r,hn,hr,hpost,Spec.commit s (Spec.transition admin s cmd),hpost.state,Spec.commit_inv admin s cmd hi⟩
end E5R.Thermostat.Engine
