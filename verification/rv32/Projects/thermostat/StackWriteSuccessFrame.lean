import Projects.thermostat.WriteSuccessFrameQuiet
import Projects.thermostat.StackStaticViews
import Projects.thermostat.StackWriteSuccessTail
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.StackWriteSuccessFrame
open E5R E5R.Thermostat WriteSuccessFrame
theorem contract_inv_quiet (c : Core) (ram : Word → BitVec 8) (p f out req eng rawPtr pathPtr bodyPtr dst : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (cap : Nat) (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (res : Spec.Success)
    (h : WriteInput.Pre StackBoard.board c ram (p+240#32) f out req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
    (hdecode : WireSpec.decode path body first = .ok cmd) (hres : Spec.transition admin s cmd = .ok res) (hi : Spec.Inv s)
    (hm : Memory.Block StackBoard.board p 416) (ha : p.toNat%4=0)
    (hcap : ramRead ram (f+16#32) .w = BitVec.ofNat 32 cap) (hptr : ramRead ram (f+12#32) .w = dst)
    (hc : cap<2^32) (hlen : 103≤cap) (hd : Memory.Block StackBoard.board dst cap) (hw : dst.toNat+cap<2^32)
    (ho : Memory.Block StackBoard.board out 15) (hoa : out.toNat%4=0)
    (hds : WordRegions.Disjoint dst cap p 416) (hos : WordRegions.Disjoint out 15 p 416) (hfs : WordRegions.Disjoint f 41 p 416)
    (hof : WordRegions.Disjoint out 15 f 41) (hdo : WordRegions.Disjoint dst cap out 15) (hdf : WordRegions.Disjoint dst cap f 41)
    (hes : WordRegions.Disjoint eng 25 p 416) (hed : WordRegions.Disjoint eng 25 dst cap) (heo : WordRegions.Disjoint eng 25 out 15) :
    ∃ d n r, n ≤ 212*entries.length+18*body.length+4595 ∧ Quiet.Steps StackBoard.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      FormatCursor.Returned c d ∧
      BodyMemory.At r out 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.snapshot res.reply).length) 200#32 ∧
      Bytes.Span StackBoard.board r dst (ReplyJson.snapshot res.reply) ∧
      Encoding.SnapshotAt r (eng+4#32) (Spec.commit s (.ok res)) ∧ ramRead r eng .w = 0#32 ∧ Engine.InvariantAt r eng ∧
      r (f+36#32)=1#8 ∧ r (f+40#32)=1#8 ∧
      ReadBytes.Span StackBoard.board img r 0x800056a8#32 (WireSpec.ascii "application/json") ∧
      (∀ x, (∀ i : Fin 416, x ≠ p+BitVec.ofNat 32 i.val) → (∀ i : Fin cap, x ≠ dst+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 15, x ≠ out+BitVec.ofNat 32 i.val) → (∀ i : Fin 41, x ≠ f+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 14, x ≠ eng+BitVec.ofNat 32 i.val) → r x = ram x) := by
  obtain ⟨na,a,ra,hna,ta,hpost,_,a8,a9,a19,a18,a22,_⟩ := E5R.Thermostat.WriteBody.contract_io_quiet StackBoard.board c ram (p+240#32)
    f out req eng rawPtr pathPtr bodyPtr raw path body entries first admin s cmd h hallow hdecode hi
    (StackStaticViews.auth_header _) (StackStaticViews.auth_bearer _) (StackStaticViews.auth_key _)
  have apc : a.pc = 0x80000736#32 := by simpa only [hres,Engine.endPc,show (0x80000736:Word)=0x80000736#32 by decide +kernel] using hpost.pc
  have asp : a.get 2 = p+320#32 := by
    simpa only [BitVec.add_assoc,show (240#32+80#32)=320#32 by decide +kernel] using hpost.sp
  have hreply : Encoding.SnapshotAt ra (p+344#32) res.reply := by
    have hh := hpost.reply
    simpa only [hres,Engine.ReplyAt,BitVec.add_assoc,show (240#32+104#32)=344#32 by decide +kernel] using hh
  have hfit : (ReplyJson.snapshot res.reply).length ≤ cap := Nat.le_trans (JsonCapacity.snapshot_length res.reply) hlen
  obtain ⟨d,nb,r,hnb,tb,dpc,dsp,dc,dsaved,dresponse,dbytes,h36,h40,fr⟩ :=
    E5R.Thermostat.StackWriteSuccessTail.contract_quiet a ra p dst out f cap res.reply apc asp a8 a9 (a19.trans hptr) (a18.trans hcap) a22
      hm ha hreply hc hd hw ho hoa h.futureBlock hds hos hfs hof hdo hdf hfit
  have hsave := OuterSave.saved ram ((p+240#32)+80#32) c
  have saved (off : Nat) (hlo : 44≤off) (hhi : off+4≤96) :
      ramRead ra (a.get 2+BitVec.ofNat 32 off) .w =
        ramRead (OuterSave.memory ram ((p+240#32)+80#32) c) (((p+240#32)+80#32)+BitVec.ofNat 32 off) .w := by
    have hh := ViewFrame.word hpost.saved (off-44) (by omega)
    have he : (((p+240#32)+80#32)+44#32)+BitVec.ofNat 32 (off-44) = ((p+240#32)+80#32)+BitVec.ofNat 32 off := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add,show 44+(off-44)=off by omega]
    rw [he] at hh
    have hasp : a.get 2 = (p+240#32)+80#32 := hpost.sp
    rw [hasp];exact hh
  have hstate : Encoding.SnapshotAt r (eng+4#32) (Spec.commit s (.ok res)) := by
    intro i
    have hbyte := fr ((eng+4#32)+BitVec.ofNat 32 i.val)
      (by simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hes ⟨4+i.val,by have := i.isLt;omega⟩)
      (by simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hed ⟨4+i.val,by have := i.isLt;omega⟩)
      (by simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using heo ⟨4+i.val,by have := i.isLt;omega⟩)
      (by simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using h.appAvoid.2 ⟨4+i.val,by have := i.isLt;omega⟩)
    rw [hbyte]
    simpa only [hres] using hpost.state i
  have hborrow : ramRead r eng .w = 0#32 := by
    have hr : ViewFrame.Region ra r eng 4 := by
      intro i
      exact fr _ (hes ⟨i.val,by have := i.isLt;omega⟩) (hed ⟨i.val,by have := i.isLt;omega⟩)
        (heo ⟨i.val,by have := i.isLt;omega⟩) (h.appAvoid.2 ⟨i.val,by have := i.isLt;omega⟩)
    have hh := ViewFrame.word hr 0 (by decide)
    simp only [BitVec.add_zero] at hh
    exact hh.trans hpost.released
  have hinv : Engine.InvariantAt r eng := ⟨Spec.commit s (.ok res),hstate,by
    have hh := Spec.commit_inv admin s cmd hi
    simpa only [hres] using hh⟩
  have hra : ramRead ra (a.get 2+92#32) .w = c.get 1 := (saved 92 (by decide) (by decide)).trans hsave.1
  refine ⟨d,na+nb,r,by omega,ta.trans tb,?_,dresponse,dbytes,hstate,hborrow,hinv,h36,h40,StackStaticViews.json r,?_⟩
  · refine ⟨by rw [dpc,hra],?_,dc.trans hpost.csr,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · have hsp := h.sp
      rw [BitVec.add_assoc,BitVec.add_assoc,show (80#32+96#32)=176#32 by decide +kernel,
        show (240#32+176#32)=416#32 by decide +kernel] at hsp
      exact dsp.trans hsp.symm
    · exact dsaved.x1 |>.trans ((saved 92 (by decide) (by decide)).trans hsave.1)
    · exact dsaved.x8 |>.trans ((saved 88 (by decide) (by decide)).trans hsave.2.1)
    · exact dsaved.x9 |>.trans ((saved 84 (by decide) (by decide)).trans hsave.2.2.1)
    · exact dsaved.x18 |>.trans ((saved 80 (by decide) (by decide)).trans hsave.2.2.2.1)
    · exact dsaved.x19 |>.trans ((saved 76 (by decide) (by decide)).trans hsave.2.2.2.2.1)
    · exact dsaved.x20 |>.trans ((saved 72 (by decide) (by decide)).trans hsave.2.2.2.2.2.1)
    · exact dsaved.x21 |>.trans ((saved 68 (by decide) (by decide)).trans hsave.2.2.2.2.2.2.1)
    · exact dsaved.x22 |>.trans ((saved 64 (by decide) (by decide)).trans hsave.2.2.2.2.2.2.2.1)
    · exact dsaved.x23 |>.trans ((saved 60 (by decide) (by decide)).trans hsave.2.2.2.2.2.2.2.2.1)
    · exact dsaved.x24 |>.trans ((saved 56 (by decide) (by decide)).trans hsave.2.2.2.2.2.2.2.2.2.1)
    · exact dsaved.x25 |>.trans ((saved 52 (by decide) (by decide)).trans hsave.2.2.2.2.2.2.2.2.2.2.1)
    · exact dsaved.x26 |>.trans ((saved 48 (by decide) (by decide)).trans hsave.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact dsaved.x27 |>.trans ((saved 44 (by decide) (by decide)).trans hsave.2.2.2.2.2.2.2.2.2.2.2.2)
  · intro x hx hdst hout hfuture heng
    rw [fr x hx hdst hout hfuture]
    apply hpost.frame x
    · intro i
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨240+i.val,by have := i.isLt;omega⟩
    · exact hfuture
    · intro i
      exact heng ⟨i.val,by have := i.isLt;omega⟩

end E5R.Thermostat.StackWriteSuccessFrame
