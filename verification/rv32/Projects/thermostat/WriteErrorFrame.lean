import Projects.thermostat.WriteBodyIO
import Projects.thermostat.WriteErrorTail
import Projects.thermostat.ResponseLiterals
import Projects.thermostat.JsonCapacity
namespace E5R.Thermostat.WriteErrorFrame
open E5R E5R.Thermostat

/-- Complete fresh write-handler execution through an actual kernel refusal,
    exact error JSON/status, completion flags and real saved-register return. -/
theorem contract_inv (c : Core) (ram : Word → BitVec 8) (p f out req eng rawPtr pathPtr bodyPtr dst : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (cap : Nat) (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (err : Spec.Error)
    (h : WriteInput.Pre UartPlatform.board c ram (p+240#32) f out req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
    (hdecode : WireSpec.decode path body first = .ok cmd) (hres : Spec.transition admin s cmd = .error err) (hi : Spec.Inv s)
    (hm : Memory.Block UartPlatform.board p 416) (ha : p.toNat%4=0)
    (hcap : ramRead ram (f+16#32) .w = BitVec.ofNat 32 cap) (hptr : ramRead ram (f+12#32) .w = dst)
    (hc : cap<2^32) (hlen : 33≤cap) (hd : Memory.Block UartPlatform.board dst cap) (hw : dst.toNat+cap<2^32) (hda : dst.toNat%4=0)
    (ho : Memory.Block UartPlatform.board out 15) (hoa : out.toNat%4=0)
    (hds : WordRegions.Disjoint dst cap p 416) (hos : WordRegions.Disjoint out 15 p 416) (hfs : WordRegions.Disjoint f 41 p 416)
    (hof : WordRegions.Disjoint out 15 f 41) (hdo : WordRegions.Disjoint dst cap out 15) (hdf : WordRegions.Disjoint dst cap f 41)
    (hes : WordRegions.Disjoint eng 25 p 416) (hed : WordRegions.Disjoint eng 25 dst cap) (heo : WordRegions.Disjoint eng 25 out 15) :
    ∃ d n r, n ≤ 212*entries.length+18*body.length+865 ∧ DetSteps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      FormatCursor.Returned c d ∧
      BodyMemory.At r out 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.errorBody err).length) (ErrorLiterals.status err) ∧
      Bytes.Span UartPlatform.board r dst (ReplyJson.errorBody err) ∧
      Encoding.SnapshotAt r (eng+4#32) (Spec.commit s (.error err)) ∧ ramRead r eng .w = 0#32 ∧ Engine.InvariantAt r eng ∧
      r (f+36#32)=1#8 ∧ r (f+40#32)=1#8 ∧
      ReadBytes.Span UartPlatform.board img r 0x800056a8#32 (WireSpec.ascii "application/json") ∧
      (∀ x, (∀ i : Fin 416, x ≠ p+BitVec.ofNat 32 i.val) → (∀ i : Fin cap, x ≠ dst+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 15, x ≠ out+BitVec.ofNat 32 i.val) → (∀ i : Fin 41, x ≠ f+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 14, x ≠ eng+BitVec.ofNat 32 i.val) → r x = ram x) := by
  obtain ⟨na,a,ra,hna,ta,hpost,_,a8,a9,a19,a18,a22,herr⟩ := WriteBody.contract_io UartPlatform.board c ram (p+240#32)
    f out req eng rawPtr pathPtr bodyPtr raw path body entries first admin s cmd h hallow hdecode hi
    (AuthLiterals.header _) (AuthLiterals.bearer _) (AuthLiterals.key _)
  have apc : a.pc = 0x80000652#32 := by simpa only [hres,Engine.endPc,show (0x80000652:Word)=0x80000652#32 by decide +kernel] using hpost.pc
  have asp : a.get 2 = p+320#32 := by
    simpa only [BitVec.add_assoc,show (240#32+80#32)=320#32 by decide +kernel] using hpost.sp
  obtain ⟨d,nb,r,hnb,tb,dpc,dsp,dc,dsaved,dresponse,dbytes,h36,h40,fr⟩ :=
    WriteErrorTail.contract a ra p dst out f cap err apc asp a8 a9 (a19.trans hptr) (a18.trans hcap) a22
      hm ha (herr err hres) hc hd hw hda ho hoa h.futureBlock hds hos hfs hof hdo hdf hlen
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
  have hstate : Encoding.SnapshotAt r (eng+4#32) (Spec.commit s (.error err)) := by
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
  have hinv : Engine.InvariantAt r eng := ⟨Spec.commit s (.error err),hstate,by
    have hh := Spec.commit_inv admin s cmd hi
    simpa only [hres] using hh⟩
  have hra : ramRead ra (a.get 2+92#32) .w = c.get 1 := (saved 92 (by decide) (by decide)).trans hsave.1
  refine ⟨d,na+nb,r,by omega,ta.trans tb,?_,dresponse,dbytes,hstate,hborrow,hinv,h36,h40,ResponseLiterals.json r,?_⟩
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
end E5R.Thermostat.WriteErrorFrame
