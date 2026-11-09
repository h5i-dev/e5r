import Projects.thermostat.MainFutureDecodeHandler
import Projects.thermostat.StackStaticViews
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.StackMainFutureDecodeHandler
open E5R E5R.Thermostat MainFutureDecodeHandler
theorem contract (c : Core) (ram : Word → BitVec 8) (f : Word) (req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (status : Nat)
    (h : WriteInput.Pre StackBoard.board c ram p f out req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
    (hdecode : WireSpec.decode path body first = .error status)
    (hi : Spec.Inv s) (ho : Memory.Block StackBoard.board out 15) (hoa : out.toNat%4 = 0)
    (hso : WordRegions.Disjoint (p+80#32) 96 out 15) (hof : WordRegions.Disjoint out 15 f 41)
    (heo : WordRegions.Disjoint eng 25 out 15) :
    ∃ d n r, n ≤ 212*entries.length+18*body.length+514 ∧ Quiet.Steps StackBoard.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      WriteRefusal.Returned c d ∧ StatusMemory.At r out (BitVec.ofNat 32 status) ∧ Encoding.SnapshotAt r (eng+4#32) s ∧
      ramRead r eng .w = 0#32 ∧ Engine.InvariantAt r eng ∧ r (f+36#32) = 1#8 ∧ r (f+40#32) = 1#8 ∧ MainFutureFrame.At f ram r := by
  let r0 := WriteStart.memory ram (p+80#32) f c
  obtain ⟨a,ta,ha,a8,a9,_,_,acsr⟩ := E5R.Thermostat.WriteInput.establishes_quiet h
  obtain ⟨d,n,r,hn,td,dpc,dsp,dcsr,dsaved,dresponse,ds,db,di,dflag36,dflag40,innerFrame⟩ := MainFutureDecodeInner.contract StackBoard.board a r0 f
    req eng rawPtr pathPtr bodyPtr raw path body entries first admin s status ha a8 a9
    (StackStaticViews.auth_header _) (StackStaticViews.auth_bearer _) (StackStaticViews.auth_key _) hallow hdecode hi ho hoa h.futureBlock h.stack hso
    (WordRegions.symm h.futureSeparate) hof heo h.appAvoid.2
  have hword (k : Nat) (hk : k+4 ≤ 96) :
      ramRead r0 (a.get 2+BitVec.ofNat 32 k) .w = ramRead (OuterSave.memory ram (p+80#32) c) ((p+80#32)+BitVec.ofNat 32 k) .w := by
    rw [ha.sp]
    exact ViewFrame.word (WriteStart.saved_region ram (p+80#32) f c h.futureSeparate) k hk
  have hs := OuterSave.saved ram (p+80#32) c
  have hra : ramRead r0 ((p+80#32)+92#32) .w = c.get 1 :=
    (ViewFrame.word (WriteStart.saved_region ram (p+80#32) f c h.futureSeparate) 92 (by decide)).trans hs.1
  have startFrame : MainFutureFrame.At f ram r0 := by
    intro x hstack _ _ hfuture _
    apply WriteStart.frame
    · intro j
      have address : (p+80#32)+BitVec.ofNat 32 j.val=0x80ffe9f0#32+BitVec.ofNat 32 (320+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc]
        rfl
      rw [address]
      exact hstack ⟨320+j.val,by have := j.isLt;omega⟩
    · intro j
      exact hfuture ⟨20+j.val,by have := j.isLt;omega⟩
  have fullFrame : MainFutureFrame.At f ram r := by
    intro x hstack hdst hout hfuture heng
    exact (innerFrame x hstack hdst hout hfuture heng).trans (startFrame x hstack hdst hout hfuture heng)
  refine ⟨d,31+n,r,
    by omega,ta.trans td,?_,dresponse,ds,db,di,dflag36,dflag40,fullFrame⟩
  refine ⟨by rw [dpc,hra],dsp.trans h.sp.symm,dcsr.trans acsr,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact dsaved.x1 |>.trans ((hword 92 (by decide)).trans hs.1)
  · exact dsaved.x8 |>.trans ((hword 88 (by decide)).trans hs.2.1)
  · exact dsaved.x9 |>.trans ((hword 84 (by decide)).trans hs.2.2.1)
  · exact dsaved.x18 |>.trans ((hword 80 (by decide)).trans hs.2.2.2.1)
  · exact dsaved.x19 |>.trans ((hword 76 (by decide)).trans hs.2.2.2.2.1)
  · exact dsaved.x20 |>.trans ((hword 72 (by decide)).trans hs.2.2.2.2.2.1)
  · exact dsaved.x21 |>.trans ((hword 68 (by decide)).trans hs.2.2.2.2.2.2.1)
  · exact dsaved.x22 |>.trans ((hword 64 (by decide)).trans hs.2.2.2.2.2.2.2.1)
  · exact dsaved.x23 |>.trans ((hword 60 (by decide)).trans hs.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x24 |>.trans ((hword 56 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x25 |>.trans ((hword 52 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x26 |>.trans ((hword 48 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x27 |>.trans ((hword 44 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.2.2.2)
end E5R.Thermostat.StackMainFutureDecodeHandler
