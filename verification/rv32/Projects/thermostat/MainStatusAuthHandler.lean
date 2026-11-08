-- G5 actual main write-handler auth-refusal frame, needed by the sender join.
import Projects.thermostat.MainStatusHandlersQuiet
import Projects.thermostat.MainWritePost
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.MainStatusAuthHandler
open E5R E5R.Thermostat
abbrev p : Word := 0x80ffeae0#32
abbrev f : Word := 0x80fffa2c#32
abbrev out : Word := 0x80fffd38#32
theorem contract (c : Core) (ram : Word → BitVec 8) (req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot)
    (h : WriteInput.Pre UartPlatform.board c ram p f out req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hdeny : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = false)
    (hi : Spec.Inv s) (ho : Memory.Block UartPlatform.board out 15) (hoa : out.toNat%4 = 0)
    (hso : WordRegions.Disjoint (p+80#32) 96 out 15) (hof : WordRegions.Disjoint out 15 f 41)
    (heo : WordRegions.Disjoint eng 25 out 15) :
    ∃ d n r, n ≤ 212*entries.length+202 ∧ Quiet.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      WriteRefusal.Returned c d ∧ StatusMemory.At r out 401#32 ∧ Encoding.SnapshotAt r (eng+4#32) s ∧
      ramRead r eng .w = 0#32 ∧ Engine.InvariantAt r eng ∧ r (f+36#32) = 1#8 ∧ r (f+40#32) = 1#8 ∧ MainWritePost.Frame ram r := by
  let r0 := WriteStart.memory ram (p+80#32) f c
  obtain ⟨a,ta,ha,a8,a9,_,_,acsr⟩ := E5R.Thermostat.WriteInput.establishes_quiet h
  obtain ⟨d,n,hn,td,dpc,dsp,dcsr,dsaved,dresponse,ds,db,di⟩ := E5R.Thermostat.RequestRefusal.contract_inv_quiet UartPlatform.board a r0
    p req eng rawPtr pathPtr bodyPtr out f raw path body entries first admin s ha a8 a9
    (AuthLiterals.header _) (AuthLiterals.bearer _) (AuthLiterals.key _) hdeny hi ho hoa h.futureBlock h.stack hso
    (WordRegions.symm h.futureSeparate) hof heo h.appAvoid.2
  have hword (k : Nat) (hk : k+4 ≤ 96) :
      ramRead r0 (a.get 2+BitVec.ofNat 32 k) .w = ramRead (OuterSave.memory ram (p+80#32) c) ((p+80#32)+BitVec.ofNat 32 k) .w := by
    rw [ha.sp]
    exact ViewFrame.word (WriteStart.saved_region ram (p+80#32) f c h.futureSeparate) k hk
  have hs := OuterSave.saved ram (p+80#32) c
  have hra : ramRead r0 ((p+80#32)+92#32) .w = c.get 1 :=
    (ViewFrame.word (WriteStart.saved_region ram (p+80#32) f c h.futureSeparate) 92 (by decide)).trans hs.1
  have fullFrame : MainWritePost.Frame ram
      (RequestRefusal.memory r0 (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)) := by
    intro x hstack _ hout hfuture _
    have stackAddr (j : Fin 96) : (p+80#32)+BitVec.ofNat 32 j.val=0x80ffe9f0#32+BitVec.ofNat 32 (320+j.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc]
      rfl
    have authApart : x≠(p+80#32)+24#32 := by
      simpa only [show 0x80ffe9f0#32+BitVec.ofNat 32 (344 : Nat)=(p+80#32)+24#32 by decide +kernel] using hstack ⟨344,by decide⟩
    unfold RequestRefusal.memory
    rw [StatusMemory.frame (RequestAuth.memory r0 (p+80#32) (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)) out f 401#32 x hout hfuture]
    rw [RequestAuth.memory_frame r0 (p+80#32) x _ authApart]
    apply WriteStart.frame
    · intro j
      rw [stackAddr]
      exact hstack ⟨320+j.val,by have := j.isLt;omega⟩
    · intro j
      exact hfuture ⟨20+j.val,by have := j.isLt;omega⟩
  refine ⟨d,31+n,RequestRefusal.memory r0 (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries),
    by omega,ta.trans td,?_,dresponse,ds,db,di,
    (StatusMemory.flags _ out f 401#32).1,(StatusMemory.flags _ out f 401#32).2,fullFrame⟩
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
end E5R.Thermostat.MainStatusAuthHandler
