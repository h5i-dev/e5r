import Projects.thermostat.RequestRefusal
import Projects.thermostat.WriteInput
import Projects.thermostat.AuthLiterals
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WriteRefusal
open E5R E5R.Thermostat

structure Returned (c d : Core) : Prop where
  pc : d.pc = c.get 1 &&& ~~~1
  sp : d.get 2 = c.get 2
  csr : d.sameCsr c
  x1 : d.get 1 = c.get 1
  x8 : d.get 8 = c.get 8
  x9 : d.get 9 = c.get 9
  x18 : d.get 18 = c.get 18
  x19 : d.get 19 = c.get 19
  x20 : d.get 20 = c.get 20
  x21 : d.get 21 = c.get 21
  x22 : d.get 22 = c.get 22
  x23 : d.get 23 = c.get 23
  x24 : d.get 24 = c.get 24
  x25 : d.get 25 = c.get 25
  x26 : d.get 26 = c.get 26
  x27 : d.get 27 = c.get 27

/-- Fresh actual write-handler call with refused Request authentication returns
    a concrete empty401 Response, unchanged snapshot/freeborrow, all caller saves. -/
theorem contract_inv (c : Core) (ram : Word → BitVec 8) (p f out req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot)
    (h : WriteInput.Pre UartPlatform.board c ram p f out req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hdeny : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = false)
    (hi : Spec.Inv s) (ho : Memory.Block UartPlatform.board out 15) (hoa : out.toNat%4 = 0)
    (hso : WordRegions.Disjoint (p+80#32) 96 out 15) (hof : WordRegions.Disjoint out 15 f 41)
    (heo : WordRegions.Disjoint eng 25 out 15) :
    ∃ d n r, n ≤ 212*entries.length+202 ∧ DetSteps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Returned c d ∧ StatusMemory.At r out 401#32 ∧ Encoding.SnapshotAt r (eng+4#32) s ∧
      ramRead r eng .w = 0#32 ∧ Engine.InvariantAt r eng ∧ r (f+36#32) = 1#8 ∧ r (f+40#32) = 1#8 := by
  let r0 := WriteStart.memory ram (p+80#32) f c
  obtain ⟨a,ta,ha,a8,a9,_,_,acsr⟩ := WriteInput.establishes h
  obtain ⟨d,n,hn,td,dpc,dsp,dcsr,dsaved,dresponse,ds,db,di⟩ := RequestRefusal.contract_inv UartPlatform.board a r0
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
  refine ⟨d,31+n,RequestRefusal.memory r0 (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries),
    by omega,ta.trans td,?_,dresponse,ds,db,di,
    (StatusMemory.flags _ out f 401#32).1,(StatusMemory.flags _ out f 401#32).2⟩
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
theorem closed_contract_inv (c : Core) (ram : Word → BitVec 8) (p f out req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot)
    (h : WriteInput.Pre UartPlatform.board c ram p f out req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hdeny : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = false)
    (hi : Spec.Inv s) (ho : Memory.Block UartPlatform.board out 15) (hoa : out.toNat%4 = 0)
    (hso : WordRegions.Disjoint (p+80#32) 96 out 15) (hof : WordRegions.Disjoint out 15 f 41)
    (heo : WordRegions.Disjoint eng 25 out 15) (hm : c.mie_ = false) :
    ∃ d n r, n ≤ 212*entries.length+202 ∧ Trace.Closed UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Returned c d ∧ StatusMemory.At r out 401#32 ∧ Encoding.SnapshotAt r (eng+4#32) s ∧
      ramRead r eng .w = 0#32 ∧ Engine.InvariantAt r eng ∧ r (f+36#32) = 1#8 ∧ r (f+40#32) = 1#8 := by
  obtain ⟨d,n,r,hn,ht,hret,hr,hs,hb,hi,h36,h40⟩ := contract_inv c ram p f out req eng rawPtr pathPtr bodyPtr raw path body entries first admin s h hdeny hi ho hoa hso hof heo
  exact ⟨d,n,r,hn,Interrupt.close ht hm,hret,hr,hs,hb,hi,h36,h40⟩
end E5R.Thermostat.WriteRefusal
