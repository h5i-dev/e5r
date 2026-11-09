import Projects.thermostat.RelayPrefixScan
import Projects.thermostat.RelayCaptureTail
import Projects.thermostat.RouteMatcherStart
import Projects.thermostat.RouteSpec
set_option autoImplicit false
namespace E5R.Thermostat.RouteRelayBody
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (params : Word) (path : List (BitVec 8)) :=
  if path.take 7=WireSpec.ascii "/relay/" then RelayCaptureTail.memory ram params (path.drop 7) else ram

def count (path : List (BitVec 8)) : Word :=
  if path.take 7=WireSpec.ascii "/relay/" then
    if RoutePathScan.length (path.drop 7)=0 then 0#32 else 1#32
  else 0#32

def Frame (c d : Core) : Prop :=
  ∀ r : Reg,r≠1 → (r.val<8 ∨ (14<r.val ∧ r.val<18) ∨ 27<r.val) → d.get r=c.get r

/-- Complete matcher body for the actual relay pattern, on arbitrary received
    slash-prefixed paths. Match and exact capture RAM derive from path bytes. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (path params : Word) (ys : List (BitVec 8))
    (pattern : ReadBytes.Span B img ram 0x80005b9c#32 (WireSpec.ascii "/relay/{i}"))
    (span : Bytes.Span B ram path (47#8::ys)) (bound : (47#8::ys).length≤2048)
    (block : Memory.Block B params 8) (aligned : params.toNat%4=0)
    (pc : c.pc=0x80002856#32) (h10 : c.get 10=0x80005b9c#32) (h11 : c.get 11=10#32)
    (h12 : c.get 12=path) (h13 : c.get 13=BitVec.ofNat 32 (47#8::ys).length) (h14 : c.get 14=params) :
    ∃ n d,n≤15*ys.length+210 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,memory ram params (47#8::ys)⟩ ∧
      d.pc=0x8000293a#32 ∧ d.get 10=(if RouteSpec.relayPath (47#8::ys) then 1#32 else 0#32) ∧
      d.get 11=count (47#8::ys) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,a19,a9,a20,a18,a21,a8,a10,a11,a24,a25,a26,a27,a22,ar,ac⟩ := RouteMatcherStart.contract B c ram 0x80005b9c#32
    10#32 path (BitVec.ofNat 32 (47#8::ys).length) params h10 h11 h12 h13 h14 pc
  obtain ⟨np,b,npb,tb,pb,b22,b11,b10,b23,br,bc⟩ := RouteLiteralLeading.contract B a ram 0x80005b9c#32 path 114#8
    (WireSpec.ascii "elay/{i}") ys 0#32 pattern span (by decide) bound pa a21 a22 a18 a11 a20 a10 a9 a24 a25 a26
  have keepB (r : Reg) (n1 : r≠1) (n22 : r≠22) (n23 : r≠23) (out : r.val<10 ∨ 14<r.val) : b.get r=a.get r := br r n1 n22 n23 out
  obtain ⟨nk,e,nkb,te,pe,er,ec⟩ := RelayPrefixScan.contract B b ram path ys pattern (Bytes.tail span) (by simpa only [List.length_cons,Nat.add_comm] using bound)
    pb ((keepB 21 (by decide) (by decide) (by decide) (by decide)).trans a21) b22
    ((keepB 18 (by decide) (by decide) (by decide) (by decide)).trans a18) b11
    ((keepB 20 (by decide) (by decide) (by decide) (by decide)).trans a20) b10
    (by simpa only [List.length_cons,Nat.add_comm] using (keepB 9 (by decide) (by decide) (by decide) (by decide)).trans a9)
    ((keepB 24 (by decide) (by decide) (by decide) (by decide)).trans a24)
    ((keepB 25 (by decide) (by decide) (by decide) (by decide)).trans a25)
    ((keepB 26 (by decide) (by decide) (by decide) (by decide)).trans a26)
    ((keepB 8 (by decide) (by decide) (by decide) (by decide)).trans a8)
  have keepE (r : Reg) (n1 : r≠1) (n10 : r≠10) (n11 : r≠11) (n12 : r≠12) (n13 : r≠13) (n14 : r≠14) (n22 : r≠22) (n23 : r≠23)
      (out : r.val<10 ∨ 14<r.val) : e.get r=a.get r :=
    (er r n1 n10 n11 n12 n13 n14 n22 n23).trans (keepB r n1 n22 n23 out)
  have startFrame : Frame c a := by
    intro r n1 outside
    exact ar r (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega)
      (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega)
      (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega)
      (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega)
  have frameE : Frame c e := by
    intro r n1 outside
    exact (keepE r n1 (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega)
      (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega) (by omega)).trans (startFrame r n1 outside)
  have csrE : e.sameCsr c := ec.trans (bc.trans ac)
  by_cases prefixOk : (47#8::ys).take 7=WireSpec.ascii "/relay/"
  · have ep : e.pc=0x8000287a#32 ∧ e.get 22=7#32 ∧ e.get 11=7#32 ∧ e.get 10=7#32 := by simpa only [prefixOk,ite_true] using pe
    obtain ⟨rest,whole,restEq⟩ := RouteScanSpec.relay_decompose ys (RouteScanSpec.relay_known ys prefixOk).1 (RouteScanSpec.relay_known ys prefixOk).2
    have dropEq : (47#8::ys).drop 7=rest := by rw [whole];rfl
    have suffixSpan : Bytes.Span B ram (path+7#32) rest := by
      rw [whole] at span
      have view := Bytes.tail (Bytes.tail (Bytes.tail (Bytes.tail (Bytes.tail (Bytes.tail (Bytes.tail span))))))
      change Bytes.Span B ram (path+1#32+1#32+1#32+1#32+1#32+1#32+1#32) rest at view
      simpa only [BitVec.add_assoc,show 1#32+(1#32+(1#32+(1#32+(1#32+(1#32+1#32)))))=7#32 by decide +kernel] using view
    have restBound : 7+rest.length≤2048 := by rw [whole,List.length_append] at bound;exact bound
    obtain ⟨nt,d,ntb,td,pd,d10,d11,dr,dc⟩ := RelayCaptureTail.contract B e ram path params rest pattern suffixSpan restBound block aligned ep.1
      ((keepE 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a21) ep.2.1
      ((keepE 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a18) ep.2.2.1
      ((keepE 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a20) ep.2.2.2
      (by rw [whole,List.length_append] at a9;exact (keepE 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a9)
      ((keepE 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a24)
      ((keepE 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a25)
      ((keepE 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a26)
      ((keepE 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a27)
      ((keepE 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a8)
      ((keepE 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a19)
    have lengths : 7+rest.length=1+ys.length := by have h := congrArg List.length whole;rw [List.length_cons,List.length_append] at h;change ys.length+1=7+rest.length at h;omega
    refine ⟨13+np+nk+nt,d,by simp only [List.length_cons] at npb;omega,?_,pd,?_,?_,?_,dc.trans csrE⟩
    · simpa only [memory,prefixOk,ite_true,dropEq] using ((ta.trans tb).trans te).trans td
    · simpa only [RouteSpec.relayPath,prefixOk,dropEq,true_and,RelayCaptureTail.accepted] using d10
    · simpa only [count,prefixOk,ite_true,dropEq] using d11
    · intro r n1 outside
      exact (dr r (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega)
        (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega)).trans (frameE r n1 outside)
  · have ep : e.pc=0x8000293a#32 ∧ e.get 10=0#32 ∧ e.get 11=0#32 := by simpa only [prefixOk,ite_false] using pe
    refine ⟨13+np+nk,e,by simp only [List.length_cons] at npb;omega,?_,ep.1,?_,?_,frameE,csrE⟩
    · simpa only [memory,prefixOk,ite_false] using (ta.trans tb).trans te
    · simpa only [RouteSpec.relayPath,prefixOk,false_and,ite_false] using ep.2.1
    · simpa only [count,prefixOk,ite_false] using ep.2.2
end E5R.Thermostat.RouteRelayBody
