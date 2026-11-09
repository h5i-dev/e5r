import Projects.thermostat.RouteMatcherStart
import Projects.thermostat.RouteLiteralLeading
set_option autoImplicit false
namespace E5R.Thermostat.RouteLiteralBody
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop :=
  ∀ r : Reg, r≠1 → (r.val<8 ∨ (14<r.val ∧ r.val<18) ∨ 27<r.val) → d.get r=c.get r

/-- Generic actual matcher body for each fixed literal route, for every
    allocated slash-prefixed path. The parser's leading-slash obligation is
    explicit here and must be discharged when connecting received requests. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (pattern path params : Word) (first : BitVec 8) (rest ys : List (BitVec 8))
    (patSpan : ReadBytes.Span B img ram pattern (47#8::first::rest))
    (pathSpan : Bytes.Span B ram path (47#8::ys))
    (plain : ∀ b∈first::rest,b≠47#8) (literal : first≠123#8)
    (patBound : (47#8::first::rest).length≤2048) (pathBound : (47#8::ys).length≤2048)
    (hp : c.pc=0x80002856#32) (h10 : c.get 10=pattern)
    (h11 : c.get 11=BitVec.ofNat 32 (47#8::first::rest).length) (h12 : c.get 12=path)
    (h13 : c.get 13=BitVec.ofNat 32 (47#8::ys).length) (h14 : c.get 14=params) :
    ∃ n d, n≤12*(first::rest).length+10*ys.length+78 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=0x8000293a#32 ∧ d.get 10=(if first::rest=ys then 1#32 else 0#32) ∧ d.get 11=0#32 ∧
      Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,a19,a9,a20,a18,a21,a8,a10,a11,a24,a25,a26,a27,a22,ar,ac⟩ := RouteMatcherStart.contract B c ram pattern
    (BitVec.ofNat 32 (47#8::first::rest).length) path (BitVec.ofNat 32 (47#8::ys).length) params h10 h11 h12 h13 h14 hp
  obtain ⟨np,b,npb,tb,pb,b22,b11,b10,b23,br,bc⟩ := RouteLiteralLeading.contract B a ram pattern path first rest ys 0#32
    patSpan pathSpan patBound pathBound pa a21 a22 a18 a11 a20 a10 a9 a24 a25 a26
  have keep (r : Reg) (n1 : r≠1) (n22 : r≠22) (n23 : r≠23) (out : r.val<10 ∨ 14<r.val) : b.get r=a.get r := br r n1 n22 n23 out
  have patTail : ReadBytes.Span B img ram (pattern+BitVec.ofNat 32 1) (first::rest) := ReadBytes.tail patSpan
  have pathTail : Bytes.Span B ram (path+BitVec.ofNat 32 1) ys := Bytes.tail pathSpan
  obtain ⟨nt,d,ntb,td,pd,d10,d11,dr,dc⟩ := RouteLiteralTail.contract B b ram pattern path 1 1 first rest ys 0#32 patTail pathTail plain literal
    (by simpa only [List.length_cons,Nat.add_comm] using patBound) (by simpa only [List.length_cons,Nat.add_comm] using pathBound) pb
    ((keep 21 (by decide) (by decide) (by decide) (by decide)).trans a21) b22
    (by simpa only [List.length_cons,Nat.add_comm] using (keep 18 (by decide) (by decide) (by decide) (by decide)).trans a18) b11
    ((keep 20 (by decide) (by decide) (by decide) (by decide)).trans a20) b10
    (by simpa only [List.length_cons,Nat.add_comm] using (keep 9 (by decide) (by decide) (by decide) (by decide)).trans a9)
    ((keep 24 (by decide) (by decide) (by decide) (by decide)).trans a24)
    ((keep 25 (by decide) (by decide) (by decide) (by decide)).trans a25)
    ((keep 26 (by decide) (by decide) (by decide) (by decide)).trans a26)
    ((keep 8 (by decide) (by decide) (by decide) (by decide)).trans a8)
  refine ⟨13+np+nt,d,by simp only [List.length_cons] at npb;omega,(ta.trans tb).trans td,pd,d10,d11,?_,dc.trans (bc.trans ac)⟩
  intro r n1 outside
  have out : r.val<10 ∨ 14<r.val := by omega
  have n22 : r≠22 := by intro h;subst r;omega
  have n23 : r≠23 := by intro h;subst r;omega
  exact (dr r n1 n22 n23 out).trans ((br r n1 n22 n23 out).trans
    (ar r (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega)
      (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega)
      (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega)
      (by intro h;subst r;omega) (by intro h;subst r;omega) (by intro h;subst r;omega) n22))
end E5R.Thermostat.RouteLiteralBody
