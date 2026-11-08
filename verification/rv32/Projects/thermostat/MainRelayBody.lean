import Projects.thermostat.MainRelayPrefix
import Projects.thermostat.MainRelaySegment
import Projects.thermostat.MainRelayCaptureFrame
import Projects.thermostat.ByteSlices
set_option autoImplicit false
namespace E5R.Thermostat.MainRelayBody
open E5R E5R.Thermostat

/-- Actual selected relay matcher: fixed prefix, arbitrary final segment loop,
    bounds checks and the two real parameter stores. No capture result is assumed. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (path params : Word) (param : List (BitVec 8))
    (hp : c.pc=0x80002856#32) (h10 : c.get 10=0x80005b9c#32) (h11 : c.get 11=10#32)
    (h12 : c.get 12=path) (h13 : c.get 13=BitVec.ofNat 32 (7+param.length)) (h14 : c.get 14=params)
    (patternBytes : ReadBytes.Span B img ram 0x80005b9c#32 (WireSpec.ascii "/relay/{i}"))
    (pathBytes : Bytes.Span B ram path (WireSpec.ascii "/relay/"++param))
    (nonempty : param≠[]) (noSlash : ∀ b∈param, b≠47#8)
    (block : Memory.Block B params 8) (aligned : params.toNat%4=0) :
    ∃ d, Quiet.Steps B img (211+5*param.length) ⟨c,ram⟩ ⟨d,MainRelayCapture.memory ram params (BitVec.ofNat 32 (7+param.length))⟩ ∧
      d.pc=0x8000293a#32 ∧ d.get 10=1#32 ∧ d.get 11=1#32 ∧
      (∀ r : Reg, r∈[2,3,4] → d.get r=c.get r) ∧ d.sameCsr c := by
  have length : (WireSpec.ascii "/relay/"++param).length=7+param.length := by rw [List.length_append];rfl
  have bound : 7+param.length<2^32 := by rw [←length];exact pathBytes.length
  have lower : 8≤(BitVec.ofNat 32 (7+param.length)).toNat := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound]
    have positive := List.length_pos_iff.mpr nonempty
    omega
  obtain ⟨a,ta,pa,a19,a9,a20,a18,a21,a8,a10,a11,a24,a25,a26,a27,a22,a12,a23,a13,a1,a14,ar,ac⟩ :=
    MainRelayPrefix.contract B c ram path params (BitVec.ofNat 32 (7+param.length)) param h10 h11 h12 h13 h14 lower patternBytes (ReadBytes.of_ram pathBytes) hp
  have span : Bytes.Span B ram (path+7#32) param := by
    simpa only [show (WireSpec.ascii "/relay/").length=7 from rfl] using Bytes.suffix pathBytes
  obtain ⟨b,tb,pb,b23,br,bc⟩ := MainRelaySegment.contract B a ram path 7 param span nonempty bound noSlash pa a20 a23 a9 a24
  obtain ⟨d,td,pd,d12,d13,d11,d8,d10,dr,dc⟩ := MainRelayCapture.contract B b ram params (BitVec.ofNat 32 (7+param.length))
    ((br 9 (by decide) (by decide)).trans a9) ((br 18 (by decide) (by decide)).trans a18)
    ((br 22 (by decide) (by decide)).trans a22) ((br 11 (by decide) (by decide)).trans a11) b23
    ((br 10 (by decide) (by decide)).trans a10) ((br 21 (by decide) (by decide)).trans a21)
    ((br 25 (by decide) (by decide)).trans a25) ((br 26 (by decide) (by decide)).trans a26)
    ((br 27 (by decide) (by decide)).trans a27) ((br 8 (by decide) (by decide)).trans a8)
    ((br 19 (by decide) (by decide)).trans a19) lower block aligned patternBytes pb
  have trace := (ta.trans tb).trans td
  have count : 181+(5*param.length+1)+29=211+5*param.length := by omega
  refine ⟨d,by simpa only [count] using trace,pd,d10,d11,?_,dc.trans (bc.trans ac)⟩
  intro r member
  have n : ∀ r : Reg, r∈[2,3,4] → r≠12 ∧ r≠13 ∧ r≠11 ∧ r≠8 ∧ r≠10 ∧ r≠23 ∧
      r≠19 ∧ r≠9 ∧ r≠20 ∧ r≠18 ∧ r≠21 ∧ r≠24 ∧ r≠25 ∧ r≠26 ∧ r≠27 ∧ r≠22 ∧ r≠1 ∧ r≠14 := by decide +kernel
  obtain ⟨n12,n13,n11,n8,n10,n23,n19,n9,n20,n18,n21,n24,n25,n26,n27,n22,n1,n14⟩ := n r member
  exact (dr r n12 n13 n11 n8 n10).trans ((br r n12 n23).trans
    (ar r n19 n9 n20 n18 n21 n8 n10 n11 n24 n25 n26 n27 n22 n12 n23 n13 n1 n14))
end E5R.Thermostat.MainRelayBody
