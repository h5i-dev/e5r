import Projects.thermostat.RelayCaptureEmpty
import Projects.thermostat.RelayCaptureNonempty
import Projects.thermostat.RoutePatternScan
import Projects.thermostat.RoutePathEntry
import Projects.thermostat.RouteScanSpec
set_option autoImplicit false
namespace E5R.Thermostat.RelayCaptureTail
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (params : Word) (ys : List (BitVec 8)) :=
  if RoutePathScan.length ys=0 then ram else MainRelayCapture.memory ram params (BitVec.ofNat 32 (7+RoutePathScan.length ys))

def accepted (ys : List (BitVec 8)) : Prop := ys≠[] ∧ ∀ b∈ys,b≠47#8
instance (ys : List (BitVec 8)) : Decidable (accepted ys) := by unfold accepted;infer_instance

/-- Actual suffix scan and capture, including empty and extra-slash refusal.
    The memory result retains a partial capture even when the final test fails. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (path params : Word) (ys : List (BitVec 8))
    (pattern : ReadBytes.Span B img ram 0x80005b9c#32 (WireSpec.ascii "/relay/{i}"))
    (span : Bytes.Span B ram (path+7#32) ys) (bound : 7+ys.length≤2048)
    (block : Memory.Block B params 8) (aligned : params.toNat%4=0)
    (pc : c.pc=0x8000287a#32) (h21 : c.get 21=0x80005b9c#32) (h22 : c.get 22=7#32)
    (h18 : c.get 18=10#32) (h11 : c.get 11=7#32) (h20 : c.get 20=path) (h10 : c.get 10=7#32)
    (h9 : c.get 9=BitVec.ofNat 32 (7+ys.length)) (h24 : c.get 24=47#32) (h25 : c.get 25=1#32)
    (h26 : c.get 26=123#32) (h27 : c.get 27=125#32) (h8 : c.get 8=0#32) (h19 : c.get 19=params) :
    ∃ n d, n≤5*ys.length+48 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,memory ram params ys⟩ ∧ d.pc=0x8000293a#32 ∧
      d.get 10=(if accepted ys then 1#32 else 0#32) ∧
      d.get 11=(if RoutePathScan.length ys=0 then 0#32 else 1#32) ∧
      (∀ r : Reg,r≠8 → r≠10 → r≠11 → r≠12 → r≠13 → r≠22 → r≠23 → d.get r=c.get r) ∧ d.sameCsr c := by
  have suffix : ReadBytes.Span B img ram (0x80005b9c#32+BitVec.ofNat 32 7) (WireSpec.ascii "{i}") := by
    have view := ReadBytes.tail (ReadBytes.tail (ReadBytes.tail (ReadBytes.tail (ReadBytes.tail (ReadBytes.tail (ReadBytes.tail pattern))))))
    exact view
  obtain ⟨np,a,npb,ta,pa,a22,ar,ac⟩ := RoutePatternScan.contract B c ram 0x80005b9c#32 7 (WireSpec.ascii "{i}") suffix
    (by decide) (by decide) pc h21 h22 h18 h24
  have ae : a.get 22=10#32 := by simpa only [show RoutePathScan.length (WireSpec.ascii "{i}")=3 by rfl] using a22
  obtain ⟨ns,b,nsb,tb,pb,b23,br,bc⟩ := RoutePathEntry.contract B a ram path 7 ys span bound pa
    ((ar 20 (by decide) (by decide)).trans h20) ((ar 10 (by decide) (by decide)).trans h10)
    ((ar 9 (by decide) (by decide)).trans h9) ((ar 24 (by decide) (by decide)).trans h24)
  have keep (r : Reg) (n12 : r≠12) (n22 : r≠22) (n23 : r≠23) : b.get r=c.get r :=
    (br r n12 n23).trans (ar r n12 n22)
  have b22 : b.get 22=10#32 := (br 22 (by decide) (by decide)).trans ae
  have usedBound : RoutePathScan.length ys≤ys.length := RoutePathScan.bounded ys
  have ordered : (BitVec.ofNat 32 (7+RoutePathScan.length ys)).toNat≤(BitVec.ofNat 32 (7+ys.length)).toNat := by
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 7+RoutePathScan.length ys<2^32 by omega),
      Nat.mod_eq_of_lt (show 7+ys.length<2^32 by omega)];omega
  have iffFinish : BitVec.ofNat 32 (7+RoutePathScan.length ys)=BitVec.ofNat 32 (7+ys.length) ↔ ∀ b∈ys,b≠47#8 := by
    constructor
    · intro equal
      have numeric := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 7+RoutePathScan.length ys<2^32 by omega),
        Nat.mod_eq_of_lt (show 7+ys.length<2^32 by omega)] at numeric
      exact RouteScanSpec.noSlash_of_end ys (by omega)
    · intro plain;rw [RouteLiteralTail.noSlash_length ys plain]
  by_cases zero : RoutePathScan.length ys=0
  · have noAccept : ¬accepted ys := by
      intro yes
      have all := RouteLiteralTail.noSlash_length ys yes.2
      have size : ys.length=0 := by omega
      exact yes.1 (List.length_eq_zero_iff.mp size)
    have b23' : b.get 23=7#32 := by simpa only [zero,Nat.add_zero] using b23
    obtain ⟨d,td,pd,d10,d11,dr,dc⟩ := RelayCaptureEmpty.contract B b ram (BitVec.ofNat 32 (7+ys.length))
      ((keep 9 (by decide) (by decide) (by decide)).trans h9)
      ((keep 18 (by decide) (by decide) (by decide)).trans h18) b22
      ((keep 11 (by decide) (by decide) (by decide)).trans h11) b23'
      ((keep 10 (by decide) (by decide) (by decide)).trans h10)
      ((keep 21 (by decide) (by decide) (by decide)).trans h21)
      ((keep 25 (by decide) (by decide) (by decide)).trans h25)
      ((keep 26 (by decide) (by decide) (by decide)).trans h26)
      ((keep 27 (by decide) (by decide) (by decide)).trans h27)
      ((keep 8 (by decide) (by decide) (by decide)).trans h8)
      (by simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 7+ys.length<2^32 by omega)];omega) pattern pb
    refine ⟨np+ns+17,d,by change np≤16 at npb;omega,?_,pd,?_,?_,?_,dc.trans (bc.trans ac)⟩
    · simpa only [memory,zero,ite_true] using (ta.trans tb).trans td
    · simpa only [noAccept,ite_false] using d10
    · simpa only [zero,ite_true] using d11
    · intro r n8 n10 n11 n12 n13 n22 n23
      exact (dr r n12 n13 n11 n10).trans (keep r n12 n22 n23)
  · have nonempty : ys≠[] := by intro nil;subst ys;exact zero rfl
    have acceptedIff : accepted ys ↔ ∀ b∈ys,b≠47#8 := by exact ⟨And.right,fun h => ⟨nonempty,h⟩⟩
    obtain ⟨d,td,pd,d10,d11,dr,dc⟩ := RelayCaptureNonempty.contract B b ram params
      (BitVec.ofNat 32 (7+RoutePathScan.length ys)) (BitVec.ofNat 32 (7+ys.length))
      ((keep 9 (by decide) (by decide) (by decide)).trans h9)
      ((keep 18 (by decide) (by decide) (by decide)).trans h18) b22
      ((keep 11 (by decide) (by decide) (by decide)).trans h11) b23
      ((keep 10 (by decide) (by decide) (by decide)).trans h10)
      ((keep 21 (by decide) (by decide) (by decide)).trans h21)
      ((keep 25 (by decide) (by decide) (by decide)).trans h25)
      ((keep 26 (by decide) (by decide) (by decide)).trans h26)
      ((keep 27 (by decide) (by decide) (by decide)).trans h27)
      ((keep 8 (by decide) (by decide) (by decide)).trans h8)
      ((keep 19 (by decide) (by decide) (by decide)).trans h19)
      (by simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 7+RoutePathScan.length ys<2^32 by omega)];omega)
      ordered block aligned pattern pb
    refine ⟨np+ns+29,d,by change np≤16 at npb;omega,?_,pd,?_,?_,?_,dc.trans (bc.trans ac)⟩
    · simpa only [memory,zero,ite_false] using (ta.trans tb).trans td
    · simpa only [iffFinish,←acceptedIff] using d10
    · simpa only [zero,ite_false] using d11
    · intro r n8 n10 n11 n12 n13 n22 n23
      exact (dr r n12 n13 n11 n8 n10).trans (keep r n12 n22 n23)
end E5R.Thermostat.RelayCaptureTail
