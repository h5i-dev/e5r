import Projects.thermostat.HeadTargetCase00
import Projects.thermostat.HeadTargetCase01
import Projects.thermostat.HeadTargetCase02
import Projects.thermostat.HeadTargetCase03
import Projects.thermostat.HeadTargetCase04
import Projects.thermostat.HeadTargetCase05
namespace E5R.Thermostat.HeadTargetValidate
open E5R E5R.Thermostat

def pc (offset index last stopByte : Word) (byte : BitVec 8) (remaining : Word) : Word :=
  if taken .eq offset (0 : Word) then 0x80002efc#32
  else if taken .geu index last then 0x80002efc#32
  else if taken .ne stopByte 32#32 then 0x80002efc#32
  else if taken .ne (BitVec.ofNat 32 byte.toNat) 47#32 then 0x80002efc#32
  else if taken .ne remaining 9#32 then 0x80002efc#32
  else 0x80002e20#32

/-- All actual target-stop checks through the HTTP-version prefix load.
    The byte and all branch conditions come from the real registers/RAM. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (offset index last stopByte base remaining : Word) (byte : BitVec 8)
    (hp : c.pc=0x80002dfe#32) (h30 : c.get 30=offset) (h18 : c.get 18=index)
    (h9 : c.get 9=last) (h20 : c.get 20=stopByte) (h28 : c.get 28=base) (h31 : c.get 31=remaining)
    (hm : B.inRam (base+1#32) 1=true) (hbyte : ram (base+1#32)=byte) :
    ∃ n d, 1≤n ∧ n≤9 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=pc offset index last stopByte byte remaining ∧
      (∀ r : Reg, r≠8 → r≠28 → d.get r=c.get r) ∧ d.sameCsr c := by
  cases h0 : taken .eq offset (0 : Word) with
  | true =>
    obtain ⟨d,trace,endPC,frame,csr⟩ := HeadTargetCase00.contract B c ram offset index last stopByte base remaining byte h30 h18 h9 h20 h28 h31 hm hbyte h0 hp
    refine ⟨1,d,by decide,by decide,trace,?_,?_,csr⟩
    · simpa only [pc,h0,Bool.false_eq_true,ite_false,ite_true] using endPC
    · intro r h8 h28
      exact frame r
  | false =>
    cases h1 : taken .geu index last with
    | true =>
      obtain ⟨d,trace,endPC,frame,csr⟩ := HeadTargetCase01.contract B c ram offset index last stopByte base remaining byte h30 h18 h9 h20 h28 h31 hm hbyte h0 h1 hp
      refine ⟨2,d,by decide,by decide,trace,?_,?_,csr⟩
      · simpa only [pc,h0,h1,Bool.false_eq_true,ite_false,ite_true] using endPC
      · intro r h8 h28
        exact frame r
    | false =>
      cases h2 : taken .ne stopByte 32#32 with
      | true =>
        obtain ⟨d,trace,endPC,v0,frame,csr⟩ := HeadTargetCase02.contract B c ram offset index last stopByte base remaining byte h30 h18 h9 h20 h28 h31 hm hbyte h0 h1 h2 hp
        refine ⟨4,d,by decide,by decide,trace,?_,?_,csr⟩
        · simpa only [pc,h0,h1,h2,Bool.false_eq_true,ite_false,ite_true] using endPC
        · intro r h8 h28
          exact frame r h8
      | false =>
        cases h3 : taken .ne (BitVec.ofNat 32 byte.toNat) 47#32 with
        | true =>
          obtain ⟨d,trace,endPC,v0,v1,frame,csr⟩ := HeadTargetCase03.contract B c ram offset index last stopByte base remaining byte h30 h18 h9 h20 h28 h31 hm hbyte h0 h1 h2 h3 hp
          refine ⟨7,d,by decide,by decide,trace,?_,?_,csr⟩
          · simpa only [pc,h0,h1,h2,h3,Bool.false_eq_true,ite_false,ite_true] using endPC
          · intro r h8 h28
            exact frame r h8 h28
        | false =>
          cases h4 : taken .ne remaining 9#32 with
          | true =>
            obtain ⟨d,trace,endPC,v0,v1,frame,csr⟩ := HeadTargetCase04.contract B c ram offset index last stopByte base remaining byte h30 h18 h9 h20 h28 h31 hm hbyte h0 h1 h2 h3 h4 hp
            refine ⟨9,d,by decide,by decide,trace,?_,?_,csr⟩
            · simpa only [pc,h0,h1,h2,h3,h4,Bool.false_eq_true,ite_false,ite_true] using endPC
            · intro r h8 h28
              exact frame r h8 h28
          | false =>
            obtain ⟨d,trace,endPC,v0,v1,frame,csr⟩ := HeadTargetCase05.contract B c ram offset index last stopByte base remaining byte h30 h18 h9 h20 h28 h31 hm hbyte h0 h1 h2 h3 h4 hp
            refine ⟨9,d,by decide,by decide,trace,?_,?_,csr⟩
            · simpa only [pc,h0,h1,h2,h3,h4,Bool.false_eq_true,ite_false,ite_true] using endPC
            · intro r h8 h28
              exact frame r h8 h28
end E5R.Thermostat.HeadTargetValidate
