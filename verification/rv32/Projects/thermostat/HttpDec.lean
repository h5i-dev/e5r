import Projects.thermostat.HttpDecRegs
import Projects.thermostat.HttpDecMemory
import Projects.thermostat.HttpDecCapacity
import Projects.thermostat.HttpDecCopyLoop
import Projects.thermostat.HttpDecEnd
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HttpDec
open E5R E5R.Thermostat

def time (n : Nat) := 74+HttpDecDigits.duration n+5*(ReplyJson.decimal n).length

theorem time_bound (n : Nat) (hn : n≤832) : time n≤126 := by
  rw [time,HttpDecDigitsSpec.length n hn]
  unfold HttpDecDigits.duration
  by_cases h1 : n<10
  · simp only [h1,ite_true];decide
  · by_cases h2 : n<100 <;> simp only [h1,h2,ite_false,ite_true] <;> decide

/-- Complete actual put_dec for the real send routine's bounded body/header
    window, through the real RET. No decimal, copy or ABI result is assumed. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp dst : Word) (pos n : Nat)
    (hn : n≤832) (hpos : pos≤94) (hp : c.pc=0x80004180#32)
    (h2 : c.get 2=sp+16#32) (h10 : c.get 10=dst) (h11 : c.get 11=192#32)
    (h12 : c.get 12=BitVec.ofNat 32 pos) (h13 : c.get 13=BitVec.ofNat 32 n)
    (hstack : Memory.Block B sp 16) (ha : sp.toNat%4=0) (hdst : Memory.Block B dst 192)
    (hsep : WordRegions.Disjoint sp 16 dst 192) :
    ∃ d, Quiet.Steps B img (time n) ⟨c,ram⟩ ⟨d,HttpDecMemory.memory ram sp dst pos n⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10=1#32 ∧ d.get 11=BitVec.ofNat 32 (pos+(ReplyJson.decimal n).length) ∧
      Bytes.Span B (HttpDecMemory.memory ram sp dst pos n) (dst+BitVec.ofNat 32 pos) (ReplyJson.decimal n) ∧
      HttpDecRegs.Frame c d := by
  have hb := HttpDecDigitsSpec.bounds n hn
  let count := (ReplyJson.decimal n).length-1
  obtain ⟨a,ta,pa,a2,a14,a15,a16,a17,ar,ac⟩ := HttpDecLeading.contract B c ram sp n hn hp h2 h13 hstack ha
  have af : HttpDecRegs.Frame c a := fun r h2 h5 h6 h10 h11 h12 h13 h14 h15 h16 h17 => ar r h2 h14 h15 h16 h17
  obtain ⟨b,tb,pb,b2,b14,b15,br,bc⟩ := HttpDecDigits.contract B a (HttpDecLeading.memory ram sp) sp n hn pa a2
    ((ar 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13) a14 hstack
  have bf : HttpDecRegs.Frame c b := fun r h2 h5 h6 h10 h11 h12 h13 h14 h15 h16 h17 =>
    (br r h5 h6 h13 h14 h15 h16 h17).trans (af r h2 h5 h6 h10 h11 h12 h13 h14 h15 h16 h17)
  have b10 : b.get 10=dst := (br 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((ar 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10)
  have b11 : b.get 11=192#32 := (br 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((ar 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11)
  have b12 : b.get 12=BitVec.ofNat 32 pos := (br 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((ar 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12)
  obtain ⟨u,tu,pu,u13,u11,u12,u10,ur,uc⟩ := HttpDecCapacity.contract B b (HttpDecMemory.source ram sp n) sp dst pos count hpos
    (by dsimp only [count];omega) b2 b10 b11 b12 b15 pb
  have uf : HttpDecRegs.Frame c u := fun r h2 h5 h6 h10 h11 h12 h13 h14 h15 h16 h17 =>
    (ur r h13 h11 h12 h10).trans (bf r h2 h5 h6 h10 h11 h12 h13 h14 h15 h16 h17)
  have uend : u.get 10=(dst+BitVec.ofNat 32 pos)+BitVec.ofNat 32 (ReplyJson.decimal n).length := by
    rw [u10,show pos+count+1=pos+(ReplyJson.decimal n).length by dsimp only [count];omega]
    rw [BitVec.ofNat_add,←BitVec.add_assoc]
  obtain ⟨v,tv,pv,v13,v12,vr,vc⟩ := HttpDecCopyLoop.contract B u (HttpDecMemory.source ram sp n) (sp+4#32) (dst+BitVec.ofNat 32 pos)
    (ReplyJson.decimal n) (List.length_pos_iff.mp hb.1) pu u13 u12 uend
    (HttpDecMemory.source_span B ram sp n hn hstack) (HttpDecMemory.destination B dst pos n hpos hn hdst)
    (HttpDecMemory.separated sp dst pos n hpos hn hsep)
  have vf : HttpDecRegs.Frame c v := fun r h2 h5 h6 h10 h11 h12 h13 h14 h15 h16 h17 =>
    (vr r h12 h13 h14).trans (uf r h2 h5 h6 h10 h11 h12 h13 h14 h15 h16 h17)
  have v2 : v.get 2=sp := (vr 2 (by decide) (by decide) (by decide)).trans
    ((ur 2 (by decide) (by decide) (by decide) (by decide)).trans b2)
  have v11 : v.get 11=BitVec.ofNat 32 (pos+count) := (vr 11 (by decide) (by decide) (by decide)).trans u11
  obtain ⟨d,td,pd,d11,d14,d10,d2,dr,dc⟩ := HttpDecEnd.contract B v (HttpDecMemory.memory ram sp dst pos n) sp (pos+count) v2 v11 pv
  have df : HttpDecRegs.Frame c d := fun r h2 h5 h6 h10 h11 h12 h13 h14 h15 h16 h17 =>
    (dr r h11 h14 h10 h2).trans (vf r h2 h5 h6 h10 h11 h12 h13 h14 h15 h16 h17)
  refine ⟨d,?_,HttpDecRegs.returned ?_ (d2.trans h2.symm) (dc.trans (vc.trans (uc.trans (bc.trans ac)))) df,d10,?_,
    HttpDecMemory.bytes B ram sp dst pos n hpos hn hdst,df⟩
  · have tt := (((ta.trans tb).trans tu).trans tv).trans td
    change Quiet.Steps B img (((60+HttpDecDigits.duration n)+8)+5*(ReplyJson.decimal n).length+6) ⟨c,ram⟩ ⟨d,HttpDecMemory.memory ram sp dst pos n⟩ at tt
    rw [show ((60+HttpDecDigits.duration n)+8)+5*(ReplyJson.decimal n).length+6=time n by unfold time;omega] at tt
    exact tt
  · rw [pd,vf 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [d11,show pos+count+1=pos+(ReplyJson.decimal n).length by dsimp only [count];omega]
end E5R.Thermostat.HttpDec
