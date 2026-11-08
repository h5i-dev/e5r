import Projects.thermostat.OutputEffect
import Projects.thermostat.HttpDec
namespace E5R.Thermostat.HttpDecEffect
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp dst : Word) (pos n : Nat)
    (hn : n≤832) (hpos : pos≤94) (hp : c.pc=0x80004180#32)
    (h2 : c.get 2=sp+16#32) (h10 : c.get 10=dst) (h11 : c.get 11=192#32)
    (h12 : c.get 12=BitVec.ofNat 32 pos) (h13 : c.get 13=BitVec.ofNat 32 n)
    (hstack : Memory.Block B sp 16) (ha : sp.toNat%4=0) (hdst : Memory.Block B dst 192)
    (hsep : WordRegions.Disjoint sp 16 dst 192) :
    ∃ d, Quiet.Steps B img (HttpDec.time n) ⟨c,ram⟩ ⟨d,HttpDecMemory.memory ram sp dst pos n⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10=1#32 ∧ d.get 11=BitVec.ofNat 32 (pos+(ReplyJson.decimal n).length) ∧
      OutputEffect.Effect B ram (HttpDecMemory.memory ram sp dst pos n) sp dst 16 pos (ReplyJson.decimal n) := by
  obtain ⟨d,td,hr,d10,d11,hb,_⟩ := HttpDec.contract B c ram sp dst pos n hn hpos hp h2 h10 h11 h12 h13 hstack ha hdst hsep
  exact ⟨d,td,hr,d10,d11,hb,fun x hs ho => HttpDecMemory.frame ram sp dst x pos n hn hs ho⟩
end E5R.Thermostat.HttpDecEffect
