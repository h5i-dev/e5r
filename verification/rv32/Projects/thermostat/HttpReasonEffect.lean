import Projects.thermostat.OutputEffect
import Projects.thermostat.HttpReason
namespace E5R.Thermostat.HttpReasonEffect
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

theorem contract (c : Core) (ram : Word → BitVec 8) (sp dst : Word) (status : Nat)
    (hlo : 100≤status) (hhi : status≤599) (hp : c.pc=0x80003584#32)
    (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=13#32)
    (h13 : c.get 13=BitVec.ofNat 32 status) (hm : Memory.Block B dst 192) :
    ∃ d n, n≤178 ∧ Quiet.Steps B img n ⟨c,ram⟩
      ⟨d,ByteWrite.write ram (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason status))⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10=1#32 ∧
      d.get 11=BitVec.ofNat 32 (13+(WireSpec.ascii (ResponseHeadSpec.reason status)).length) ∧
      OutputEffect.Effect B ram (ByteWrite.write ram (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason status)))
        sp dst 0 13 (WireSpec.ascii (ResponseHeadSpec.reason status)) := by
  obtain ⟨d,n,hn,td,hr,d10,d11,hb⟩ := HttpReason.contract c ram dst status hlo hhi hp h10 h11 h12 h13 hm
  refine ⟨d,n,hn,td,hr,d10,d11,hb,?_⟩
  intro x _ ho
  exact ByteWrite.frame ram _ x _ ho
end E5R.Thermostat.HttpReasonEffect
