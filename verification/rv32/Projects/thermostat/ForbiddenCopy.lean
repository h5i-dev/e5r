import Projects.thermostat.AlignedCopy
import Projects.thermostat.ForbiddenCopyData
namespace E5R.Thermostat.ForbiddenCopy
open E5R E5R.Thermostat

theorem contract (c : Core) (ram : Word → BitVec 8) (sp dst : Word)
    (hp : c.pc=0x80005182#32) (hsp : c.get 2=sp+16#32)
    (h10 : c.get 10=dst) (h11 : c.get 11=0x80005be0#32) (h12 : c.get 12=21#32)
    (hd : Memory.Block UartPlatform.board dst 21) (ha : dst.toNat%4=0) (hw : dst.toNat+21<2^32) :
    ∃ d n r, n≤55 ∧ DetSteps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10=dst ∧ Bytes.Span UartPlatform.board r dst (ReplyJson.errorBody .forbidden) ∧
      (∀ x, (∀ i : Fin 21, x≠dst+BitVec.ofNat 32 i.val) → r x=ram x) := by
  have he : 0x80005be0#32+BitVec.ofNat 32 (4*ForbiddenCopyData.words.length)=0x80005bf4#32 := by decide +kernel
  obtain ⟨d,n,hn,td,hr,h10,hs,hframe⟩ := AlignedCopy.contract UartPlatform.board c ram sp 0x80005be0#32 dst ForbiddenCopyData.words [125#8]
    hp hsp h10 h11 h12 (by decide) (by decide) ForbiddenCopyData.source ha hd hw (by decide +kernel)
    (by rw [he];exact ForbiddenCopyData.final_byte ram) (by
      intro i
      have hi : i.val=0 := by have := i.isLt;change i.val<1 at this;omega
      simpa only [he,hi,show BitVec.ofNat 32 0=0#32 from rfl,BitVec.add_zero] using ForbiddenCopyData.final_outside)
  refine ⟨d,n,_,hn,td,hr,h10,?_,hframe⟩
  rw [←ForbiddenCopyData.bytes];exact hs
end E5R.Thermostat.ForbiddenCopy
