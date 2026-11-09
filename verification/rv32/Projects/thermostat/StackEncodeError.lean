import Projects.thermostat.EncodeErrorQuiet
import Projects.thermostat.StackCopyData
import Projects.thermostat.StackErrorCopy
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.StackEncodeError
open E5R E5R.Thermostat EncodeError
theorem contract_quiet (c : Core) (ram : Word → BitVec 8) (p ptr dst : Word) (cap : Nat) (e : Spec.Error)
    (hp : c.pc=0x80001e4a#32) (hsp : c.get 2=p+32#32) (h10 : c.get 10=ptr) (h11 : c.get 11=dst)
    (h12 : c.get 12=BitVec.ofNat 32 cap) (hc : 33≤cap) (hb : cap<2^32)
    (hm : Memory.Block StackBoard.board p 32) (ha : p.toNat%4=0)
    (hx : ReadBytes.Byte StackBoard.board img ram ptr (Errors.code e))
    (hps : WordRegions.Disjoint ptr 1 p 32) (hds : WordRegions.Disjoint dst (ReplyJson.errorBody e).length p 32)
    (hd : Memory.Block StackBoard.board dst (ReplyJson.errorBody e).length)
    (hda : dst.toNat%4=0) (hw : dst.toNat+(ReplyJson.errorBody e).length<2^32) :
    ∃ d n r, n≤ErrorCopy.bound e+26 ∧ Quiet.Steps StackBoard.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧ FormatCursor.Returned c d ∧
      d.get 10=ErrorLiterals.status e ∧ d.get 11=BitVec.ofNat 32 (ReplyJson.errorBody e).length ∧
      Bytes.Span StackBoard.board r dst (ReplyJson.errorBody e) ∧
      (∀ x, (∀ i : Fin 32, x≠p+BitVec.ofNat 32 i.val) →
        (∀ i : Fin (ReplyJson.errorBody e).length, x≠dst+BitVec.ofNat 32 i.val) → r x=ram x) := by
  have hsp' : c.get 2=(p+16#32)+16#32 := by simpa only [BitVec.add_assoc,show (16#32+16#32)=32#32 by decide +kernel] using hsp
  have hmem := Memory.sub_block hm (off := 16) (m := 16) (by decide) (by decide)
  have hal := Memory.word_aligned p 4 ha
  obtain ⟨a,na,hna,ta,hr⟩ := E5R.Thermostat.ErrorPrepare.contract_quiet StackBoard.board c ram (p+16#32) ptr dst cap e hp hsp' h10 h11 h12 hc hb
    hmem hal hx (Subregion.right hps 16 16 (by decide))
  let saved := ErrorSave.memory ram (p+16#32) c
  obtain ⟨z,nz,r,hnz,tz,hz,_,hbytes,hfr⟩ := E5R.Thermostat.StackErrorCopy.contract_quiet a saved p dst e hr.pc hr.stack hr.output hr.source hr.length
    (by simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 16) (by decide) (by decide)) ha hd hda hw
    (by simpa only [BitVec.add_zero] using Subregion.right hds 0 16 (by decide))
  have region : ViewFrame.Region saved r (p+20#32) 12 := by
    intro i
    apply hfr
    · intro j
      have hi := i.isLt
      have hj := j.isLt
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using WordZero.offset_ne p (20+i.val) j.val (by omega) (by omega) (by omega)
    · exact WordRegions.symm (Subregion.right hds 20 12 (by decide)) i
  have region' : ViewFrame.Region saved r ((p+16#32)+4#32) 12 := by
    simpa only [BitVec.add_assoc,show (16#32+4#32)=20#32 by decide +kernel] using region
  obtain ⟨d,td,hret,hstatus,hlen⟩ := E5R.Thermostat.ErrorExit.contract_quiet StackBoard.board c a z ram r (p+16#32) dst e hr hz hsp' hmem hal region'
  refine ⟨d,na+nz+7,r,by omega,(ta.trans tz).trans td,hret,hstatus,hlen,hbytes,?_⟩
  intro x hstack hout
  rw [hfr x (fun i => hstack ⟨i.val,by have := i.isLt;omega⟩) hout]
  exact ErrorSave.frame ram (p+16#32) c x (by
    intro i
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hstack ⟨16+i.val,by have := i.isLt;omega⟩)

end E5R.Thermostat.StackEncodeError
