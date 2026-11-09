import Projects.thermostat.WriteErrorTailQuiet
import Projects.thermostat.StackCopyData
import Projects.thermostat.StackEncodeError
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.StackWriteErrorTail
open E5R E5R.Thermostat WriteErrorTail
theorem contract_quiet (c : Core) (ram : Word → BitVec 8) (p dst out f : Word) (cap : Nat) (e : Spec.Error)
    (hp : c.pc = 0x80000652#32) (hsp : c.get 2 = p+320#32)
    (h8 : c.get 8 = f) (h9 : c.get 9 = out) (h19 : c.get 19 = dst)
    (h18 : c.get 18 = BitVec.ofNat 32 cap) (h22 : c.get 22 = 1#32)
    (hm : Memory.Block StackBoard.board p 416) (ha : p.toNat%4=0)
    (herr : c.get 10=BitVec.ofNat 32 (Errors.code e).toNat)
    (hc : cap<2^32) (hd : Memory.Block StackBoard.board dst cap) (hw : dst.toNat+cap<2^32) (hda : dst.toNat%4=0)
    (ho : Memory.Block StackBoard.board out 15) (hoa : out.toNat%4=0) (hf : Memory.Block StackBoard.board f 41)
    (hds : WordRegions.Disjoint dst cap p 416) (hos : WordRegions.Disjoint out 15 p 416) (hfs : WordRegions.Disjoint f 41 p 416)
    (hof : WordRegions.Disjoint out 15 f 41) (hdo : WordRegions.Disjoint dst cap out 15) (hdf : WordRegions.Disjoint dst cap f 41)
    (hcap : 33≤cap) :
    ∃ d n r, n ≤ 198 ∧ Quiet.Steps StackBoard.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = ramRead ram (c.get 2+92#32) .w &&& ~~~1 ∧ d.get 2 = p+416#32 ∧ d.sameCsr c ∧
      OuterReturn.Restored c d ram ∧
      BodyMemory.At r out 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.errorBody e).length) (ErrorLiterals.status e) ∧
      Bytes.Span StackBoard.board r dst (ReplyJson.errorBody e) ∧ r (f+36#32)=1#8 ∧ r (f+40#32)=1#8 ∧
      (∀ x, (∀ i : Fin 416, x ≠ p+BitVec.ofNat 32 i.val) → (∀ i : Fin cap, x ≠ dst+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 15, x ≠ out+BitVec.ofNat 32 i.val) → (∀ i : Fin 41, x ≠ f+BitVec.ofNat 32 i.val) → r x = ram x) := by
  have hfit : (ReplyJson.errorBody e).length≤cap := by
    have hb : (ReplyJson.errorBody e).length≤33 := by cases e <;> decide
    omega
  let r0 := WriteErrorStore.memory ram (p+320#32) e
  have tm := E5R.Thermostat.WriteErrorStore.contract_quiet StackBoard.board c ram (p+320#32) e hp hsp herr
    (Memory.sub_block hm (off := 320) (m := 25) (by decide) (by decide))
  obtain ⟨a,ta,apc,a10,a11,a12,a1,ar,ac⟩ := E5R.Thermostat.WriteErrorCall.contract_quiet StackBoard.board (c.goto 0x80000656#32) r0 (p+320#32) dst (BitVec.ofNat 32 cap) hsp h19 h18 rfl
  have asp : a.get 2=p+320#32 := (ar 2 (by decide) (by decide) (by decide) (by decide)).trans hsp
  have a10' : a.get 10=p+344#32 := by simpa only [BitVec.add_assoc,show (320#32+24#32)=344#32 by decide +kernel] using a10
  have astack : a.get 2=(p+288#32)+32#32 := by simpa only [BitVec.add_assoc,show (288#32+32#32)=320#32 by decide +kernel] using asp
  have hbyte : ReadBytes.Byte StackBoard.board img r0 (p+344#32) (Errors.code e) := by
    simpa only [BitVec.add_assoc,show (320#32+24#32)=344#32 by decide +kernel] using
      WriteErrorStore.byte StackBoard.board ram (p+320#32) e (Memory.sub_block hm (off := 320) (m := 25) (by decide) (by decide))
  obtain ⟨z,k,r,hk,tz,hz,z10,z11,hsout,fr0⟩ := E5R.Thermostat.StackEncodeError.contract_quiet a r0 (p+288#32) (p+344#32) dst cap e apc astack a10' a11 a12 hcap hc
    (Memory.sub_block hm (off := 288) (m := 32) (by decide) (by decide)) (Memory.word_aligned p 72 ha) hbyte
    (FormatSpace.offsets_disjoint p 344 1 288 32 (by decide) (by decide) (by decide))
    (WordRegions.shrink (Subregion.right hds 288 32 (by decide)) hfit (Nat.le_refl _))
    (by simpa only [BitVec.add_zero] using Subregion.block hd (by omega) hw 0 (ReplyJson.errorBody e).length (by simpa only [Nat.zero_add] using hfit))
    hda (by omega)
  have hmax : ErrorCopy.bound e≤137 := by cases e <;> decide
  have fr (x : Word) (hs : ∀ i : Fin 416, x≠p+BitVec.ofNat 32 i.val)
      (hdst : ∀ i : Fin cap, x≠dst+BitVec.ofNat 32 i.val) : r x=ram x := by
    rw [fr0 x (by intro i;simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hs ⟨288+i.val,by have := i.isLt;omega⟩)
      (fun i => hdst ⟨i.val,Nat.lt_of_lt_of_le i.isLt hfit⟩)]
    exact WriteErrorStore.frame ram (p+320#32) e x (by
      simpa only [BitVec.add_assoc,show (320#32+24#32)=344#32 by decide +kernel] using hs ⟨344,by decide⟩)
  have zpc : z.pc = 0x80000664#32 := by rw [hz.pc,a1];decide +kernel
  have zsp : z.get 2 = p+320#32 := hz.sp.trans asp
  have keep (reg : Reg) (hsaved : Callee.Saved reg) : z.get reg = c.get reg := by
    exact (Callee.of_returned hz reg hsaved).trans (ar reg (Callee.ne_low reg 10 hsaved (by decide) (by decide) (by decide))
      (Callee.ne_low reg 11 hsaved (by decide) (by decide) (by decide))
      (Callee.ne_low reg 12 hsaved (by decide) (by decide) (by decide))
      (Callee.ne_low reg 1 hsaved (by decide) (by decide) (by decide)))
  obtain ⟨b,tb,bpc,b20,b18,b12,b10,br,bc⟩ := E5R.Thermostat.WriteErrorReturn.contract_quiet StackBoard.board z r (ErrorLiterals.status e) (ReplyJson.errorBody e).length cap z10 z11
    ((hz.x18.trans (ar 18 (by decide) (by decide) (by decide) (by decide))).trans h18) hc hfit zpc
  have bsp : b.get 2 = p+320#32 := (br 2 (by decide) (by decide) (by decide) (by decide)).trans zsp
  have b8 : b.get 8 = f := (br 8 (by decide) (by decide) (by decide) (by decide)).trans ((keep 8 (by decide)).trans h8)
  have b9 : b.get 9 = out := (br 9 (by decide) (by decide) (by decide) (by decide)).trans ((keep 9 (by decide)).trans h9)
  have b22 : b.get 22 = 1#32 := (br 22 (by decide) (by decide) (by decide) (by decide)).trans ((keep 22 (by decide)).trans h22)
  obtain ⟨d,td,dpc,dsp,dc,dsaved,dresponse,h36,h40⟩ := E5R.Thermostat.BodyReturn.contract_quiet StackBoard.board b r out f 0x800056a8#32 16#32
    (BitVec.ofNat 32 (ReplyJson.errorBody e).length) (ErrorLiterals.status e) bpc b8 b9 b10 b12 b18 b20 b22 ho hoa hf
    (by rw [bsp];exact Memory.sub_block hm (off := 320) (m := 96) (by decide) (by decide))
    (by rw [bsp];exact Memory.word_aligned p 80 ha)
    (by rw [bsp];exact WordRegions.symm (Subregion.right hos 320 96 (by decide)))
    (by rw [bsp];exact WordRegions.symm (Subregion.right hfs 320 96 (by decide))) hof
  have saved : ViewFrame.Region ram r (p+364#32) 52 := by
    intro i
    rw [fr0 _ (FormatSpace.offsets_disjoint p 364 52 288 32 (by decide) (by decide) (by decide) i)
      (WordRegions.symm (WordRegions.shrink (Subregion.right hds 364 52 (by decide)) hfit (Nat.le_refl _)) i)]
    apply WriteErrorStore.frame
    have hi := i.isLt
    have hh := WordZero.offset_ne p (364+i.val) 344 (by omega) (by decide) (by omega)
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hh
  have words (off : Nat) (hlo : 44≤off) (hb : off+4≤96) : ramRead r (b.get 2+BitVec.ofNat 32 off) .w = ramRead ram (c.get 2+BitVec.ofNat 32 off) .w := by
    have hh := ViewFrame.word saved (off-44) (by omega)
    have he : (p+364#32)+BitVec.ofNat 32 (off-44)=(p+320#32)+BitVec.ofNat 32 off := by
      rw [BitVec.add_assoc,BitVec.add_assoc,←BitVec.ofNat_add,←BitVec.ofNat_add]
      congr 2;omega
    rw [he] at hh
    rw [bsp,hsp];exact hh
  let final := BodyResponse.memory r out f 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.errorBody e).length) (ErrorLiterals.status e)
  have hbytes : Bytes.Span StackBoard.board final dst (ReplyJson.errorBody e) := by
    apply ViewFrame.span hsout
    intro i
    have hi : i.val < cap := Nat.lt_of_lt_of_le i.isLt hfit
    exact BodyMemory.frame r out f 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.errorBody e).length) (ErrorLiterals.status e)
      (dst+BitVec.ofNat 32 i.val) (hdo ⟨i.val,hi⟩) (hdf ⟨i.val,hi⟩)
  refine ⟨d,1+5+k+7+22,final,by omega,(((Quiet.Steps.single tm).trans ta).trans tz).trans tb |>.trans td,?_,?_,((dc.trans bc).trans hz.csr).trans ac,?_,dresponse,hbytes,h36,h40,?_⟩
  · rw [dpc,words 92 (by decide) (by decide)]
  · simpa only [bsp,BitVec.add_assoc,show (320#32+96#32)=416#32 by decide +kernel] using dsp
  · constructor
    · exact dsaved.x1 |>.trans (words 92 (by decide) (by decide))
    · exact dsaved.x8 |>.trans (words 88 (by decide) (by decide))
    · exact dsaved.x9 |>.trans (words 84 (by decide) (by decide))
    · exact dsaved.x18 |>.trans (words 80 (by decide) (by decide))
    · exact dsaved.x19 |>.trans (words 76 (by decide) (by decide))
    · exact dsaved.x20 |>.trans (words 72 (by decide) (by decide))
    · exact dsaved.x21 |>.trans (words 68 (by decide) (by decide))
    · exact dsaved.x22 |>.trans (words 64 (by decide) (by decide))
    · exact dsaved.x23 |>.trans (words 60 (by decide) (by decide))
    · exact dsaved.x24 |>.trans (words 56 (by decide) (by decide))
    · exact dsaved.x25 |>.trans (words 52 (by decide) (by decide))
    · exact dsaved.x26 |>.trans (words 48 (by decide) (by decide))
    · exact dsaved.x27 |>.trans (words 44 (by decide) (by decide))
  · intro x hx hdst hout hfuture
    exact (BodyMemory.frame r out f 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.errorBody e).length) (ErrorLiterals.status e) x hout hfuture).trans
      (fr x hx hdst)

end E5R.Thermostat.StackWriteErrorTail
