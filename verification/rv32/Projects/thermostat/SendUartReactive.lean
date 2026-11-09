import Projects.thermostat.UartWritePhase
import Projects.thermostat.SendHeadUart
import Projects.thermostat.SendBodyUart
set_option autoImplicit false
namespace E5R.Thermostat.SendUartReactive
open E5R E5R.Thermostat ProtocolStreamSpec
abbrev B := UartPlatform.board

/-- The actual Send-to-UART caller, including its concrete return site and
    preserved caller registers/RAM. No UART outcome is assumed. -/
structure Prepared (original a : Core) (before pre : Word → BitVec 8) (obj io src : Word)
    (bs : List (BitVec 8)) (ret : Word) : Prop where
  input : UartWritePhase.Input a pre (obj+48#32) io src bs
  returnAddress : a.get 1=ret
  returnAligned : ret &&& ~~~1=ret
  keep : ResponseHeadCallee.Keep original a []
  csr : a.sameCsr original
  outside : ∀ x,(∀ i : Fin 89,x≠obj+BitVec.ofNat 32 i.val) → pre x=before x

/-- The real UART return preserves the caller and its prefix fields while
    moving only the declared UART future fields to their completed values. -/
theorem finish {original a before pre obj io src bs ret suffix c ram g}
    (prepared : Prepared original a before pre obj io src bs ret)
    (h : UartWritePhase.Returned a pre (obj+48#32) io src bs suffix c ram g) :
    c.pc=ret ∧ ResponseHeadCallee.Keep original c [] ∧ c.sameCsr original ∧
      ViewFrame.Region pre ram obj 48 ∧
      (∀ x,(∀ i : Fin 89,x≠obj+BitVec.ofNat 32 i.val) → ram x=before x) ∧
      ram=UartWriteAll.memory pre (obj+48#32) io src bs ∧
      ∃ p,g.phase=.reply p ∧ p.remaining=suffix := by
  obtain ⟨returned,memory,queue⟩ := h
  have frame : ∀ x,(∀ i : Fin 41,x≠(obj+48#32)+BitVec.ofNat 32 i.val) → ram x=pre x := by
    intro x apart
    rw [memory]
    unfold UartWriteAll.memory
    split
    · exact UartWriteZero.frame _ _ _ _ x apart
    · exact UartWriteNonzero.frame _ _ _ _ _ x apart
  refine ⟨by rw [returned.pc,prepared.returnAddress,prepared.returnAligned],
    (fun r kept safe => (ResponseHeadCallee.returned returned r kept).trans (prepared.keep r kept safe)),
    returned.csr.trans prepared.csr,SendUartFrame.prefixRegion frame,
    (fun x apart => (SendUartFrame.outside frame x apart).trans (prepared.outside x apart)),memory,queue⟩

theorem head (c : Core) (ram : Word → BitVec 8) (obj io src body flag : Word)
    (bs : List (BitVec 8)) (hl : bs.length≤120)
    (h8 : c.get 8=obj) (h18 : c.get 18=obj+48#32) (h19 : c.get 19=src)
    (h10 : c.get 10=body) (h11 : c.get 11=BitVec.ofNat 32 bs.length) (h22 : c.get 22=flag)
    (hm : Memory.Block B obj 89) (ha : obj.toNat%4=0) (hio : ramRead ram (obj+16#32) .w=io)
    (hs : ReadBytes.Span B img ram src bs) (hw : src.toNat+bs.length<2^32)
    (hsep : WordRegions.Disjoint src bs.length obj 89)
    (masked : c.mie_=false) (hp : c.pc=0x80000408#32) :
    ∃ a,Quiet.Steps B img 12 ⟨c,ram⟩ ⟨a,SendHeadUart.prepared ram obj io src body flag bs⟩ ∧
      Prepared c a ram (SendHeadUart.prepared ram obj io src body flag bs) obj io src bs 0x8000042e#32 := by
  obtain ⟨a,ta,pa,a12,a10,a1,fa,ka⟩ := SendHeadUartCall.contract B c ram obj io src body flag bs.length hl h8 h18 h19 h10 h11 h22 hm ha hio hp
  let pre := SendHeadUart.prepared ram obj io src body flag bs
  have source : ReadBytes.Span B img pre src bs := ReadFrame.span hs (fun i => SendHeadUartCallData.frame ram obj io src body flag bs.length _ (hsep i))
  have fresh : pre ((obj+48#32)+40#32)=0#8 := by
    rw [BitVec.add_assoc,show 48#32+40#32=88#32 by decide +kernel]
    exact SendHeadUartCallData.slot88 _ _ _ _ _ _ _
  have p0 : ramRead pre (obj+48#32) .w=io := SendHeadUartCallData.slot48 _ _ _ _ _ _ _
  have p4 : ramRead pre ((obj+48#32)+4#32) .w=src := by
    rw [BitVec.add_assoc,show 48#32+4#32=52#32 by decide +kernel]
    exact SendHeadUartCallData.slot52 _ _ _ _ _ _ _
  have p8 : ramRead pre ((obj+48#32)+8#32) .w=BitVec.ofNat 32 bs.length := by
    rw [BitVec.add_assoc,show 48#32+8#32=56#32 by decide +kernel]
    exact SendHeadUartCallData.slot56 _ _ _ _ _ _ _
  have input : UartWritePhase.Input a pre (obj+48#32) io src bs :=
    ⟨pa,a10,Memory.sub_block hm (by decide : 0<41) (by decide : 48+41≤89),Memory.word_aligned obj 12 ha,
      fresh,p0,p4,p8,source,hw,Subregion.right hsep 48 41 (by decide),(congrArg Prod.fst ka).trans masked⟩
  refine ⟨a,ta,input,a1,by decide +kernel,?_,ka,?_⟩
  · intro r hrreg safe
    apply fa r
    all_goals intro eq;subst r;simp [ResponseHeadCallee.Registers] at hrreg
  · intro x apart
    exact SendHeadUartCallData.frame ram obj io src body flag bs.length x apart

theorem body (c : Core) (ram : Word → BitVec 8) (obj io src : Word)
    (bs : List (BitVec 8)) (hl : bs.length≤832)
    (h8 : c.get 8=obj) (h18 : c.get 18=obj+48#32)
    (hm : Memory.Block B obj 89) (ha : obj.toNat%4=0)
    (hcap : ramRead ram (obj+4#32) .w=832#32) (hbody : ramRead ram (obj+20#32) .w=BitVec.ofNat 32 bs.length)
    (hptr : ramRead ram (obj+0#32) .w=src) (hio : ramRead ram (obj+16#32) .w=io)
    (hs : ReadBytes.Span B img ram src bs) (hw : src.toNat+bs.length<2^32)
    (hsep : WordRegions.Disjoint src bs.length obj 89)
    (masked : c.mie_=false) (hp : c.pc=0x8000042e#32) :
    ∃ a,Quiet.Steps B img 12 ⟨c,ram⟩ ⟨a,SendBodyUart.prepared ram obj io src bs⟩ ∧
      Prepared c a ram (SendBodyUart.prepared ram obj io src bs) obj io src bs 0x8000044e#32 := by
  obtain ⟨a,ta,pa,a12,a11,a10,a1,fa,ka⟩ := SendBodyUartCall.contract B c ram obj io src bs.length hl h8 h18 hm ha hcap hbody hptr hio hp
  let pre := SendBodyUart.prepared ram obj io src bs
  have source : ReadBytes.Span B img pre src bs := ReadFrame.span hs (fun i => SendBodyUartCallData.frame ram obj io src bs.length _ (hsep i))
  have fresh : pre ((obj+48#32)+40#32)=0#8 := by
    rw [BitVec.add_assoc,show 48#32+40#32=88#32 by decide +kernel]
    exact SendBodyUartCallData.slot88 _ _ _ _ _
  have p0 : ramRead pre (obj+48#32) .w=io := SendBodyUartCallData.slot48 _ _ _ _ _
  have p4 : ramRead pre ((obj+48#32)+4#32) .w=src := by
    rw [BitVec.add_assoc,show 48#32+4#32=52#32 by decide +kernel]
    exact SendBodyUartCallData.slot52 _ _ _ _ _
  have p8 : ramRead pre ((obj+48#32)+8#32) .w=BitVec.ofNat 32 bs.length := by
    rw [BitVec.add_assoc,show 48#32+8#32=56#32 by decide +kernel]
    exact SendBodyUartCallData.slot56 _ _ _ _ _
  have input : UartWritePhase.Input a pre (obj+48#32) io src bs :=
    ⟨pa,a10,Memory.sub_block hm (by decide : 0<41) (by decide : 48+41≤89),Memory.word_aligned obj 12 ha,
      fresh,p0,p4,p8,source,hw,Subregion.right hsep 48 41 (by decide),(congrArg Prod.fst ka).trans masked⟩
  refine ⟨a,ta,input,a1,by decide +kernel,?_,ka,?_⟩
  · intro r hrreg safe
    apply fa r
    all_goals intro eq;subst r;simp [ResponseHeadCallee.Registers] at hrreg
  · intro x apart
    exact SendBodyUartCallData.frame ram obj io src bs.length x apart

end E5R.Thermostat.SendUartReactive
