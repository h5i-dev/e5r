import Projects.thermostat.SendHeadUartCallData
import Projects.thermostat.SendUartFrame
import Projects.thermostat.ResponseHeadCallee
namespace E5R.Thermostat.SendHeadUart
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def prepared (ram : Word → BitVec 8) (obj io src body flag : Word) (bs : List (BitVec 8)) :=
  SendHeadUartCall.memory ram obj io src body flag bs.length

def memory (ram : Word → BitVec 8) (obj io src body flag : Word) (bs : List (BitVec 8)) :=
  UartWriteAll.memory (prepared ram obj io src body flag bs) (obj+48#32) io src bs

/-- Real caller stores construct the fresh UART future, whose checked THR
    event sequence is exactly the completed header bytes. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (obj io src body flag : Word)
    (bs : List (BitVec 8)) (slots : List UartTxLoop.Slot) (hl : bs.length≤120)
    (h8 : c.get 8=obj) (h18 : c.get 18=obj+48#32) (h19 : c.get 19=src)
    (h10 : c.get 10=body) (h11 : c.get 11=BitVec.ofNat 32 bs.length) (h22 : c.get 22=flag)
    (hm : Memory.Block B obj 89) (ha : obj.toNat%4=0) (hio : ramRead ram (obj+16#32) .w=io)
    (hs : ReadBytes.Span B img ram src bs) (hw : src.toNat+bs.length<2^32)
    (hsep : WordRegions.Disjoint src bs.length obj 89) (hlen : slots.length=bs.length)
    (hp : c.pc=0x80000408#32) :
    ∃ d, Observed.Steps B img (12+UartWriteAll.time bs slots) ⟨c,ram⟩ ⟨d,memory ram obj io src body flag bs⟩
      (UartTxLoop.reads slots) (UartTxLoop.events bs) ∧ d.pc=0x8000042e#32 ∧
      ResponseHeadCallee.Keep c d [] ∧ d.sameCsr c ∧
      ViewFrame.Region (prepared ram obj io src body flag bs) (memory ram obj io src body flag bs) obj 48 ∧
      (∀ x, (∀ i : Fin 89, x≠obj+BitVec.ofNat 32 i.val) → memory ram obj io src body flag bs x=ram x) := by
  obtain ⟨a,ta,pa,a12,a10,a1,fa,ka⟩ := SendHeadUartCall.contract B c ram obj io src body flag bs.length hl h8 h18 h19 h10 h11 h22 hm ha hio hp
  let pre := prepared ram obj io src body flag bs
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
  obtain ⟨d,td,hr,_,_,_,_,df⟩ := UartWriteAll.contract a pre (obj+48#32) io src bs slots pa a10
    (Memory.sub_block hm (by decide : 0<41) (by decide : 48+41≤89)) (Memory.word_aligned obj 12 ha)
    fresh p0 p4 p8 hlen source hw (Subregion.right hsep 48 41 (by decide))
  refine ⟨d,?_,?_,?_,hr.csr.trans ka,SendUartFrame.prefixRegion df,?_⟩
  · simpa only [memory,pre,List.nil_append] using ta.observed.trans td
  · rw [hr.pc,a1];decide +kernel
  · intro r hrreg _
    apply (ResponseHeadCallee.returned hr r hrreg).trans
    apply fa r
    all_goals intro he;subst r;simp [ResponseHeadCallee.Registers] at hrreg
  · intro x hx
    exact (SendUartFrame.outside df x hx).trans (SendHeadUartCallData.frame ram obj io src body flag bs.length x hx)
end E5R.Thermostat.SendHeadUart
