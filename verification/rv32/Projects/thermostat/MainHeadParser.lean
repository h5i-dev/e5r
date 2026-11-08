import Projects.thermostat.MainHeadCall
import Projects.thermostat.MainHeadLayout
import Projects.thermostat.HeadColdFuture
namespace E5R.Thermostat.MainHeadParser
open E5R E5R.Thermostat

def values (c : Core) (r : Reg) : Word := if r=1 then 0x80000a26#32 else c.get r

/-- Actual main call site, complete byte-derived parse_head and main return.
    The whole future object is framed, so its RX/config layout can be used by
    the next real polling iteration without assuming it survived the parser. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8))
    (hp : c.pc=0x80000a10#32) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32)
    (h12 : c.get 12=BitVec.ofNat 32 input.length) (layout : MainHeadLayout.At ram)
    (bytesAt : Bytes.At ram 0x80ffec14#32 input) (length : input.length≤2048)
    (stack : Memory.Block B 0x80ffea10#32 5312)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    ∃ n d after, 26≤n ∧ n≤7+HeadColdFutureComplete.budget (min input.length 1024) ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ d.pc=0x80000a26#32 ∧ d.get 2=0x80ffeb90#32 ∧
      HeadSaved.CoreAt d (values c) ∧ HeadFinalResult.At after 0x80fffd38#32 (HttpRequestBytes.parse input 1024 1024) ∧
      ViewFrame.Region ram after 0x80ffec14#32 2048 ∧ ViewFrame.Region ram after 0x80fff814#32 449 ∧
      MainHeadLayout.At after ∧ (∀ state, AppState.At ram state → AppState.At after state) ∧ d.sameCsr c := by
  have object : Memory.Block B 0x80fff814#32 449 := by
    simpa only [show 0x80ffea10#32+3588#32=0x80fff814#32 by decide +kernel] using Memory.sub_block stack (off := 3588) (m := 449) (by decide) (by decide)
  obtain ⟨a,ta,apc,a11,a13,a10,a1,ar,ac⟩ := MainHeadCall.contract B c ram _ _ h8 h2 layout.rx layout.config object hp
  have asp := (ar 2 (by decide) (by decide) (by decide) (by decide)).trans h2
  have alen := (ar 12 (by decide) (by decide) (by decide) (by decide)).trans h12
  obtain ⟨n,d,after,lo,hi,trace,dpc,dsp,regs,result,rx,app,csr,future⟩ := HeadColdFuture.contract B a ram 0x80ffea10#32 input
    apc asp a10 a11 alen a13 stack (by decide +kernel) length layout.headLimit bytesAt layout.bodyLimit clOutside teOutside
  have returnPC : d.pc=0x80000a26#32 := by rw [dpc,a1];decide +kernel
  have mainFuture : ViewFrame.Region ram after 0x80fff814#32 449 := future
  have saved : HeadSaved.CoreAt d (values c) := by
    constructor
    · simpa only [values,ite_true] using regs.x1.trans a1
    · simpa only [values,show ¬((8 : Reg)=1) by decide,ite_false] using regs.x8.trans (ar 8 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((9 : Reg)=1) by decide,ite_false] using regs.x9.trans (ar 9 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((18 : Reg)=1) by decide,ite_false] using regs.x18.trans (ar 18 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((19 : Reg)=1) by decide,ite_false] using regs.x19.trans (ar 19 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((20 : Reg)=1) by decide,ite_false] using regs.x20.trans (ar 20 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((21 : Reg)=1) by decide,ite_false] using regs.x21.trans (ar 21 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((22 : Reg)=1) by decide,ite_false] using regs.x22.trans (ar 22 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((23 : Reg)=1) by decide,ite_false] using regs.x23.trans (ar 23 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((24 : Reg)=1) by decide,ite_false] using regs.x24.trans (ar 24 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((25 : Reg)=1) by decide,ite_false] using regs.x25.trans (ar 25 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((26 : Reg)=1) by decide,ite_false] using regs.x26.trans (ar 26 (by decide) (by decide) (by decide) (by decide))
    · simpa only [values,show ¬((27 : Reg)=1) by decide,ite_false] using regs.x27.trans (ar 27 (by decide) (by decide) (by decide) (by decide))
  exact ⟨7+n,d,after,by omega,by omega,ta.trans trace,returnPC,dsp,saved,result,rx,mainFuture,
    MainHeadLayout.preserve layout mainFuture,app rfl,csr.trans ac⟩
end E5R.Thermostat.MainHeadParser
