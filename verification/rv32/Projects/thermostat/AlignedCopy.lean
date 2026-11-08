import Projects.thermostat.CopyAlignedEntry
import Projects.thermostat.AlignedCopyResult
import Projects.thermostat.CopyTailRun
import Projects.thermostat.ReadOnlySpan
namespace E5R.Thermostat.AlignedCopy
open E5R E5R.Thermostat

/-- Complete real optimized memcpy on aligned ROM/output with a word bulk and
    0..3 final bytes. The bulk-mask premise is pure arithmetic, discharged for
    each real constant-length error string by the caller proof. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp src dst : Word)
    (ws : List Word) (tail : List (BitVec 8))
    (hp : c.pc=0x80005182#32) (hsp : c.get 2=sp+16#32)
    (h10 : c.get 10=dst) (h11 : c.get 11=src) (h12 : c.get 12=BitVec.ofNat 32 (4*ws.length+tail.length))
    (hn : 4≤ws.length) (ht : tail.length<4) (hs : AlignedSource.Source B src ws) (had : dst.toNat%4=0)
    (hd : Memory.Block B dst (4*ws.length+tail.length)) (hw : dst.toNat+(4*ws.length+tail.length)<2^32)
    (hm : BitVec.ofNat 32 (4*ws.length+tail.length) &&& 0xfffffffc#32 = BitVec.ofNat 32 (4*ws.length))
    (hx : ReadBytes.Span B img ram (src+BitVec.ofNat 32 (4*ws.length)) tail)
    (hro : ∀ i : Fin tail.length, B.inRam ((src+BitVec.ofNat 32 (4*ws.length))+BitVec.ofNat 32 i.val) 1=false) :
    ∃ d n, n≤24+5*ws.length+6*tail.length ∧
      DetSteps B img n ⟨c,ram⟩ ⟨d,AlignedCopyResult.memory ram dst ws tail⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10=dst ∧
      Bytes.Span B (AlignedCopyResult.memory ram dst ws tail) dst (AlignedCopyLoop.bytes ws++tail) ∧
      (∀ x, (∀ i : Fin (4*ws.length+tail.length), x≠dst+BitVec.ofNat 32 i.val) →
        AlignedCopyResult.memory ram dst ws tail x=ram x) := by
  have hnb : 4*ws.length+tail.length<2^32 := by omega
  have hm2 : BitVec.ofNat 32 (4*ws.length+tail.length) &&& 3#32=BitVec.ofNat 32 tail.length := by
    apply BitVec.eq_of_toNat_eq
    rw [CopyBits.low2]
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hnb,Nat.mod_eq_of_lt (show tail.length<2^32 by omega)]
    omega
  obtain ⟨a,ta,apc,asp,a10,a11,a12,a13,a14,a15,a16,ar,ac⟩ := CopyAlignedEntry.contract B c ram sp src dst
    (4*ws.length+tail.length) (4*ws.length) hp hsp h10 h11 h12 (by omega) hnb (by omega) (by omega) hs.aligned had hm
  have hbulk : Memory.Block B dst (4*ws.length) := by
    simpa only [BitVec.add_zero] using Subregion.block hd hnb hw 0 (4*ws.length) (by omega)
  obtain ⟨z,tz,zpc,z14,_,zr,zc⟩ := AlignedCopyLoop.contract B a ram src dst ws (by omega) apc a16 a14 a13 hs had hbulk (by omega)
  let wordram := AlignedCopyLoop.writes ram dst ws
  have next : ReadBytes.Span B img wordram (src+BitVec.ofNat 32 (4*ws.length)) tail := hx.readonly hro
  have hd' := Subregion.block hd hnb hw (4*ws.length) tail.length (by exact Nat.le_refl _)
  have hw' := Subregion.nowrap hw (4*ws.length) tail.length (by exact Nat.le_refl _)
  obtain ⟨d,td,dpc,dsp,d10,dr,dc⟩ := CopyTailRun.contract B z wordram src (dst+BitVec.ofNat 32 (4*ws.length))
    (4*ws.length+tail.length) (4*ws.length) tail zpc
    ((zr 11 (by decide) (by decide) (by decide)).trans a11)
    ((zr 12 (by decide) (by decide) (by decide)).trans a12)
    ((zr 13 (by decide) (by decide) (by decide)).trans a13)
    ((zr 15 (by decide) (by decide) (by decide)).trans a15) hm2 hw' next hro hd'
  have keep (reg : Reg) (hr : CopyRegs.Preserved reg) : z.get reg=c.get reg := by
    exact (zr reg (CopyRegs.ne_low reg 14 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low reg 16 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low reg 17 hr (by decide) (by decide) (by decide) (by decide))).trans (ar reg hr)
  have fullkeep (reg : Reg) (hr : CopyRegs.Preserved reg) : d.get reg=c.get reg := (dr reg hr).trans (keep reg hr)
  have fullpc : d.pc=c.get 1 &&& ~~~1 := by rw [dpc,keep 1 (by decide)]
  have fullsp : d.get 2=c.get 2 := by
    rw [dsp,zr 2 (by decide) (by decide) (by decide),asp,←hsp]
  have csr : d.sameCsr c := (dc.trans zc).trans ac
  refine ⟨d,17+5*ws.length+(5+6*tail.length+2),by omega,(ta.trans tz).trans td,
    CopyRegs.returned fullpc fullsp csr fullkeep,?_,AlignedCopyResult.written ram dst ws tail hd (by omega),AlignedCopyResult.frame ram dst ws tail⟩
  exact d10.trans ((zr 10 (by decide) (by decide) (by decide)).trans a10)
end E5R.Thermostat.AlignedCopy
