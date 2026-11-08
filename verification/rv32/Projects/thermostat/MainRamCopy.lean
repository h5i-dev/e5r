import Projects.thermostat.MainRamCopyLoop
import Projects.thermostat.CopyAlignedEntryQuiet
import Projects.thermostat.CopyTailRunQuiet
import Projects.thermostat.AlignedCopyMemory
import Projects.thermostat.CopyBits
import Projects.thermostat.Subregion
namespace E5R.Thermostat.MainRamCopy
open E5R E5R.Thermostat

/-- Complete actual aligned RAM-to-RAM memcpy, with a separated source snapshot.
    The mask arithmetic is explicit and is discharged for the real 256-byte call. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp src dst : Word) (ws : List Word)
    (hp : c.pc=0x80005182#32) (hsp : c.get 2=sp+16#32)
    (h10 : c.get 10=dst) (h11 : c.get 11=src) (h12 : c.get 12=BitVec.ofNat 32 (4*ws.length))
    (hn : 4≤ws.length) (hs : HeadCopyRamSource.Source B ram src ws)
    (apart : MainRamCopySource.Apart src dst ws.length) (had : dst.toNat%4=0)
    (hd : Memory.Block B dst (4*ws.length)) (hw : dst.toNat+4*ws.length<2^32)
    (hm : BitVec.ofNat 32 (4*ws.length) &&& 0xfffffffc#32=BitVec.ofNat 32 (4*ws.length)) :
    ∃ d, Quiet.Steps B img (24+5*ws.length) ⟨c,ram⟩ ⟨d,AlignedCopyLoop.writes ram dst ws⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10=dst ∧
      Bytes.Span B (AlignedCopyLoop.writes ram dst ws) dst (AlignedCopyLoop.bytes ws) ∧
      (∀ x, (∀ i : Fin (4*ws.length), x≠dst+BitVec.ofNat 32 i.val) →
        AlignedCopyLoop.writes ram dst ws x=ram x) := by
  have nb : 4*ws.length<2^32 := by omega
  obtain ⟨a,ta,apc,asp,a10,a11,a12,a13,a14,a15,a16,ar,ac⟩ := CopyAlignedEntry.contract_quiet B c ram sp src dst
    (4*ws.length) (4*ws.length) hp hsp h10 h11 h12 (by omega) nb (by omega) hw hs.aligned had hm
  obtain ⟨z,tz,zpc,z14,z16,zr,zc⟩ := MainRamCopyLoop.contract B a ram src dst ws (by omega) apc a16 a14 a13 hs apart had hd hw
  have low : BitVec.ofNat 32 (4*ws.length) &&& 3#32=BitVec.ofNat 32 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [CopyBits.low2]
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nb]
    omega
  have endNat := WordZero.add_nat dst (4*ws.length) hw
  have blockEnd : Memory.Block B (dst+BitVec.ofNat 32 (4*ws.length)) 0 :=
    Subregion.block hd nb hw (4*ws.length) 0 (by omega)
  obtain ⟨d,td,dpc,dsp,d10,dr,dc⟩ := CopyTailRun.contract_quiet B z (AlignedCopyLoop.writes ram dst ws) src
    (dst+BitVec.ofNat 32 (4*ws.length)) (4*ws.length) (4*ws.length) [] zpc
    ((zr 11 (by decide) (by decide) (by decide)).trans a11)
    ((zr 12 (by decide) (by decide) (by decide)).trans a12)
    ((zr 13 (by decide) (by decide) (by decide)).trans a13)
    ((zr 15 (by decide) (by decide) (by decide)).trans a15) low (by rw [endNat];exact hw)
    (by exact ⟨by decide,by have := (src+BitVec.ofNat 32 (4*ws.length)).isLt;simpa only [List.length_nil,Nat.add_zero] using Nat.le_of_lt this,fun i => Fin.elim0 i⟩) (fun i => Fin.elim0 i) blockEnd
  have keep (r : Reg) (hr : CopyRegs.Preserved r) : z.get r=c.get r :=
    (zr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 16 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 17 hr (by decide) (by decide) (by decide) (by decide))).trans (ar r hr)
  have ret : FormatCursor.Returned c d := by
    apply CopyRegs.returned
    · rw [dpc,keep 1 (by decide)]
    · rw [dsp,zr 2 (by decide) (by decide) (by decide),asp,←hsp]
    · exact (dc.trans zc).trans ac
    · intro r hr;exact (dr r hr).trans (keep r hr)
  refine ⟨d,?_,ret,d10.trans ((zr 10 (by decide) (by decide) (by decide)).trans a10),AlignedCopyLoop.written ram dst ws hd hw,AlignedCopyLoop.frame ram dst ws⟩
  have steps := (ta.trans tz).trans td
  have count : 17+5*ws.length+(5+6*(([] : List (BitVec 8)).length)+2)=24+5*ws.length := by simp only [List.length_nil];omega
  simpa only [count,ByteWrite.write] using steps
end E5R.Thermostat.MainRamCopy
