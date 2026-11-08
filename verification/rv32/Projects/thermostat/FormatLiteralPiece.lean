import Projects.thermostat.FormatLiteralCall
import Projects.thermostat.FormatLiteralReturn
import Projects.thermostat.FormatEngineNext
import Projects.thermostat.FormatEngineReady
import Projects.thermostat.AppendEffect
import Projects.thermostat.Callee
import Projects.thermostat.ReadOnlyByte
import Projects.thermostat.CursorLayoutPreserve
import Projects.thermostat.CursorFull
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.FormatLiteralPiece
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p obj args desc dst : Word)
    (cap pos idx : Nat) (xs : List (BitVec 8)) (next : BitVec 8)
    (hr : FormatEngineReady.Ready c (p+32#32) obj args desc idx (BitVec.ofNat 8 xs.length))
    (h : CursorInput.Layout B ram p obj (desc+1#32) dst cap pos xs) (hfit : pos+xs.length ≤ cap)
    (hnext : ReadBytes.Byte B img ram ((desc+1#32)+BitVec.ofNat 32 xs.length) next)
    (hrom : B.inRam ((desc+1#32)+BitVec.ofNat 32 xs.length) 1 = false) :
    ∃ d n r, n ≤ 6*xs.length+54 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = FormatEngineNext.resultPc next ∧ d.get 2 = p+32#32 ∧
      (next.toNat ≠ 0 → FormatEngineReady.Ready d (p+32#32) obj args ((desc+1#32)+BitVec.ofNat 32 xs.length) idx next) ∧
      d.get 27 = c.get 27 ∧ d.sameCsr c ∧ AppendEffect.Effect B ram r p obj dst 32 cap pos xs := by
  have hlen := h.short
  have h21 : c.get 21 = BitVec.ofNat 32 xs.length := by
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show xs.length < 256 by omega)] using hr.tagWord
  obtain ⟨a,ta,apc,a10,a20,a11,a12,a1,ar,ac⟩ := FormatLiteralCall.contract B c ram obj desc xs.length hlen hr.writer hr.descriptor h21 hr.writeStr hr.pc
  have asp : a.get 2 = p+32#32 := (ar 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr.spReg
  have hpre := CursorInput.pre_of_layout h apc asp a10 a11 a12
  obtain ⟨z,k,r,hk,tz,hz,zh⟩ := Cursor.contract_full B a ram p obj (desc+1#32) dst cap pos xs hpre
  have zpc : z.pc = 0x800049fc#32 := by rw [hz.returned.pc,a1];decide +kernel
  have z10 : z.get 10 = 0#32 := by simpa only [Cursor.resultWord,ite_eq_left hfit] using hz.result
  have hcs := Callee.of_cursor hz.returned zh
  have z20 : z.get 20 = desc+1#32 := (hcs 20 (by decide)).trans a20
  have z21 : z.get 21 = BitVec.ofNat 32 xs.length := (hcs 21 (by decide)).trans
    ((ar 21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h21)
  obtain ⟨u,tu,upc,u20,ur,uc⟩ := FormatLiteralReturn.contract B z r (desc+1#32) xs.length z10 z20 z21 zpc
  obtain ⟨d,td,dpc,d21,d12,dr,dc⟩ := FormatEngineNext.contract B u r _ next upc u20 (hnext.readonly hrom)
  have keep (reg : Reg) (hc : Callee.Saved reg) (h20 : reg ≠ 20) (h21n : reg ≠ 21) : d.get reg = c.get reg := by
    have hn (q : Reg) (hq : q.val < 18) (h8 : q ≠ 8) (h9 : q ≠ 9) := Callee.ne_low reg q hc hq h8 h9
    exact (dr reg h21n (hn 12 (by decide) (by decide) (by decide))).trans ((ur reg h20).trans
      ((hcs reg hc).trans (ar reg (hn 10 (by decide) (by decide) (by decide)) h20 (hn 11 (by decide) (by decide) (by decide))
        (hn 12 (by decide) (by decide) (by decide)) (hn 1 (by decide) (by decide) (by decide)))))
  have dsp : d.get 2 = p+32#32 := (dr 2 (by decide) (by decide)).trans ((ur 2 (by decide)).trans (hz.returned.sp.trans asp))
  refine ⟨d,7+k+3+3,r,by omega,((ta.trans tz).trans tu).trans td,dpc,dsp,?_,keep 27 (by decide) (by decide) (by decide),
    ((dc.trans uc).trans hz.returned.csr).trans ac,AppendEffect.of_cursor hz⟩
  intro hn
  refine ⟨by simpa only [FormatEngineNext.resultPc,ite_eq_right hn] using dpc,dsp,?_,d12,?_,?_,d21,?_,?_,?_,?_,?_⟩
  · exact (keep 9 (by decide) (by decide) (by decide)).trans hr.arguments
  · exact (keep 18 (by decide) (by decide) (by decide)).trans hr.vtable
  · exact (keep 19 (by decide) (by decide) (by decide)).trans hr.writer
  · exact (keep 22 (by decide) (by decide) (by decide)).trans hr.writeStr
  · exact (keep 23 (by decide) (by decide) (by decide)).trans hr.longTag
  · exact (keep 24 (by decide) (by decide) (by decide)).trans hr.index
  · exact (keep 25 (by decide) (by decide) (by decide)).trans hr.argumentTag
  · exact (keep 26 (by decide) (by decide) (by decide)).trans hr.flags
end E5R.Thermostat.FormatLiteralPiece
