-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatArgumentPiece
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.FormatArgumentCallQuiet
import Projects.thermostat.FormatArgumentPrepareQuiet
import Projects.thermostat.FormatArgumentReturnQuiet
import Projects.thermostat.FormatCallbackQuiet
import Projects.thermostat.FormatEngineNextQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatArgumentPiece
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p obj args desc dst : Word)
    (cap pos idx : Nat) (value : FormatValue.Value) (next : BitVec 8)
    (hr : FormatEngineReady.Ready c (p+160#32) obj args desc idx 192#8) (hi : idx < 8)
    (hm : Memory.Block B (args+BitVec.ofNat 32 (8*idx)) 8) (ha : (args+BitVec.ofNat 32 (8*idx)).toNat%4 = 0)
    (hptr : ramRead ram (args+BitVec.ofNat 32 (8*idx)) .w = FormatValue.pointer value)
    (hmethod : ramRead ram ((args+BitVec.ofNat 32 (8*idx))+4#32) .w = FormatValue.entry value)
    (hfmt : Memory.Block B (p+160#32) 16) (hfmtAlign : (p+160#32).toNat%4 = 0)
    (h : FormatCallbackData.Data B (FormatArgumentCall.memory ram (p+160#32) obj) p (p+160#32) obj dst cap pos value)
    (hfit : pos+(FormatValue.bytes value).length ≤ cap)
    (hnext : ReadBytes.Byte B img ram (desc+1#32) next) (hreadonly : B.inRam (desc+1#32) 1 = false)
    (hstr : B.inRam 0x80005c10#32 4 = false) (hchar : B.inRam 0x80005c14#32 4 = false)
    (hrom : ∀ i : Fin 100, ∀ unit : Bool, B.inRam (DigitTable.address i unit) 1 = false) :
    ∃ d n r, n ≤ 312 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = FormatEngineNext.resultPc next ∧ d.get 2 = p+160#32 ∧
      (next.toNat ≠ 0 → FormatEngineReady.Ready d (p+160#32) obj args (desc+1#32) (idx+1) next) ∧
      d.get 27 = c.get 27 ∧ d.sameCsr c ∧
      AppendEffect.Effect B ram r p obj dst 176 cap pos (FormatValue.bytes value) := by
  obtain ⟨a,ta,apc,a10,a20,a11,a12,ar,ac⟩ := E5R.Thermostat.FormatArgumentPrepare.contract_quiet B c ram args desc (FormatValue.pointer value) (FormatValue.entry value) idx hi
    hr.arguments hr.descriptor hr.tagWord hr.longTag hr.argumentTag hr.index hm ha hptr hmethod hr.pc
  have asp : a.get 2 = p+160#32 := (ar 2 (by decide) (by decide) (by decide) (by decide)).trans hr.spReg
  have a19 : a.get 19 = obj := (ar 19 (by decide) (by decide) (by decide) (by decide)).trans hr.writer
  have a18 : a.get 18 = 0x80005c04#32 := (ar 18 (by decide) (by decide) (by decide) (by decide)).trans hr.vtable
  have a26 : a.get 26 = 0x60000020#32 := (ar 26 (by decide) (by decide) (by decide) (by decide)).trans hr.flags
  let mid := FormatArgumentCall.memory ram (p+160#32) obj
  obtain ⟨b,tb,bpc,b1,b11,br,bc⟩ := E5R.Thermostat.FormatArgumentCall.contract_quiet B a ram (p+160#32) obj (FormatValue.entry value) apc asp a19 a18 a26 a12 hfmt hfmtAlign
  have bpc' : b.pc = FormatValue.entry value := bpc.trans (FormatValue.entry_even value)
  have bsp : b.get 2 = p+160#32 := (br 2 (by decide) (by decide)).trans asp
  have b10 : b.get 10 = FormatValue.pointer value := (br 10 (by decide) (by decide)).trans a10
  obtain ⟨z,k,r,hk,tz,hz,z10,he⟩ := E5R.Thermostat.FormatCallback.contract_quiet B b mid p (p+160#32) obj dst cap pos value h bpc' bsp b10 b11 hfit hstr hchar hrom
  have zpc : z.pc = 0x800049d8#32 := by rw [hz.pc,b1];decide +kernel
  have hcs := Callee.of_returned hz
  have z24 : z.get 24 = BitVec.ofNat 32 idx := (hcs 24 (by decide)).trans
    ((br 24 (by decide) (by decide)).trans ((ar 24 (by decide) (by decide) (by decide) (by decide)).trans hr.index))
  have z20 : z.get 20 = desc+1#32 := (hcs 20 (by decide)).trans ((br 20 (by decide) (by decide)).trans a20)
  obtain ⟨u,tu,upc,u24,ur,uc⟩ := E5R.Thermostat.FormatArgumentReturn.contract_quiet B z r idx z10 z24 zpc
  have u20 : u.get 20 = desc+1#32 := (ur 20 (by decide)).trans z20
  obtain ⟨d,td,dpc,d21,d12,dr,dc⟩ := E5R.Thermostat.FormatEngineNext.contract_quiet B u r (desc+1#32) next upc u20 (hnext.readonly hreadonly)
  have keep (reg : Reg) (hc : Callee.Saved reg) (h20 : reg ≠ 20) (h21 : reg ≠ 21) (h24 : reg ≠ 24) : d.get reg = c.get reg := by
    have hn (q : Reg) (hq : q.val < 18) (h8 : q ≠ 8) (h9 : q ≠ 9) := Callee.ne_low reg q hc hq h8 h9
    exact (dr reg h21 (hn 12 (by decide) (by decide) (by decide))).trans ((ur reg h24).trans
      ((hcs reg hc).trans ((br reg (hn 1 (by decide) (by decide) (by decide)) (hn 11 (by decide) (by decide) (by decide))).trans
        (ar reg (hn 10 (by decide) (by decide) (by decide)) h20 (hn 11 (by decide) (by decide) (by decide)) (hn 12 (by decide) (by decide) (by decide))))))
  have dsp : d.get 2 = p+160#32 := (dr 2 (by decide) (by decide)).trans ((ur 2 (by decide)).trans (hz.sp.trans bsp))
  have d24 : d.get 24 = BitVec.ofNat 32 (idx+1) := (dr 24 (by decide) (by decide)).trans u24
  have he0 : AppendEffect.Effect B mid r p obj dst 176 cap pos (FormatValue.bytes value) := AppendEffect.expand he (by decide)
  have heFull : AppendEffect.Effect B ram r p obj dst 176 cap pos (FormatValue.bytes value) := AppendEffect.rebase he0 (by
    intro x hx
    apply FormatArgumentCall.frame
    intro i
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨160+i.val,by have := i.isLt;omega⟩)
  refine ⟨d,9+6+k+2+3,r,by omega,((((ta.trans tb).trans tz).trans tu).trans td),dpc,dsp,?_,
    keep 27 (by decide) (by decide) (by decide) (by decide),(((dc.trans uc).trans hz.csr).trans bc).trans ac,heFull⟩
  intro hn
  refine ⟨by simpa only [FormatEngineNext.resultPc,ite_eq_right hn] using dpc,dsp,?_,d12,?_,?_,d21,?_,?_,d24,?_,?_⟩
  · exact (keep 9 (by decide) (by decide) (by decide) (by decide)).trans hr.arguments
  · exact (keep 18 (by decide) (by decide) (by decide) (by decide)).trans hr.vtable
  · exact (keep 19 (by decide) (by decide) (by decide) (by decide)).trans hr.writer
  · exact (keep 22 (by decide) (by decide) (by decide) (by decide)).trans hr.writeStr
  · exact (keep 23 (by decide) (by decide) (by decide) (by decide)).trans hr.longTag
  · exact (keep 25 (by decide) (by decide) (by decide) (by decide)).trans hr.argumentTag
  · exact (keep 26 (by decide) (by decide) (by decide) (by decide)).trans hr.flags

end E5R.Thermostat.FormatArgumentPiece
