-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Param
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ParamDigitsQuiet
import Projects.thermostat.ParamPrefixQuiet
import Projects.thermostat.ParamReturnQuiet
import Projects.thermostat.ParamSetupQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.Param
theorem missing_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (req : Word)
    (hm : Memory.Block B req 372) (ha : req.toNat%4 = 0) (hz : ramRead ram (req+368#32) .w = 0#32)
    (hp : c.pc = 0x8000278a#32) (hreq : c.get 10 = req) (h11 : c.get 11 = 0#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800027be#32 ∧
      (∀ r : Reg, r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 0#32 0x8000278e#32
  let d := c1.goto 0x800027be#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact pm2147493770) fun o => ?_
    rw [exec_load,hreq,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned req 92 ha) (Memory.block_access hm (off := 368) (by decide) (by decide)),hz,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000278e#32).getLsbD 0 = false;decide) pm2147493774 fun o => ?_
    have hv11 : c1.get 11 = 0#32 := by simp [c1,Core.wr_get_ne,h11]
    have hv12 : c1.get 12 = 0#32 := by simp [c1,Core.wr_get]
    rw [exec_branch,hv11,hv12]
    have ht : taken .geu 0#32 0#32 = true := by decide +kernel
    rw [ht]
    simp only [ite_true]
    change interp B img o (jump c1 (0x8000278e#32+48#32)) ram 0 [] = _
    rw [show 0x8000278e#32+48#32 = 0x800027be#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,by rfl⟩
  intro r hr;simp [d,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.Param
namespace E5R.Thermostat.Param
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (req : Word)
    (first : Option (List (BitVec 8))) (h : Pre B ram req first)
    (hp : c.pc = 0x8000278a#32) (hreq : c.get 10 = req) (h11 : c.get 11 = 0#32) :
    ∃ d n, n ≤ 203 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      ParamReturn.Result d (first.bind WireSpec.parseU32) ∧ Frame c d ∧ d.sameCsr c := by
  cases h with
  | missing hm ha hz =>
    obtain ⟨a,ht,apc,aregs,acsr⟩ := E5R.Thermostat.Param.missing_quiet B c ram req hm ha hz hp hreq h11
    obtain ⟨d,hr,dpc,dresult,dregs,dcsr⟩ := E5R.Thermostat.ParamReturn.none_quiet B a ram apc
    refine ⟨d,4,by decide,ht.trans hr,?_,dresult,?_,dcsr.trans acsr⟩
    · rw [dpc,aregs 1 (by decide)]
    · intro r h5 h10 h11 h12 h13 h14 h15 h16 h17
      exact (dregs r h10).trans (aregs r h12)
  | @present pathPtr path s e count hc =>
    obtain ⟨a,hprefix,apc,a11,a14,a12,aregs,acsr⟩ := E5R.Thermostat.ParamPrefix.contract_quiet B c ram req pathPtr path s e count hc hp hreq h11
    have a10 : a.get 10 = req := (aregs 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hreq
    have ara : a.get 1 = c.get 1 := aregs 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    by_cases hlen : 1 ≤ e-s ∧ e-s ≤ 10
    · have apc' : a.pc = 0x800027c2#32 := by simpa only [ite_eq_left hlen] using apc
      obtain ⟨b,hsetup,bpc,b11,b13,b10,b14,bregs,bcsr⟩ := E5R.Thermostat.ParamSetup.contract_quiet B a ram req pathPtr path s e count hc hlen apc' a10 a11 a14
      have b12 : b.get 12 = BitVec.ofNat 32 (ParamInput.captured path s e).length := by
        rw [hc.length]
        exact (bregs 12 (by decide) (by decide) (by decide) (by decide)).trans a12
      have blen : 1 ≤ (ParamInput.captured path s e).length ∧ (ParamInput.captured path s e).length ≤ 10 := by rw [hc.length];exact hlen
      obtain ⟨d,n,hn,hbody,dpc,dresult,dregs,dcsr⟩ := E5R.Thermostat.ParamDigits.contract_quiet B b ram (pathPtr+BitVec.ofNat 32 s)
        (ParamInput.captured path s e) hc.span blen bpc b11 b13 b12 b14 b10
      refine ⟨d,15+6+n,by omega,(hprefix.trans hsetup).trans hbody,?_,dresult,?_,dcsr.trans (bcsr.trans acsr)⟩
      · rw [dpc,bregs 1 (by decide) (by decide) (by decide) (by decide),ara]
      · intro r h5 h10 h11 h12 h13 h14 h15 h16 h17
        exact (dregs r h5 h10 h11 h12 h13 h14 h15 h16 h17).trans
          ((bregs r h10 h11 h13 h14).trans (aregs r h11 h12 h13 h14 h15))
    · have apc' : a.pc = 0x800027be#32 := by simpa only [ite_eq_right hlen] using apc
      obtain ⟨d,hr,dpc,dresult,dregs,dcsr⟩ := E5R.Thermostat.ParamReturn.none_quiet B a ram apc'
      refine ⟨d,17,by decide,hprefix.trans hr,?_,?_,?_,dcsr.trans acsr⟩
      · rw [dpc,ara]
      · have hbad : ¬(1 ≤ (ParamInput.captured path s e).length ∧
            (ParamInput.captured path s e).length ≤ 10 ∧ (ParamInput.captured path s e).all DecimalSpec.digit = true) := by
          intro hh
          rw [hc.length] at hh
          exact hlen ⟨hh.1,hh.2.1⟩
        simpa only [Option.bind,WireSpec.parseU32,ite_eq_right hbad] using dresult
      · intro r h5 h10 h11 h12 h13 h14 h15 h16 h17
        exact (dregs r h10).trans (aregs r h11 h12 h13 h14 h15)

end E5R.Thermostat.Param
