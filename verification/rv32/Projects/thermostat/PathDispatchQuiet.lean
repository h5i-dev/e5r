-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.PathDispatch
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.LenBranchQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.PathDispatch
theorem load_path_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (req p : Word) (xs : List (BitVec 8))
    (h : PathAt B ram req p xs) (addr next : Word) (hp : c.pc = addr) (ha : addr.getLsbD 0 = false)
    (hd : fetchDecode img addr = some (.load .w true 11 10 304#32,4#32))
    (hnext : addr+4#32 = next) (hreq : c.get 10 = req) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 11 p next,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];exact ha) (by rw [hp];exact hd) fun o => ?_
  rw [exec_load,hreq,interp_load_ram (B := B) (img := img) (w := .w) o
    (Memory.word_aligned req 76 h.aligned) (Memory.block_access h.object (off := 304) (by decide) (by decide)),h.pointer,hp,hnext];rfl

end E5R.Thermostat.PathDispatch
namespace E5R.Thermostat.PathDispatch
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (req p : Word) (xs : List (BitVec 8))
    (h : PathAt B ram req p xs) (hp : c.pc = 0x80001fb4#32) (hreq : c.get 10 = req) :
    ∃ d k, k ≤ 8 ∧ Quiet.Steps B img k ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = destination xs.length ∧
      ((xs.length = 5 ∨ xs.length = 9 ∨ xs.length = 6) → d.get 11 = p) ∧ Frame c d ∧ d.sameCsr c := by
  let n := xs.length
  let a := c.wr 11 (BitVec.ofNat 32 n) 0x80001fb8#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wd2147491764) fun o => ?_
    rw [exec_load,hreq,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned req 77 h.aligned) (Memory.block_access h.object (off := 308) (by decide) (by decide)),h.length,hp];rfl
  have fa : Frame c a := by intro r h1 h2;simp [a,Core.wr_get_ne,h1]
  have acsr : a.sameCsr c := Core.sameCsr_wr _ _ _ _
  have a11 : a.get 11 = BitVec.ofNat 32 n := by simp [a,Core.wr_get]
  obtain ⟨b,h5,bpc,bregs,bcsr⟩ := E5R.Thermostat.LenBranch.contract_quiet B a ram n 5 h.bytes.length (by decide) LenBranch.five rfl a11
  have fb : Frame a b := by intro r h1 h2;exact bregs r h2
  have b11 : b.get 11 = BitVec.ofNat 32 n := (bregs 11 (by decide)).trans a11
  by_cases hn5 : n = 5
  · have bpc' : b.pc = 0x800020aa#32 := by simpa only [ite_eq_left hn5,LenBranch.yes,LenBranch.five,ite_true] using bpc
    let d := b.wr 11 p 0x800020ae#32
    have sl := E5R.Thermostat.PathDispatch.load_path_quiet B b ram req p xs h 0x800020aa#32 0x800020ae#32 bpc' (by decide) wd2147492010 (by decide +kernel)
      ((fa.trans fb) 10 (by decide) (by decide) |>.trans hreq)
    have fd : Frame b d := by intro r h1 h2;simp [d,Core.wr_get_ne,h1]
    refine ⟨d,4,by decide,((Quiet.Steps.single s0).trans h5).trans (.single sl),?_,?_,(fa.trans fb).trans fd,(Core.sameCsr_wr b 11 _ _).trans (bcsr.trans acsr)⟩
    · change d.pc = destination n
      simp only [d,Core.wr_pc,destination,ite_eq_left hn5]
    · intro _;simp [d,Core.wr_get]
  · have bpc' : b.pc = 0x80001fbe#32 := by simpa only [ite_eq_right hn5,LenBranch.no,LenBranch.five,ite_true] using bpc
    obtain ⟨e,h9,epc,eregs,ecsr⟩ := E5R.Thermostat.LenBranch.contract_quiet B b ram n 9 h.bytes.length (by decide) LenBranch.nine bpc' b11
    have fe : Frame b e := by intro r h1 h2;exact eregs r h2
    have e11 : e.get 11 = BitVec.ofNat 32 n := (eregs 11 (by decide)).trans b11
    by_cases hn9 : n = 9
    · have epc' : e.pc = 0x8000201c#32 := by simpa only [ite_eq_left hn9,LenBranch.yes,LenBranch.nine,ite_true] using epc
      let d := e.wr 11 p 0x80002020#32
      have sl := E5R.Thermostat.PathDispatch.load_path_quiet B e ram req p xs h 0x8000201c#32 0x80002020#32 epc' (by decide) wd2147491868 (by decide +kernel)
        (((fa.trans fb).trans fe) 10 (by decide) (by decide) |>.trans hreq)
      have fd : Frame e d := by intro r h1 h2;simp [d,Core.wr_get_ne,h1]
      refine ⟨d,6,by decide,(((Quiet.Steps.single s0).trans h5).trans h9).trans (.single sl),?_,?_,((fa.trans fb).trans fe).trans fd,(Core.sameCsr_wr e 11 _ _).trans (ecsr.trans (bcsr.trans acsr))⟩
      · change d.pc = destination n
        simp only [d,Core.wr_pc,destination,ite_eq_right hn5,ite_eq_left hn9]
      · intro _;simp [d,Core.wr_get]
    · have epc' : e.pc = 0x80001fc4#32 := by simpa only [ite_eq_right hn9,LenBranch.no,LenBranch.nine,ite_true] using epc
      obtain ⟨f,h6,fpc,fregs,fcsr⟩ := E5R.Thermostat.LenBranch.contract_quiet B e ram n 6 h.bytes.length (by decide) LenBranch.six epc' e11
      have ff : Frame e f := by intro r h1 h2;exact fregs r h2
      by_cases hn6 : n = 6
      · have fpc' : f.pc = 0x80001fca#32 := by simpa only [ite_eq_left hn6,LenBranch.yes,LenBranch.six,Bool.false_eq_true,ite_false] using fpc
        let d := f.wr 11 p 0x80001fce#32
        have sl := E5R.Thermostat.PathDispatch.load_path_quiet B f ram req p xs h 0x80001fca#32 0x80001fce#32 fpc' (by decide) wd2147491786 (by decide +kernel)
          ((((fa.trans fb).trans fe).trans ff) 10 (by decide) (by decide) |>.trans hreq)
        have fd : Frame f d := by intro r h1 h2;simp [d,Core.wr_get_ne,h1]
        refine ⟨d,8,by decide,((((Quiet.Steps.single s0).trans h5).trans h9).trans h6).trans (.single sl),?_,?_,(((fa.trans fb).trans fe).trans ff).trans fd,(Core.sameCsr_wr f 11 _ _).trans (fcsr.trans (ecsr.trans (bcsr.trans acsr)))⟩
        · change d.pc = destination n
          simp only [d,Core.wr_pc,destination,ite_eq_right hn5,ite_eq_right hn9,ite_eq_left hn6]
        · intro _;simp [d,Core.wr_get]
      · refine ⟨f,7,by decide,(((Quiet.Steps.single s0).trans h5).trans h9).trans h6,?_,?_,((fa.trans fb).trans fe).trans ff,fcsr.trans (ecsr.trans (bcsr.trans acsr))⟩
        · change f.pc = destination n
          simpa only [destination,ite_eq_right hn5,ite_eq_right hn9,ite_eq_right hn6,LenBranch.no,LenBranch.six,Bool.false_eq_true,ite_false] using fpc
        · intro hh
          rcases hh with hh|hh|hh
          all_goals contradiction

end E5R.Thermostat.PathDispatch
