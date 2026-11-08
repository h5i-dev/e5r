-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.NumericCall
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.DecimalQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.NumericCall
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8)) (report : Bool)
    (hs : Bytes.Span B ram p xs) (hp : c.pc = start report)
    (h8 : c.get 8 = p) (h9 : c.get 9 = BitVec.ofNat 32 xs.length) :
    ∃ d n, n ≤ 106 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = ret report ∧
      Decimal.Result d (DecimalSpec.parse xs) ∧ d.get 1 = ret report ∧
      (∀ r : Reg, r ≠ 1 → r.val < 10 ∨ 16 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 p (start report+2#32)
  let c2 := c1.wr 11 (BitVec.ofNat 32 xs.length) (start report+4#32)
  let c3 := c2.wr 1 (start report+4#32) (start report+8#32)
  let a := c3.wr 1 (ret report) 0x80001dae#32
  have har : (start report+8#32)+4#32 = ret report := by cases report <;> decide +kernel
  have htarg : ((start report+4#32)+offset report) &&& ~~~(1 : Word) = 0x80001dae#32 := by cases report <;> decide +kernel
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];cases report <;> decide) (by rw [hp];exact code0 report) fun o => ?_
    rw [exec_op,Core.get_zero,h8,hp]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by cases report <;> change ((start _+2#32).getLsbD 0 = false) <;> decide) (code1 report) fun o => ?_
    have hv : c1.get 9 = BitVec.ofNat 32 xs.length := by simp [c1,Core.wr_get_ne,h9]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add]
    have he : (start report+2#32)+2#32 = start report+4#32 := by cases report <;> decide +kernel
    change interp B img o (.done (c1.wr 11 (BitVec.ofNat 32 xs.length) ((start report+2#32)+2#32))) ram 0 [] = _
    rw [he];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by cases report <;> change ((start _+4#32).getLsbD 0 = false) <;> decide) (code2 report) fun o => ?_
    rw [exec_auipc,BitVec.add_zero]
    have he : (start report+4#32)+4#32 = start report+8#32 := by cases report <;> decide +kernel
    change interp B img o (.done (c2.wr 1 (start report+4#32) ((start report+4#32)+4#32))) ram 0 [] = _
    rw [he];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by cases report <;> change ((start _+8#32).getLsbD 0 = false) <;> decide) (code3 report) fun o => ?_
    have hv : c3.get 1 = start report+4#32 := by simp [c3,Core.wr_get]
    rw [exec_jalr,hv,htarg,jump_ok _ _ (by decide)]
    change interp B img o (.done ((c3.set 1 ((start report+8#32)+4#32)).goto 0x80001dae#32)) ram 0 [] = _
    rw [har];rfl
  have ha10 : a.get 10 = p := by simp [a,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  have ha11 : a.get 11 = BitVec.ofNat 32 xs.length := by simp [a,c3,c2,Core.wr_get_ne,Core.wr_get]
  obtain ⟨d,n,hn,ht,hpc,hresult,hframe,hcsr⟩ := E5R.Thermostat.Decimal.contract_quiet B a ram p xs hs rfl ha10 ha11
  have hara : a.get 1 = ret report := by simp [a,Core.wr_get]
  have hdra : d.get 1 = ret report := (hframe 1 (by decide)).trans hara
  have heven : ret report &&& ~~~(1 : Word) = ret report := by cases report <;> decide +kernel
  refine ⟨d,4+n,by omega,(Quiet.Steps.step s0 (.step s1 (.step s2 (.single s3)))).trans ht,?_,hresult,hdra,?_,hcsr⟩
  · rw [hpc,hara,heven]
  · intro r h1 hr
    rw [hframe r hr]
    have h10 : r ≠ 10 := by intro he;have hv := congrArg Fin.val he;change r.val = 10 at hv;omega
    have h11 : r ≠ 11 := by intro he;have hv := congrArg Fin.val he;change r.val = 11 at hv;omega
    simp [a,c3,c2,c1,Core.wr_get_ne,h1,h10,h11]

end E5R.Thermostat.NumericCall
