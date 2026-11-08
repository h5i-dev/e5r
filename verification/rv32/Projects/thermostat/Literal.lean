import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Literal
open E5R

/-- A checked load/constant/branch site. Decoder facts and PC arithmetic are
    explicit proof obligations; this carries no assumed semantic summary. -/
structure Site (img : List Segment) (expected : BitVec 8) where
  loadPc : Word
  constPc : Word
  branchPc : Word
  nextPc : Word
  badPc : Word
  constLen : Word
  offset : Word
  branchOffset : Word
  rd : Reg
  rc : Reg
  base : Reg
  rd_nonzero : rd.val ≠ 0
  rc_nonzero : rc.val ≠ 0
  distinct : rd ≠ rc
  load_aligned : loadPc.getLsbD 0 = false
  const_aligned : constPc.getLsbD 0 = false
  branch_aligned : branchPc.getLsbD 0 = false
  bad_aligned : badPc.getLsbD 0 = false
  load_code : fetchDecode img loadPc = some (.load .b false rd base offset,4#32)
  const_code : fetchDecode img constPc = some (.opimm .add rc 0 (BitVec.ofNat 32 expected.toNat),constLen)
  branch_code : fetchDecode img branchPc = some (.branch .ne rd rc branchOffset,4#32)
  to_const : loadPc+4#32 = constPc
  to_branch : constPc+constLen = branchPc
  to_next : branchPc+4#32 = nextPc
  to_bad : branchPc+branchOffset = badPc

theorem byte_injective (a b : BitVec 8) : BitVec.ofNat 32 a.toNat = BitVec.ofNat 32 b.toNat ↔ a = b := by
  constructor
  · intro h
    have hh := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat] at hh
    apply BitVec.eq_of_toNat_eq
    have ha := a.isLt;have hb := b.isLt;omega
  · intro h;rw [h]

/-- Both comparison outcomes are real deterministic instructions, including the
    rejection branch. Only the two declared destination registers change. -/
theorem compare (B : Board) (img : List Segment) (expected actual : BitVec 8) (site : Site img expected)
    (c : Core) (ram : Word → BitVec 8) (p : Word) (hp : c.pc = site.loadPc)
    (hbase : c.get site.base+site.offset = p) (hm : B.inRam p 1 = true) (hb : ram p = actual) :
    ∃ d, DetSteps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if actual = expected then site.nextPc else site.badPc) ∧
      d.get site.rd = BitVec.ofNat 32 actual.toNat ∧ d.get site.rc = BitVec.ofNat 32 expected.toNat ∧
      (∀ r : Reg, r ≠ site.rd → r ≠ site.rc → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr site.rd (BitVec.ofNat 32 actual.toNat) site.constPc
  let c2 := c1.wr site.rc (BitVec.ofNat 32 expected.toNat) site.branchPc
  let d := c2.goto (if actual = expected then site.nextPc else site.badPc)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];exact site.load_aligned) (by rw [hp];exact site.load_code) fun o => ?_
    rw [exec_load,hbase,interp_load_ram (B := B) (img := img) (w := .b) o (by change p.toNat%1 = 0;exact Nat.mod_one _) hm,Memory.load_byte]
    change interp B img o (.done (c.wr site.rd (BitVec.ofNat 32 (ram p).toNat) (c.pc+4#32))) ram 0 [] = _
    rw [hb,hp,site.to_const];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of site.const_aligned site.const_code fun o => ?_
    rw [exec_opimm,Core.get_zero]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add]
    change interp B img o (.done (c1.wr site.rc (BitVec.ofNat 32 expected.toNat) (site.constPc+site.constLen))) ram 0 [] = _
    rw [site.to_branch];rfl
  have hrd : c2.get site.rd = BitVec.ofNat 32 actual.toNat :=
    (Core.wr_get_ne _ _ _ _ _ site.distinct).trans (Core.wr_get_self _ _ _ _ site.rd_nonzero)
  have hrc : c2.get site.rc = BitVec.ofNat 32 expected.toNat := Core.wr_get_self _ _ _ _ site.rc_nonzero
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of site.branch_aligned site.branch_code fun o => ?_
    rw [exec_branch,hrd,hrc]
    have ht : taken .ne (BitVec.ofNat 32 actual.toNat) (BitVec.ofNat 32 expected.toNat) = decide (actual ≠ expected) := by
      change decide (BitVec.ofNat 32 actual.toNat ≠ BitVec.ofNat 32 expected.toNat) = _
      simp only [ne_eq,byte_injective]
    rw [ht]
    by_cases he : actual = expected
    · simp only [d,ite_eq_left he,he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false]
      change interp B img o (.done (c2.goto (site.branchPc+4#32))) ram 0 [] = _
      rw [site.to_next];rfl
    · simp only [d,ite_eq_right he,he,ne_eq,not_false_eq_true,decide_true,ite_true]
      change interp B img o (jump c2 (site.branchPc+site.branchOffset)) ram 0 [] = _
      rw [site.to_bad,jump_ok _ _ site.bad_aligned];rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,hrd,hrc,?_,by exact ((Core.sameCsr_goto c2 _).trans (Core.sameCsr_wr c1 site.rc _ _)).trans (Core.sameCsr_wr c site.rd _ _)⟩
  intro r hr hc
  exact (Core.wr_get_ne _ _ _ _ _ hc).trans (Core.wr_get_ne _ _ _ _ _ hr)
end E5R.Thermostat.Literal
