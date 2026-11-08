import Projects.thermostat.HeadFoldMath
import Projects.thermostat.QuietRam
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeadFoldLiteral
open E5R E5R.Thermostat HttpRequestSpec

/-- Each site supplies actual decoder facts and PC arithmetic. The temporary
    and literal registers may alias, as they do in the emitted final Host byte. -/
structure Site (image : List Segment) (expected : BitVec 8) where
  loadPc : Word
  biasPc : Word
  testPc : Word
  shiftPc : Word
  foldPc : Word
  constPc : Word
  branchPc : Word
  nextPc : Word
  badPc : Word
  shiftLen : Word
  foldLen : Word
  constLen : Word
  offset : Word
  branchOffset : Word
  rd : Reg
  rt : Reg
  rc : Reg
  base : Reg
  rd_nonzero : rd.val≠0
  rt_nonzero : rt.val≠0
  rc_nonzero : rc.val≠0
  rd_ne_rt : rd≠rt
  rd_ne_rc : rd≠rc
  load_even : loadPc.getLsbD 0=false
  bias_even : biasPc.getLsbD 0=false
  test_even : testPc.getLsbD 0=false
  shift_even : shiftPc.getLsbD 0=false
  fold_even : foldPc.getLsbD 0=false
  const_even : constPc.getLsbD 0=false
  branch_even : branchPc.getLsbD 0=false
  bad_even : badPc.getLsbD 0=false
  load_code : fetchDecode image loadPc=some (.load .b false rd base offset,4#32)
  bias_code : fetchDecode image biasPc=some (.opimm .add rt rd 0xffffffbf#32,4#32)
  test_code : fetchDecode image testPc=some (.opimm .sltu rt rt 26#32,4#32)
  shift_code : fetchDecode image shiftPc=some (.opimm .sll rt rt 5#32,shiftLen)
  fold_code : fetchDecode image foldPc=some (.op .or rd rd rt,foldLen)
  const_code : fetchDecode image constPc=some (.opimm .add rc 0 (BitVec.ofNat 32 expected.toNat),constLen)
  branch_code : fetchDecode image branchPc=some (.branch .ne rd rc branchOffset,4#32)
  to_bias : loadPc+4#32=biasPc
  to_test : biasPc+4#32=testPc
  to_shift : testPc+4#32=shiftPc
  to_fold : shiftPc+shiftLen=foldPc
  to_const : foldPc+foldLen=constPc
  to_branch : constPc+constLen=branchPc
  to_next : branchPc+4#32=nextPc
  to_bad : branchPc+branchOffset=badPc

/-- Seven real instructions refine case-insensitive literal comparison.
    No semantic summary, environment value or desired result is assumed. -/
theorem compare (B : Board) (image : List Segment) (expected actual : BitVec 8) (site : Site image expected)
    (c : Core) (ram : Word → BitVec 8) (p : Word) (hp : c.pc=site.loadPc)
    (hbase : c.get site.base+site.offset=p) (hm : B.inRam p 1=true) (hbyte : ram p=actual) :
    ∃ d, Quiet.Steps B image 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if lower actual.toNat=expected.toNat then site.nextPc else site.badPc) ∧
      d.get site.rd=BitVec.ofNat 32 (lower actual.toNat) ∧ d.get site.rc=BitVec.ofNat 32 expected.toNat ∧
      (∀ r : Reg, r≠site.rd → r≠site.rt → r≠site.rc → d.get r=c.get r) ∧ d.sameCsr c := by
  let val : Word := BitVec.ofNat 32 actual.toNat
  let bias := alu .add val 0xffffffbf#32
  let flag := alu .sltu bias 26#32
  let shift := alu .sll flag 5#32
  let c1 := c.wr site.rd val site.biasPc
  let c2 := c1.wr site.rt bias site.testPc
  let c3 := c2.wr site.rt flag site.shiftPc
  let c4 := c3.wr site.rt shift site.foldPc
  let c5 := c4.wr site.rd (HeadFoldMath.word actual) site.constPc
  let c6 := c5.wr site.rc (BitVec.ofNat 32 expected.toNat) site.branchPc
  let d := c6.goto (if lower actual.toNat=expected.toNat then site.nextPc else site.badPc)
  have byte1 : c1.get site.rd=val := Core.wr_get_self _ _ _ _ site.rd_nonzero
  have bias2 : c2.get site.rt=bias := Core.wr_get_self _ _ _ _ site.rt_nonzero
  have flag3 : c3.get site.rt=flag := Core.wr_get_self _ _ _ _ site.rt_nonzero
  have shift4 : c4.get site.rt=shift := Core.wr_get_self _ _ _ _ site.rt_nonzero
  have byte2 : c2.get site.rd=val := (Core.wr_get_ne _ _ _ _ _ site.rd_ne_rt).trans byte1
  have byte3 : c3.get site.rd=val := (Core.wr_get_ne _ _ _ _ _ site.rd_ne_rt).trans byte2
  have byte4 : c4.get site.rd=val := (Core.wr_get_ne _ _ _ _ _ site.rd_ne_rt).trans byte3
  have fold5 : c5.get site.rd=HeadFoldMath.word actual := Core.wr_get_self _ _ _ _ site.rd_nonzero
  have fold6 : c6.get site.rd=HeadFoldMath.word actual := (Core.wr_get_ne _ _ _ _ _ site.rd_ne_rc).trans fold5
  have literal6 : c6.get site.rc=BitVec.ofNat 32 expected.toNat := Core.wr_get_self _ _ _ _ site.rc_nonzero
  have t0 : Quiet.Step B image ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];exact site.load_even) (by rw [hp];exact site.load_code) fun o => ?_
    change Observed.interp B image o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,hbase,Quiet.interp_load_ram (B := B) (img := image) (w := .b) o (by exact Nat.mod_one _) hm,Memory.load_byte]
    change Observed.interp B image o (.done (c.wr site.rd (BitVec.ofNat 32 (ram p).toNat) (c.pc+4#32))) ram 0 [] [] = _
    rw [hbyte,hp,site.to_bias];rfl
  have t1 : Quiet.Step B image ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of site.bias_even site.bias_code fun o => ?_
    change Observed.interp B image o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,byte1]
    change Observed.interp B image o (.done (c1.wr site.rt bias (site.biasPc+4#32))) ram 0 [] [] = _
    rw [site.to_test];rfl
  have t2 : Quiet.Step B image ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of site.test_even site.test_code fun o => ?_
    change Observed.interp B image o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,bias2]
    change Observed.interp B image o (.done (c2.wr site.rt flag (site.testPc+4#32))) ram 0 [] [] = _
    rw [site.to_shift];rfl
  have t3 : Quiet.Step B image ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of site.shift_even site.shift_code fun o => ?_
    change Observed.interp B image o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,flag3]
    change Observed.interp B image o (.done (c3.wr site.rt shift (site.shiftPc+site.shiftLen))) ram 0 [] [] = _
    rw [site.to_fold];rfl
  have t4 : Quiet.Step B image ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of site.fold_even site.fold_code fun o => ?_
    change Observed.interp B image o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    rw [exec_op,byte4,shift4]
    change Observed.interp B image o (.done (c4.wr site.rd (HeadFoldMath.word actual) (site.foldPc+site.foldLen))) ram 0 [] [] = _
    rw [site.to_const];rfl
  have t5 : Quiet.Step B image ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of site.const_even site.const_code fun o => ?_
    change Observed.interp B image o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B image o (.done (c5.wr site.rc ((0 : Word)+BitVec.ofNat 32 expected.toNat) (site.constPc+site.constLen))) ram 0 [] [] = _
    rw [show (0 : Word)=0#32 by decide +kernel,BitVec.zero_add,site.to_branch];rfl
  have t6 : Quiet.Step B image ⟨c6,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of site.branch_even site.branch_code fun o => ?_
    change Observed.interp B image o (exec c6 _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    rw [exec_branch,fold6,literal6,HeadFoldMath.comparison]
    by_cases same : lower actual.toNat=expected.toNat
    · simp only [d,same,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false]
      change Observed.interp B image o (.done (c6.goto (site.branchPc+4#32))) ram 0 [] [] = _
      rw [site.to_next];rfl
    · simp only [d,same,ne_eq,not_false_eq_true,decide_true,ite_true]
      change Observed.interp B image o (jump c6 (site.branchPc+site.branchOffset)) ram 0 [] [] = _
      rw [site.to_bad,jump_ok _ _ site.bad_even];rfl
  have csr1 : c1.sameCsr c := Core.sameCsr_wr _ _ _ _
  have csr2 : c2.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans csr1
  have csr3 : c3.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans csr2
  have csr4 : c4.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans csr3
  have csr5 : c5.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans csr4
  have csr6 : c6.sameCsr c := (Core.sameCsr_wr _ _ _ _).trans csr5
  refine ⟨d,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,
    fold6.trans (HeadFoldMath.lower_word actual),literal6,?_,(Core.sameCsr_goto c6 _).trans csr6⟩
  intro r hrd hrt hrc
  change c6.get r=c.get r
  exact (Core.wr_get_ne _ _ _ _ _ hrc).trans ((Core.wr_get_ne _ _ _ _ _ hrd).trans
    ((Core.wr_get_ne _ _ _ _ _ hrt).trans ((Core.wr_get_ne _ _ _ _ _ hrt).trans
    ((Core.wr_get_ne _ _ _ _ _ hrt).trans (Core.wr_get_ne _ _ _ _ _ hrd)))))
end E5R.Thermostat.HeadFoldLiteral
