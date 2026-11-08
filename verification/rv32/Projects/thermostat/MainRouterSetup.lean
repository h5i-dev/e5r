import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRouterSetup
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32

def memory (ram : Word → BitVec 8)  :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3688#32) (2164258004#32) .w) (sp+3692#32) (832#32) .w) (sp+3696#32) (2164255704#32) .w) (sp+3700#32) (2164258944#32) .w) (sp+3704#32) (2164255676#32) .w) (sp+3708#32) (2164258004#32) .w) (sp+3712#32) (832#32) .w) (sp+3716#32) (2164255704#32) .w) (sp+3720#32) (2164258944#32) .w) (sp+3724#32) (2164255676#32) .w) (sp+3728#32) (2164258004#32) .w) (sp+3732#32) (832#32) .w) (sp+3736#32) (0#32) .b) (sp+3740#32) (2164255712#32) .w) (sp+3744#32) (2164258944#32) .w) (sp+3748#32) (2164255676#32) .w) (sp+3752#32) (2164258004#32) .w) (sp+3756#32) (832#32) .w) (sp+3780#32) (0#32) .b) (sp+3760#32) (2164255712#32) .w) (sp+3764#32) (2164258944#32) .w) (sp+3768#32) (2164255676#32) .w) (sp+3772#32) (2164258004#32) .w) (sp+3776#32) (832#32) .w) (sp+3784#32) (2164255720#32) .w) (sp+3788#32) (2164258944#32) .w) (sp+3792#32) (2164255676#32) .w) (sp+3796#32) (2164258004#32) .w) (sp+3800#32) (832#32) .w) (sp+3824#32) (0#32) .b) (sp+3804#32) (2164255720#32) .w) (sp+3808#32) (2164258944#32) .w) (sp+3812#32) (2164255676#32) .w) (sp+3816#32) (2164258004#32) .w) (sp+3820#32) (832#32) .w) (sp+3828#32) (2164255728#32) .w) (sp+3832#32) (2164258944#32) .w) (sp+3836#32) (2164255676#32) .w) (sp+3840#32) (2164258004#32) .w) (sp+3844#32) (832#32) .w) (sp+3868#32) (0#32) .b) (sp+3848#32) (2164255728#32) .w) (sp+3852#32) (2164258944#32) .w) (sp+3856#32) (2164255676#32) .w) (sp+3860#32) (2164258004#32) .w) (sp+3864#32) (832#32) .w) (sp+3872#32) (2164255736#32) .w) (sp+3876#32) (2164258944#32) .w) (sp+3880#32) (2164255676#32) .w) (sp+3884#32) (2164258004#32) .w) (sp+3888#32) (832#32) .w) (sp+3912#32) (0#32) .b) (sp+3892#32) (2164255736#32) .w) (sp+3896#32) (2164258944#32) .w) (sp+3900#32) (2164255676#32) .w) (sp+3904#32) (2164258004#32) .w) (sp+3908#32) (832#32) .w) (sp+3916#32) (2164255745#32) .w) (sp+3920#32) (2164258944#32) .w) (sp+3924#32) (2164255676#32) .w) (sp+3928#32) (2164258004#32) .w) (sp+3932#32) (832#32) .w) (sp+3936#32) (1#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32) (h12 : c.get 12=1024#32) (h22 : c.get 22=1#32)
    (stack : Memory.Block B 0x80ffeb90#32 5232)
    (tx : ramRead ram 0x80fff854#32 .w=0x80fff414#32)
    (router : ramRead ram 0x80fff844#32 .w=0x80ffebd8#32)
    (app : ramRead ram 0x80fff848#32 .w=0x80ffebbc#32)
    (hp : c.pc=0x8000129a#32) :
    ∃ d, Quiet.Steps B img 76 ⟨c,ram⟩ ⟨d,memory ram ⟩ ∧ d.pc=0x800013ba#32 ∧
      d.get 11=2164258004#32 ∧ d.get 13=2164255736#32 ∧ d.get 10=2164255676#32 ∧ d.get 12=832#32 ∧ d.get 14=2164258944#32 ∧ d.get 18=2#32 ∧ d.get 15=2164255745#32 ∧ (∀ r : Reg, r≠11 → r≠13 → r≠10 → r≠12 → r≠14 → r≠18 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (2164257812#32) 0x8000129c#32
  let c2 := c1.wr 13 (2164255704#32) 0x8000129e#32
  let c3 := c2.wr 10 (2164255676#32) 0x800012a0#32
  let c4 := c3.wr 11 (2164258004#32) 0x800012a4#32
  let c5 := c4.wr 12 (832#32) 0x800012a8#32
  let r1 := ramWrite ram (sp+3688#32) (2164258004#32) .w
  let c6 := c5.goto 0x800012ac#32
  let r2 := ramWrite r1 (sp+3692#32) (832#32) .w
  let c7 := c6.goto 0x800012b0#32
  let r3 := ramWrite r2 (sp+3696#32) (2164255704#32) .w
  let c8 := c7.goto 0x800012b4#32
  let c9 := c8.wr 14 (2164257679#32) 0x800012b8#32
  let c10 := c9.wr 14 (2164258944#32) 0x800012bc#32
  let r4 := ramWrite r3 (sp+3700#32) (2164258944#32) .w
  let c11 := c10.goto 0x800012c0#32
  let r5 := ramWrite r4 (sp+3704#32) (2164255676#32) .w
  let c12 := c11.goto 0x800012c4#32
  let r6 := ramWrite r5 (sp+3708#32) (2164258004#32) .w
  let c13 := c12.goto 0x800012c8#32
  let r7 := ramWrite r6 (sp+3712#32) (832#32) .w
  let c14 := c13.goto 0x800012cc#32
  let r8 := ramWrite r7 (sp+3716#32) (2164255704#32) .w
  let c15 := c14.goto 0x800012d0#32
  let r9 := ramWrite r8 (sp+3720#32) (2164258944#32) .w
  let c16 := c15.goto 0x800012d4#32
  let r10 := ramWrite r9 (sp+3724#32) (2164255676#32) .w
  let c17 := c16.goto 0x800012d8#32
  let r11 := ramWrite r10 (sp+3728#32) (2164258004#32) .w
  let c18 := c17.goto 0x800012dc#32
  let r12 := ramWrite r11 (sp+3732#32) (832#32) .w
  let c19 := c18.goto 0x800012e0#32
  let c20 := c19.wr 13 (2164255712#32) 0x800012e2#32
  let r13 := ramWrite r12 (sp+3736#32) (0#32) .b
  let c21 := c20.goto 0x800012e6#32
  let r14 := ramWrite r13 (sp+3740#32) (2164255712#32) .w
  let c22 := c21.goto 0x800012ea#32
  let r15 := ramWrite r14 (sp+3744#32) (2164258944#32) .w
  let c23 := c22.goto 0x800012ee#32
  let r16 := ramWrite r15 (sp+3748#32) (2164255676#32) .w
  let c24 := c23.goto 0x800012f2#32
  let r17 := ramWrite r16 (sp+3752#32) (2164258004#32) .w
  let c25 := c24.goto 0x800012f6#32
  let r18 := ramWrite r17 (sp+3756#32) (832#32) .w
  let c26 := c25.goto 0x800012fa#32
  let r19 := ramWrite r18 (sp+3780#32) (0#32) .b
  let c27 := c26.goto 0x800012fe#32
  let c28 := c27.wr 18 (2#32) 0x80001300#32
  let r20 := ramWrite r19 (sp+3760#32) (2164255712#32) .w
  let c29 := c28.goto 0x80001304#32
  let r21 := ramWrite r20 (sp+3764#32) (2164258944#32) .w
  let c30 := c29.goto 0x80001308#32
  let r22 := ramWrite r21 (sp+3768#32) (2164255676#32) .w
  let c31 := c30.goto 0x8000130c#32
  let r23 := ramWrite r22 (sp+3772#32) (2164258004#32) .w
  let c32 := c31.goto 0x80001310#32
  let c33 := c32.wr 13 (2164255720#32) 0x80001312#32
  let r24 := ramWrite r23 (sp+3776#32) (832#32) .w
  let c34 := c33.goto 0x80001316#32
  let r25 := ramWrite r24 (sp+3784#32) (2164255720#32) .w
  let c35 := c34.goto 0x8000131a#32
  let r26 := ramWrite r25 (sp+3788#32) (2164258944#32) .w
  let c36 := c35.goto 0x8000131e#32
  let r27 := ramWrite r26 (sp+3792#32) (2164255676#32) .w
  let c37 := c36.goto 0x80001322#32
  let r28 := ramWrite r27 (sp+3796#32) (2164258004#32) .w
  let c38 := c37.goto 0x80001326#32
  let r29 := ramWrite r28 (sp+3800#32) (832#32) .w
  let c39 := c38.goto 0x8000132a#32
  let r30 := ramWrite r29 (sp+3824#32) (0#32) .b
  let c40 := c39.goto 0x8000132e#32
  let r31 := ramWrite r30 (sp+3804#32) (2164255720#32) .w
  let c41 := c40.goto 0x80001332#32
  let r32 := ramWrite r31 (sp+3808#32) (2164258944#32) .w
  let c42 := c41.goto 0x80001336#32
  let r33 := ramWrite r32 (sp+3812#32) (2164255676#32) .w
  let c43 := c42.goto 0x8000133a#32
  let r34 := ramWrite r33 (sp+3816#32) (2164258004#32) .w
  let c44 := c43.goto 0x8000133e#32
  let c45 := c44.wr 13 (2164255728#32) 0x80001340#32
  let r35 := ramWrite r34 (sp+3820#32) (832#32) .w
  let c46 := c45.goto 0x80001344#32
  let r36 := ramWrite r35 (sp+3828#32) (2164255728#32) .w
  let c47 := c46.goto 0x80001348#32
  let r37 := ramWrite r36 (sp+3832#32) (2164258944#32) .w
  let c48 := c47.goto 0x8000134c#32
  let r38 := ramWrite r37 (sp+3836#32) (2164255676#32) .w
  let c49 := c48.goto 0x80001350#32
  let r39 := ramWrite r38 (sp+3840#32) (2164258004#32) .w
  let c50 := c49.goto 0x80001354#32
  let r40 := ramWrite r39 (sp+3844#32) (832#32) .w
  let c51 := c50.goto 0x80001358#32
  let r41 := ramWrite r40 (sp+3868#32) (0#32) .b
  let c52 := c51.goto 0x8000135c#32
  let r42 := ramWrite r41 (sp+3848#32) (2164255728#32) .w
  let c53 := c52.goto 0x80001360#32
  let r43 := ramWrite r42 (sp+3852#32) (2164258944#32) .w
  let c54 := c53.goto 0x80001364#32
  let r44 := ramWrite r43 (sp+3856#32) (2164255676#32) .w
  let c55 := c54.goto 0x80001368#32
  let r45 := ramWrite r44 (sp+3860#32) (2164258004#32) .w
  let c56 := c55.goto 0x8000136c#32
  let c57 := c56.wr 13 (2164255736#32) 0x8000136e#32
  let r46 := ramWrite r45 (sp+3864#32) (832#32) .w
  let c58 := c57.goto 0x80001372#32
  let r47 := ramWrite r46 (sp+3872#32) (2164255736#32) .w
  let c59 := c58.goto 0x80001376#32
  let r48 := ramWrite r47 (sp+3876#32) (2164258944#32) .w
  let c60 := c59.goto 0x8000137a#32
  let r49 := ramWrite r48 (sp+3880#32) (2164255676#32) .w
  let c61 := c60.goto 0x8000137e#32
  let r50 := ramWrite r49 (sp+3884#32) (2164258004#32) .w
  let c62 := c61.goto 0x80001382#32
  let r51 := ramWrite r50 (sp+3888#32) (832#32) .w
  let c63 := c62.goto 0x80001386#32
  let r52 := ramWrite r51 (sp+3912#32) (0#32) .b
  let c64 := c63.goto 0x8000138a#32
  let r53 := ramWrite r52 (sp+3892#32) (2164255736#32) .w
  let c65 := c64.goto 0x8000138e#32
  let r54 := ramWrite r53 (sp+3896#32) (2164258944#32) .w
  let c66 := c65.goto 0x80001392#32
  let r55 := ramWrite r54 (sp+3900#32) (2164255676#32) .w
  let c67 := c66.goto 0x80001396#32
  let r56 := ramWrite r55 (sp+3904#32) (2164258004#32) .w
  let c68 := c67.goto 0x8000139a#32
  let c69 := c68.wr 15 (2164255745#32) 0x8000139e#32
  let r57 := ramWrite r56 (sp+3908#32) (832#32) .w
  let c70 := c69.goto 0x800013a2#32
  let r58 := ramWrite r57 (sp+3916#32) (2164255745#32) .w
  let c71 := c70.goto 0x800013a6#32
  let r59 := ramWrite r58 (sp+3920#32) (2164258944#32) .w
  let c72 := c71.goto 0x800013aa#32
  let r60 := ramWrite r59 (sp+3924#32) (2164255676#32) .w
  let c73 := c72.goto 0x800013ae#32
  let r61 := ramWrite r60 (sp+3928#32) (2164258004#32) .w
  let c74 := c73.goto 0x800013b2#32
  let r62 := ramWrite r61 (sp+3932#32) (832#32) .w
  let c75 := c74.goto 0x800013b6#32
  let r63 := ramWrite r62 (sp+3936#32) (1#32) .b
  let c76 := c75.goto 0x800013ba#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147488410) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=2164258836#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_load,v8,show 2164258836#32+64#32=sp+3268#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 817 (by decide +kernel)) (Memory.block_access stack (off := 3268) (by decide) (by decide))]
    change Observed.interp B img o (.done (c.wr 11 (extend .w true (ramRead ram 2164258900#32 .w)) (c.pc+2#32))) ram 0 [] []=_
    rw [tx];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000129c#32).getLsbD 0=false;decide) rt2147488412 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=2164258836#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_load,v8,show 2164258836#32+48#32=sp+3252#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 813 (by decide +kernel)) (Memory.block_access stack (off := 3252) (by decide) (by decide))]
    change Observed.interp B img o (.done (c1.wr 13 (extend .w true (ramRead ram 2164258884#32 .w)) (c1.pc+2#32))) ram 0 [] []=_
    rw [router];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000129e#32).getLsbD 0=false;decide) rt2147488414 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=2164258836#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_load,v8,show 2164258836#32+52#32=sp+3256#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 814 (by decide +kernel)) (Memory.block_access stack (off := 3256) (by decide) (by decide))]
    change Observed.interp B img o (.done (c2.wr 10 (extend .w true (ramRead ram 2164258888#32 .w)) (c2.pc+2#32))) ram 0 [] []=_
    rw [app];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800012a0#32).getLsbD 0=false;decide) rt2147488416 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v11 : c3.get 11=2164257812#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_opimm,v11]
    change Observed.interp B img o (.done (c3.wr 11 (alu .add 2164257812#32 192#32) (c3.pc+4#32))) ram 0 [] []=_
    rw [show alu .add 2164257812#32 192#32=2164258004#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800012a4#32).getLsbD 0=false;decide) rt2147488420 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v12 : c4.get 12=1024#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_opimm,v12]
    change Observed.interp B img o (.done (c4.wr 12 (alu .add 1024#32 4294967104#32) (c4.pc+4#32))) ram 0 [] []=_
    rw [show alu .add 1024#32 4294967104#32=832#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,r1⟩ := by
    refine Quiet.step_of (by change (0x800012a8#32).getLsbD 0=false;decide) rt2147488424 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 r1 [],[]⟩
    have v8 : c5.get 8=2164258836#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v11 : c5.get 11=2164258004#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v11,show 2164258836#32+484#32=sp+3688#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 922 (by decide +kernel)) (Memory.block_access stack (off := 3688) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r1⟩ ⟨c7,r2⟩ := by
    refine Quiet.step_of (by change (0x800012ac#32).getLsbD 0=false;decide) rt2147488428 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r1 0 [] [] = ⟨.ok c7 r2 [],[]⟩
    have v8 : c6.get 8=2164258836#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v12 : c6.get 12=832#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v12,show 2164258836#32+488#32=sp+3692#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 923 (by decide +kernel)) (Memory.block_access stack (off := 3692) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r2⟩ ⟨c8,r3⟩ := by
    refine Quiet.step_of (by change (0x800012b0#32).getLsbD 0=false;decide) rt2147488432 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r2 0 [] [] = ⟨.ok c8 r3 [],[]⟩
    have v8 : c7.get 8=2164258836#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v13 : c7.get 13=2164255704#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v13,show 2164258836#32+492#32=sp+3696#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 924 (by decide +kernel)) (Memory.block_access stack (off := 3696) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r3⟩ ⟨c9,r3⟩ := by
    refine Quiet.step_of (by change (0x800012b4#32).getLsbD 0=false;decide) rt2147488436 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r3 0 [] [] = ⟨.ok c9 r3 [],[]⟩
    have v2 : c8.get 2=2164255632#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_opimm,v2]
    change Observed.interp B img o (.done (c8.wr 14 (alu .add 2164255632#32 2047#32) (c8.pc+4#32))) r3 0 [] []=_
    rw [show alu .add 2164255632#32 2047#32=2164257679#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r3⟩ ⟨c10,r3⟩ := by
    refine Quiet.step_of (by change (0x800012b8#32).getLsbD 0=false;decide) rt2147488440 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r3 0 [] [] = ⟨.ok c10 r3 [],[]⟩
    have v14 : c9.get 14=2164257679#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c9.wr 14 (alu .add 2164257679#32 1265#32) (c9.pc+4#32))) r3 0 [] []=_
    rw [show alu .add 2164257679#32 1265#32=2164258944#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r3⟩ ⟨c11,r4⟩ := by
    refine Quiet.step_of (by change (0x800012bc#32).getLsbD 0=false;decide) rt2147488444 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r3 0 [] [] = ⟨.ok c11 r4 [],[]⟩
    have v8 : c10.get 8=2164258836#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v14 : c10.get 14=2164258944#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v14,show 2164258836#32+496#32=sp+3700#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 925 (by decide +kernel)) (Memory.block_access stack (off := 3700) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r4⟩ ⟨c12,r5⟩ := by
    refine Quiet.step_of (by change (0x800012c0#32).getLsbD 0=false;decide) rt2147488448 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r4 0 [] [] = ⟨.ok c12 r5 [],[]⟩
    have v8 : c11.get 8=2164258836#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v10 : c11.get 10=2164255676#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v10,show 2164258836#32+500#32=sp+3704#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 926 (by decide +kernel)) (Memory.block_access stack (off := 3704) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r5⟩ ⟨c13,r6⟩ := by
    refine Quiet.step_of (by change (0x800012c4#32).getLsbD 0=false;decide) rt2147488452 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r5 0 [] [] = ⟨.ok c13 r6 [],[]⟩
    have v8 : c12.get 8=2164258836#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v11 : c12.get 11=2164258004#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v11,show 2164258836#32+504#32=sp+3708#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 927 (by decide +kernel)) (Memory.block_access stack (off := 3708) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r6⟩ ⟨c14,r7⟩ := by
    refine Quiet.step_of (by change (0x800012c8#32).getLsbD 0=false;decide) rt2147488456 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r6 0 [] [] = ⟨.ok c14 r7 [],[]⟩
    have v8 : c13.get 8=2164258836#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v12 : c13.get 12=832#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v12,show 2164258836#32+508#32=sp+3712#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 928 (by decide +kernel)) (Memory.block_access stack (off := 3712) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r7⟩ ⟨c15,r8⟩ := by
    refine Quiet.step_of (by change (0x800012cc#32).getLsbD 0=false;decide) rt2147488460 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r7 0 [] [] = ⟨.ok c15 r8 [],[]⟩
    have v8 : c14.get 8=2164258836#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v13 : c14.get 13=2164255704#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v13,show 2164258836#32+512#32=sp+3716#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 929 (by decide +kernel)) (Memory.block_access stack (off := 3716) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r8⟩ ⟨c16,r9⟩ := by
    refine Quiet.step_of (by change (0x800012d0#32).getLsbD 0=false;decide) rt2147488464 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r8 0 [] [] = ⟨.ok c16 r9 [],[]⟩
    have v8 : c15.get 8=2164258836#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v14 : c15.get 14=2164258944#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v14,show 2164258836#32+516#32=sp+3720#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 930 (by decide +kernel)) (Memory.block_access stack (off := 3720) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r9⟩ ⟨c17,r10⟩ := by
    refine Quiet.step_of (by change (0x800012d4#32).getLsbD 0=false;decide) rt2147488468 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r9 0 [] [] = ⟨.ok c17 r10 [],[]⟩
    have v8 : c16.get 8=2164258836#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v10 : c16.get 10=2164255676#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v10,show 2164258836#32+520#32=sp+3724#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 931 (by decide +kernel)) (Memory.block_access stack (off := 3724) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r10⟩ ⟨c18,r11⟩ := by
    refine Quiet.step_of (by change (0x800012d8#32).getLsbD 0=false;decide) rt2147488472 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r10 0 [] [] = ⟨.ok c18 r11 [],[]⟩
    have v8 : c17.get 8=2164258836#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v11 : c17.get 11=2164258004#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v11,show 2164258836#32+524#32=sp+3728#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 932 (by decide +kernel)) (Memory.block_access stack (off := 3728) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r11⟩ ⟨c19,r12⟩ := by
    refine Quiet.step_of (by change (0x800012dc#32).getLsbD 0=false;decide) rt2147488476 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r11 0 [] [] = ⟨.ok c19 r12 [],[]⟩
    have v8 : c18.get 8=2164258836#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v12 : c18.get 12=832#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v12,show 2164258836#32+528#32=sp+3732#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 933 (by decide +kernel)) (Memory.block_access stack (off := 3732) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,r12⟩ ⟨c20,r12⟩ := by
    refine Quiet.step_of (by change (0x800012e0#32).getLsbD 0=false;decide) rt2147488480 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r12 0 [] [] = ⟨.ok c20 r12 [],[]⟩
    have v13 : c19.get 13=2164255704#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_opimm,v13]
    change Observed.interp B img o (.done (c19.wr 13 (alu .add 2164255704#32 8#32) (c19.pc+2#32))) r12 0 [] []=_
    rw [show alu .add 2164255704#32 8#32=2164255712#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,r12⟩ ⟨c21,r13⟩ := by
    refine Quiet.step_of (by change (0x800012e2#32).getLsbD 0=false;decide) rt2147488482 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r12 0 [] [] = ⟨.ok c21 r13 [],[]⟩
    have v8 : c20.get 8=2164258836#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v0 : c20.get 0=0#32 := Core.get_zero _
    rw [exec_store,v8,v0,show 2164258836#32+532#32=sp+3736#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3736) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r13⟩ ⟨c22,r14⟩ := by
    refine Quiet.step_of (by change (0x800012e6#32).getLsbD 0=false;decide) rt2147488486 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r13 0 [] [] = ⟨.ok c22 r14 [],[]⟩
    have v8 : c21.get 8=2164258836#32 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v13 : c21.get 13=2164255712#32 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v13,show 2164258836#32+536#32=sp+3740#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 935 (by decide +kernel)) (Memory.block_access stack (off := 3740) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r14⟩ ⟨c23,r15⟩ := by
    refine Quiet.step_of (by change (0x800012ea#32).getLsbD 0=false;decide) rt2147488490 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r14 0 [] [] = ⟨.ok c23 r15 [],[]⟩
    have v8 : c22.get 8=2164258836#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v14 : c22.get 14=2164258944#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v14,show 2164258836#32+540#32=sp+3744#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 936 (by decide +kernel)) (Memory.block_access stack (off := 3744) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t23 : Quiet.Step B img ⟨c23,r15⟩ ⟨c24,r16⟩ := by
    refine Quiet.step_of (by change (0x800012ee#32).getLsbD 0=false;decide) rt2147488494 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r15 0 [] [] = ⟨.ok c24 r16 [],[]⟩
    have v8 : c23.get 8=2164258836#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v10 : c23.get 10=2164255676#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v10,show 2164258836#32+544#32=sp+3748#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 937 (by decide +kernel)) (Memory.block_access stack (off := 3748) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t24 : Quiet.Step B img ⟨c24,r16⟩ ⟨c25,r17⟩ := by
    refine Quiet.step_of (by change (0x800012f2#32).getLsbD 0=false;decide) rt2147488498 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r16 0 [] [] = ⟨.ok c25 r17 [],[]⟩
    have v8 : c24.get 8=2164258836#32 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v11 : c24.get 11=2164258004#32 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v11,show 2164258836#32+548#32=sp+3752#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 938 (by decide +kernel)) (Memory.block_access stack (off := 3752) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t25 : Quiet.Step B img ⟨c25,r17⟩ ⟨c26,r18⟩ := by
    refine Quiet.step_of (by change (0x800012f6#32).getLsbD 0=false;decide) rt2147488502 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r17 0 [] [] = ⟨.ok c26 r18 [],[]⟩
    have v8 : c25.get 8=2164258836#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v12 : c25.get 12=832#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v12,show 2164258836#32+552#32=sp+3756#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 939 (by decide +kernel)) (Memory.block_access stack (off := 3756) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t26 : Quiet.Step B img ⟨c26,r18⟩ ⟨c27,r19⟩ := by
    refine Quiet.step_of (by change (0x800012fa#32).getLsbD 0=false;decide) rt2147488506 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) r18 0 [] [] = ⟨.ok c27 r19 [],[]⟩
    have v8 : c26.get 8=2164258836#32 := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v0 : c26.get 0=0#32 := Core.get_zero _
    rw [exec_store,v8,v0,show 2164258836#32+576#32=sp+3780#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3780) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t27 : Quiet.Step B img ⟨c27,r19⟩ ⟨c28,r19⟩ := by
    refine Quiet.step_of (by change (0x800012fe#32).getLsbD 0=false;decide) rt2147488510 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) r19 0 [] [] = ⟨.ok c28 r19 [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c27.wr 18 (alu .add 0#32 2#32) (c27.pc+2#32))) r19 0 [] []=_
    rw [show alu .add 0#32 2#32=2#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t28 : Quiet.Step B img ⟨c28,r19⟩ ⟨c29,r20⟩ := by
    refine Quiet.step_of (by change (0x80001300#32).getLsbD 0=false;decide) rt2147488512 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) r19 0 [] [] = ⟨.ok c29 r20 [],[]⟩
    have v8 : c28.get 8=2164258836#32 := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v13 : c28.get 13=2164255712#32 := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v13,show 2164258836#32+556#32=sp+3760#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 940 (by decide +kernel)) (Memory.block_access stack (off := 3760) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,r20⟩ ⟨c30,r21⟩ := by
    refine Quiet.step_of (by change (0x80001304#32).getLsbD 0=false;decide) rt2147488516 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) r20 0 [] [] = ⟨.ok c30 r21 [],[]⟩
    have v8 : c29.get 8=2164258836#32 := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v14 : c29.get 14=2164258944#32 := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v14,show 2164258836#32+560#32=sp+3764#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 941 (by decide +kernel)) (Memory.block_access stack (off := 3764) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t30 : Quiet.Step B img ⟨c30,r21⟩ ⟨c31,r22⟩ := by
    refine Quiet.step_of (by change (0x80001308#32).getLsbD 0=false;decide) rt2147488520 fun o => ?_
    change Observed.interp B img o (exec c30 _ _) r21 0 [] [] = ⟨.ok c31 r22 [],[]⟩
    have v8 : c30.get 8=2164258836#32 := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v10 : c30.get 10=2164255676#32 := by simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v10,show 2164258836#32+564#32=sp+3768#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 942 (by decide +kernel)) (Memory.block_access stack (off := 3768) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t31 : Quiet.Step B img ⟨c31,r22⟩ ⟨c32,r23⟩ := by
    refine Quiet.step_of (by change (0x8000130c#32).getLsbD 0=false;decide) rt2147488524 fun o => ?_
    change Observed.interp B img o (exec c31 _ _) r22 0 [] [] = ⟨.ok c32 r23 [],[]⟩
    have v8 : c31.get 8=2164258836#32 := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v11 : c31.get 11=2164258004#32 := by simp [c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v11,show 2164258836#32+568#32=sp+3772#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 943 (by decide +kernel)) (Memory.block_access stack (off := 3772) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t32 : Quiet.Step B img ⟨c32,r23⟩ ⟨c33,r23⟩ := by
    refine Quiet.step_of (by change (0x80001310#32).getLsbD 0=false;decide) rt2147488528 fun o => ?_
    change Observed.interp B img o (exec c32 _ _) r23 0 [] [] = ⟨.ok c33 r23 [],[]⟩
    have v13 : c32.get 13=2164255712#32 := by simp [c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_opimm,v13]
    change Observed.interp B img o (.done (c32.wr 13 (alu .add 2164255712#32 8#32) (c32.pc+2#32))) r23 0 [] []=_
    rw [show alu .add 2164255712#32 8#32=2164255720#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t33 : Quiet.Step B img ⟨c33,r23⟩ ⟨c34,r24⟩ := by
    refine Quiet.step_of (by change (0x80001312#32).getLsbD 0=false;decide) rt2147488530 fun o => ?_
    change Observed.interp B img o (exec c33 _ _) r23 0 [] [] = ⟨.ok c34 r24 [],[]⟩
    have v8 : c33.get 8=2164258836#32 := by simp [c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v12 : c33.get 12=832#32 := by simp [c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v12,show 2164258836#32+572#32=sp+3776#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 944 (by decide +kernel)) (Memory.block_access stack (off := 3776) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t34 : Quiet.Step B img ⟨c34,r24⟩ ⟨c35,r25⟩ := by
    refine Quiet.step_of (by change (0x80001316#32).getLsbD 0=false;decide) rt2147488534 fun o => ?_
    change Observed.interp B img o (exec c34 _ _) r24 0 [] [] = ⟨.ok c35 r25 [],[]⟩
    have v8 : c34.get 8=2164258836#32 := by simp [c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v13 : c34.get 13=2164255720#32 := by simp [c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v13,show 2164258836#32+580#32=sp+3784#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 946 (by decide +kernel)) (Memory.block_access stack (off := 3784) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t35 : Quiet.Step B img ⟨c35,r25⟩ ⟨c36,r26⟩ := by
    refine Quiet.step_of (by change (0x8000131a#32).getLsbD 0=false;decide) rt2147488538 fun o => ?_
    change Observed.interp B img o (exec c35 _ _) r25 0 [] [] = ⟨.ok c36 r26 [],[]⟩
    have v8 : c35.get 8=2164258836#32 := by simp [c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v14 : c35.get 14=2164258944#32 := by simp [c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v14,show 2164258836#32+584#32=sp+3788#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 947 (by decide +kernel)) (Memory.block_access stack (off := 3788) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t36 : Quiet.Step B img ⟨c36,r26⟩ ⟨c37,r27⟩ := by
    refine Quiet.step_of (by change (0x8000131e#32).getLsbD 0=false;decide) rt2147488542 fun o => ?_
    change Observed.interp B img o (exec c36 _ _) r26 0 [] [] = ⟨.ok c37 r27 [],[]⟩
    have v8 : c36.get 8=2164258836#32 := by simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v10 : c36.get 10=2164255676#32 := by simp [c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v10,show 2164258836#32+588#32=sp+3792#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 948 (by decide +kernel)) (Memory.block_access stack (off := 3792) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t37 : Quiet.Step B img ⟨c37,r27⟩ ⟨c38,r28⟩ := by
    refine Quiet.step_of (by change (0x80001322#32).getLsbD 0=false;decide) rt2147488546 fun o => ?_
    change Observed.interp B img o (exec c37 _ _) r27 0 [] [] = ⟨.ok c38 r28 [],[]⟩
    have v8 : c37.get 8=2164258836#32 := by simp [c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v11 : c37.get 11=2164258004#32 := by simp [c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v11,show 2164258836#32+592#32=sp+3796#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 949 (by decide +kernel)) (Memory.block_access stack (off := 3796) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t38 : Quiet.Step B img ⟨c38,r28⟩ ⟨c39,r29⟩ := by
    refine Quiet.step_of (by change (0x80001326#32).getLsbD 0=false;decide) rt2147488550 fun o => ?_
    change Observed.interp B img o (exec c38 _ _) r28 0 [] [] = ⟨.ok c39 r29 [],[]⟩
    have v8 : c38.get 8=2164258836#32 := by simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v12 : c38.get 12=832#32 := by simp [c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v12,show 2164258836#32+596#32=sp+3800#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 950 (by decide +kernel)) (Memory.block_access stack (off := 3800) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t39 : Quiet.Step B img ⟨c39,r29⟩ ⟨c40,r30⟩ := by
    refine Quiet.step_of (by change (0x8000132a#32).getLsbD 0=false;decide) rt2147488554 fun o => ?_
    change Observed.interp B img o (exec c39 _ _) r29 0 [] [] = ⟨.ok c40 r30 [],[]⟩
    have v8 : c39.get 8=2164258836#32 := by simp [c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v0 : c39.get 0=0#32 := Core.get_zero _
    rw [exec_store,v8,v0,show 2164258836#32+620#32=sp+3824#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3824) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t40 : Quiet.Step B img ⟨c40,r30⟩ ⟨c41,r31⟩ := by
    refine Quiet.step_of (by change (0x8000132e#32).getLsbD 0=false;decide) rt2147488558 fun o => ?_
    change Observed.interp B img o (exec c40 _ _) r30 0 [] [] = ⟨.ok c41 r31 [],[]⟩
    have v8 : c40.get 8=2164258836#32 := by simp [c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v13 : c40.get 13=2164255720#32 := by simp [c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v13,show 2164258836#32+600#32=sp+3804#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 951 (by decide +kernel)) (Memory.block_access stack (off := 3804) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t41 : Quiet.Step B img ⟨c41,r31⟩ ⟨c42,r32⟩ := by
    refine Quiet.step_of (by change (0x80001332#32).getLsbD 0=false;decide) rt2147488562 fun o => ?_
    change Observed.interp B img o (exec c41 _ _) r31 0 [] [] = ⟨.ok c42 r32 [],[]⟩
    have v8 : c41.get 8=2164258836#32 := by simp [c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v14 : c41.get 14=2164258944#32 := by simp [c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v14,show 2164258836#32+604#32=sp+3808#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 952 (by decide +kernel)) (Memory.block_access stack (off := 3808) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t42 : Quiet.Step B img ⟨c42,r32⟩ ⟨c43,r33⟩ := by
    refine Quiet.step_of (by change (0x80001336#32).getLsbD 0=false;decide) rt2147488566 fun o => ?_
    change Observed.interp B img o (exec c42 _ _) r32 0 [] [] = ⟨.ok c43 r33 [],[]⟩
    have v8 : c42.get 8=2164258836#32 := by simp [c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v10 : c42.get 10=2164255676#32 := by simp [c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v10,show 2164258836#32+608#32=sp+3812#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 953 (by decide +kernel)) (Memory.block_access stack (off := 3812) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t43 : Quiet.Step B img ⟨c43,r33⟩ ⟨c44,r34⟩ := by
    refine Quiet.step_of (by change (0x8000133a#32).getLsbD 0=false;decide) rt2147488570 fun o => ?_
    change Observed.interp B img o (exec c43 _ _) r33 0 [] [] = ⟨.ok c44 r34 [],[]⟩
    have v8 : c43.get 8=2164258836#32 := by simp [c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v11 : c43.get 11=2164258004#32 := by simp [c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v11,show 2164258836#32+612#32=sp+3816#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 954 (by decide +kernel)) (Memory.block_access stack (off := 3816) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t44 : Quiet.Step B img ⟨c44,r34⟩ ⟨c45,r34⟩ := by
    refine Quiet.step_of (by change (0x8000133e#32).getLsbD 0=false;decide) rt2147488574 fun o => ?_
    change Observed.interp B img o (exec c44 _ _) r34 0 [] [] = ⟨.ok c45 r34 [],[]⟩
    have v13 : c44.get 13=2164255720#32 := by simp [c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_opimm,v13]
    change Observed.interp B img o (.done (c44.wr 13 (alu .add 2164255720#32 8#32) (c44.pc+2#32))) r34 0 [] []=_
    rw [show alu .add 2164255720#32 8#32=2164255728#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t45 : Quiet.Step B img ⟨c45,r34⟩ ⟨c46,r35⟩ := by
    refine Quiet.step_of (by change (0x80001340#32).getLsbD 0=false;decide) rt2147488576 fun o => ?_
    change Observed.interp B img o (exec c45 _ _) r34 0 [] [] = ⟨.ok c46 r35 [],[]⟩
    have v8 : c45.get 8=2164258836#32 := by simp [c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v12 : c45.get 12=832#32 := by simp [c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v12,show 2164258836#32+616#32=sp+3820#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 955 (by decide +kernel)) (Memory.block_access stack (off := 3820) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t46 : Quiet.Step B img ⟨c46,r35⟩ ⟨c47,r36⟩ := by
    refine Quiet.step_of (by change (0x80001344#32).getLsbD 0=false;decide) rt2147488580 fun o => ?_
    change Observed.interp B img o (exec c46 _ _) r35 0 [] [] = ⟨.ok c47 r36 [],[]⟩
    have v8 : c46.get 8=2164258836#32 := by simp [c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v13 : c46.get 13=2164255728#32 := by simp [c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v13,show 2164258836#32+624#32=sp+3828#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 957 (by decide +kernel)) (Memory.block_access stack (off := 3828) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t47 : Quiet.Step B img ⟨c47,r36⟩ ⟨c48,r37⟩ := by
    refine Quiet.step_of (by change (0x80001348#32).getLsbD 0=false;decide) rt2147488584 fun o => ?_
    change Observed.interp B img o (exec c47 _ _) r36 0 [] [] = ⟨.ok c48 r37 [],[]⟩
    have v8 : c47.get 8=2164258836#32 := by simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v14 : c47.get 14=2164258944#32 := by simp [c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v14,show 2164258836#32+628#32=sp+3832#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 958 (by decide +kernel)) (Memory.block_access stack (off := 3832) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t48 : Quiet.Step B img ⟨c48,r37⟩ ⟨c49,r38⟩ := by
    refine Quiet.step_of (by change (0x8000134c#32).getLsbD 0=false;decide) rt2147488588 fun o => ?_
    change Observed.interp B img o (exec c48 _ _) r37 0 [] [] = ⟨.ok c49 r38 [],[]⟩
    have v8 : c48.get 8=2164258836#32 := by simp [c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v10 : c48.get 10=2164255676#32 := by simp [c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v10,show 2164258836#32+632#32=sp+3836#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 959 (by decide +kernel)) (Memory.block_access stack (off := 3836) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t49 : Quiet.Step B img ⟨c49,r38⟩ ⟨c50,r39⟩ := by
    refine Quiet.step_of (by change (0x80001350#32).getLsbD 0=false;decide) rt2147488592 fun o => ?_
    change Observed.interp B img o (exec c49 _ _) r38 0 [] [] = ⟨.ok c50 r39 [],[]⟩
    have v8 : c49.get 8=2164258836#32 := by simp [c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v11 : c49.get 11=2164258004#32 := by simp [c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v11,show 2164258836#32+636#32=sp+3840#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 960 (by decide +kernel)) (Memory.block_access stack (off := 3840) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t50 : Quiet.Step B img ⟨c50,r39⟩ ⟨c51,r40⟩ := by
    refine Quiet.step_of (by change (0x80001354#32).getLsbD 0=false;decide) rt2147488596 fun o => ?_
    change Observed.interp B img o (exec c50 _ _) r39 0 [] [] = ⟨.ok c51 r40 [],[]⟩
    have v8 : c50.get 8=2164258836#32 := by simp [c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v12 : c50.get 12=832#32 := by simp [c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v12,show 2164258836#32+640#32=sp+3844#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 961 (by decide +kernel)) (Memory.block_access stack (off := 3844) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t51 : Quiet.Step B img ⟨c51,r40⟩ ⟨c52,r41⟩ := by
    refine Quiet.step_of (by change (0x80001358#32).getLsbD 0=false;decide) rt2147488600 fun o => ?_
    change Observed.interp B img o (exec c51 _ _) r40 0 [] [] = ⟨.ok c52 r41 [],[]⟩
    have v8 : c51.get 8=2164258836#32 := by simp [c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v0 : c51.get 0=0#32 := Core.get_zero _
    rw [exec_store,v8,v0,show 2164258836#32+664#32=sp+3868#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3868) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t52 : Quiet.Step B img ⟨c52,r41⟩ ⟨c53,r42⟩ := by
    refine Quiet.step_of (by change (0x8000135c#32).getLsbD 0=false;decide) rt2147488604 fun o => ?_
    change Observed.interp B img o (exec c52 _ _) r41 0 [] [] = ⟨.ok c53 r42 [],[]⟩
    have v8 : c52.get 8=2164258836#32 := by simp [c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v13 : c52.get 13=2164255728#32 := by simp [c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v13,show 2164258836#32+644#32=sp+3848#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 962 (by decide +kernel)) (Memory.block_access stack (off := 3848) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t53 : Quiet.Step B img ⟨c53,r42⟩ ⟨c54,r43⟩ := by
    refine Quiet.step_of (by change (0x80001360#32).getLsbD 0=false;decide) rt2147488608 fun o => ?_
    change Observed.interp B img o (exec c53 _ _) r42 0 [] [] = ⟨.ok c54 r43 [],[]⟩
    have v8 : c53.get 8=2164258836#32 := by simp [c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v14 : c53.get 14=2164258944#32 := by simp [c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v14,show 2164258836#32+648#32=sp+3852#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 963 (by decide +kernel)) (Memory.block_access stack (off := 3852) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t54 : Quiet.Step B img ⟨c54,r43⟩ ⟨c55,r44⟩ := by
    refine Quiet.step_of (by change (0x80001364#32).getLsbD 0=false;decide) rt2147488612 fun o => ?_
    change Observed.interp B img o (exec c54 _ _) r43 0 [] [] = ⟨.ok c55 r44 [],[]⟩
    have v8 : c54.get 8=2164258836#32 := by simp [c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v10 : c54.get 10=2164255676#32 := by simp [c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v10,show 2164258836#32+652#32=sp+3856#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 964 (by decide +kernel)) (Memory.block_access stack (off := 3856) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t55 : Quiet.Step B img ⟨c55,r44⟩ ⟨c56,r45⟩ := by
    refine Quiet.step_of (by change (0x80001368#32).getLsbD 0=false;decide) rt2147488616 fun o => ?_
    change Observed.interp B img o (exec c55 _ _) r44 0 [] [] = ⟨.ok c56 r45 [],[]⟩
    have v8 : c55.get 8=2164258836#32 := by simp [c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v11 : c55.get 11=2164258004#32 := by simp [c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v11,show 2164258836#32+656#32=sp+3860#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 965 (by decide +kernel)) (Memory.block_access stack (off := 3860) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t56 : Quiet.Step B img ⟨c56,r45⟩ ⟨c57,r45⟩ := by
    refine Quiet.step_of (by change (0x8000136c#32).getLsbD 0=false;decide) rt2147488620 fun o => ?_
    change Observed.interp B img o (exec c56 _ _) r45 0 [] [] = ⟨.ok c57 r45 [],[]⟩
    have v13 : c56.get 13=2164255728#32 := by simp [c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_opimm,v13]
    change Observed.interp B img o (.done (c56.wr 13 (alu .add 2164255728#32 8#32) (c56.pc+2#32))) r45 0 [] []=_
    rw [show alu .add 2164255728#32 8#32=2164255736#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t57 : Quiet.Step B img ⟨c57,r45⟩ ⟨c58,r46⟩ := by
    refine Quiet.step_of (by change (0x8000136e#32).getLsbD 0=false;decide) rt2147488622 fun o => ?_
    change Observed.interp B img o (exec c57 _ _) r45 0 [] [] = ⟨.ok c58 r46 [],[]⟩
    have v8 : c57.get 8=2164258836#32 := by simp [c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v12 : c57.get 12=832#32 := by simp [c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v12,show 2164258836#32+660#32=sp+3864#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 966 (by decide +kernel)) (Memory.block_access stack (off := 3864) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t58 : Quiet.Step B img ⟨c58,r46⟩ ⟨c59,r47⟩ := by
    refine Quiet.step_of (by change (0x80001372#32).getLsbD 0=false;decide) rt2147488626 fun o => ?_
    change Observed.interp B img o (exec c58 _ _) r46 0 [] [] = ⟨.ok c59 r47 [],[]⟩
    have v8 : c58.get 8=2164258836#32 := by simp [c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v13 : c58.get 13=2164255736#32 := by simp [c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v13,show 2164258836#32+668#32=sp+3872#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 968 (by decide +kernel)) (Memory.block_access stack (off := 3872) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t59 : Quiet.Step B img ⟨c59,r47⟩ ⟨c60,r48⟩ := by
    refine Quiet.step_of (by change (0x80001376#32).getLsbD 0=false;decide) rt2147488630 fun o => ?_
    change Observed.interp B img o (exec c59 _ _) r47 0 [] [] = ⟨.ok c60 r48 [],[]⟩
    have v8 : c59.get 8=2164258836#32 := by simp [c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v14 : c59.get 14=2164258944#32 := by simp [c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v14,show 2164258836#32+672#32=sp+3876#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 969 (by decide +kernel)) (Memory.block_access stack (off := 3876) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t60 : Quiet.Step B img ⟨c60,r48⟩ ⟨c61,r49⟩ := by
    refine Quiet.step_of (by change (0x8000137a#32).getLsbD 0=false;decide) rt2147488634 fun o => ?_
    change Observed.interp B img o (exec c60 _ _) r48 0 [] [] = ⟨.ok c61 r49 [],[]⟩
    have v8 : c60.get 8=2164258836#32 := by simp [c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v10 : c60.get 10=2164255676#32 := by simp [c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v10,show 2164258836#32+676#32=sp+3880#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 970 (by decide +kernel)) (Memory.block_access stack (off := 3880) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t61 : Quiet.Step B img ⟨c61,r49⟩ ⟨c62,r50⟩ := by
    refine Quiet.step_of (by change (0x8000137e#32).getLsbD 0=false;decide) rt2147488638 fun o => ?_
    change Observed.interp B img o (exec c61 _ _) r49 0 [] [] = ⟨.ok c62 r50 [],[]⟩
    have v8 : c61.get 8=2164258836#32 := by simp [c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v11 : c61.get 11=2164258004#32 := by simp [c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v11,show 2164258836#32+680#32=sp+3884#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 971 (by decide +kernel)) (Memory.block_access stack (off := 3884) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t62 : Quiet.Step B img ⟨c62,r50⟩ ⟨c63,r51⟩ := by
    refine Quiet.step_of (by change (0x80001382#32).getLsbD 0=false;decide) rt2147488642 fun o => ?_
    change Observed.interp B img o (exec c62 _ _) r50 0 [] [] = ⟨.ok c63 r51 [],[]⟩
    have v8 : c62.get 8=2164258836#32 := by simp [c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v12 : c62.get 12=832#32 := by simp [c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v12,show 2164258836#32+684#32=sp+3888#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 972 (by decide +kernel)) (Memory.block_access stack (off := 3888) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t63 : Quiet.Step B img ⟨c63,r51⟩ ⟨c64,r52⟩ := by
    refine Quiet.step_of (by change (0x80001386#32).getLsbD 0=false;decide) rt2147488646 fun o => ?_
    change Observed.interp B img o (exec c63 _ _) r51 0 [] [] = ⟨.ok c64 r52 [],[]⟩
    have v8 : c63.get 8=2164258836#32 := by simp [c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v0 : c63.get 0=0#32 := Core.get_zero _
    rw [exec_store,v8,v0,show 2164258836#32+708#32=sp+3912#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3912) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t64 : Quiet.Step B img ⟨c64,r52⟩ ⟨c65,r53⟩ := by
    refine Quiet.step_of (by change (0x8000138a#32).getLsbD 0=false;decide) rt2147488650 fun o => ?_
    change Observed.interp B img o (exec c64 _ _) r52 0 [] [] = ⟨.ok c65 r53 [],[]⟩
    have v8 : c64.get 8=2164258836#32 := by simp [c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v13 : c64.get 13=2164255736#32 := by simp [c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v13,show 2164258836#32+688#32=sp+3892#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 973 (by decide +kernel)) (Memory.block_access stack (off := 3892) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t65 : Quiet.Step B img ⟨c65,r53⟩ ⟨c66,r54⟩ := by
    refine Quiet.step_of (by change (0x8000138e#32).getLsbD 0=false;decide) rt2147488654 fun o => ?_
    change Observed.interp B img o (exec c65 _ _) r53 0 [] [] = ⟨.ok c66 r54 [],[]⟩
    have v8 : c65.get 8=2164258836#32 := by simp [c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v14 : c65.get 14=2164258944#32 := by simp [c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v14,show 2164258836#32+692#32=sp+3896#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 974 (by decide +kernel)) (Memory.block_access stack (off := 3896) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t66 : Quiet.Step B img ⟨c66,r54⟩ ⟨c67,r55⟩ := by
    refine Quiet.step_of (by change (0x80001392#32).getLsbD 0=false;decide) rt2147488658 fun o => ?_
    change Observed.interp B img o (exec c66 _ _) r54 0 [] [] = ⟨.ok c67 r55 [],[]⟩
    have v8 : c66.get 8=2164258836#32 := by simp [c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v10 : c66.get 10=2164255676#32 := by simp [c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v10,show 2164258836#32+696#32=sp+3900#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 975 (by decide +kernel)) (Memory.block_access stack (off := 3900) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t67 : Quiet.Step B img ⟨c67,r55⟩ ⟨c68,r56⟩ := by
    refine Quiet.step_of (by change (0x80001396#32).getLsbD 0=false;decide) rt2147488662 fun o => ?_
    change Observed.interp B img o (exec c67 _ _) r55 0 [] [] = ⟨.ok c68 r56 [],[]⟩
    have v8 : c67.get 8=2164258836#32 := by simp [c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v11 : c67.get 11=2164258004#32 := by simp [c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v11,show 2164258836#32+700#32=sp+3904#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 976 (by decide +kernel)) (Memory.block_access stack (off := 3904) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t68 : Quiet.Step B img ⟨c68,r56⟩ ⟨c69,r56⟩ := by
    refine Quiet.step_of (by change (0x8000139a#32).getLsbD 0=false;decide) rt2147488666 fun o => ?_
    change Observed.interp B img o (exec c68 _ _) r56 0 [] [] = ⟨.ok c69 r56 [],[]⟩
    have v13 : c68.get 13=2164255736#32 := by simp [c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_opimm,v13]
    change Observed.interp B img o (.done (c68.wr 15 (alu .add 2164255736#32 9#32) (c68.pc+4#32))) r56 0 [] []=_
    rw [show alu .add 2164255736#32 9#32=2164255745#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t69 : Quiet.Step B img ⟨c69,r56⟩ ⟨c70,r57⟩ := by
    refine Quiet.step_of (by change (0x8000139e#32).getLsbD 0=false;decide) rt2147488670 fun o => ?_
    change Observed.interp B img o (exec c69 _ _) r56 0 [] [] = ⟨.ok c70 r57 [],[]⟩
    have v8 : c69.get 8=2164258836#32 := by simp [c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v12 : c69.get 12=832#32 := by simp [c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v12,show 2164258836#32+704#32=sp+3908#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 977 (by decide +kernel)) (Memory.block_access stack (off := 3908) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t70 : Quiet.Step B img ⟨c70,r57⟩ ⟨c71,r58⟩ := by
    refine Quiet.step_of (by change (0x800013a2#32).getLsbD 0=false;decide) rt2147488674 fun o => ?_
    change Observed.interp B img o (exec c70 _ _) r57 0 [] [] = ⟨.ok c71 r58 [],[]⟩
    have v8 : c70.get 8=2164258836#32 := by simp [c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v15 : c70.get 15=2164255745#32 := by simp [c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v15,show 2164258836#32+712#32=sp+3916#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 979 (by decide +kernel)) (Memory.block_access stack (off := 3916) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t71 : Quiet.Step B img ⟨c71,r58⟩ ⟨c72,r59⟩ := by
    refine Quiet.step_of (by change (0x800013a6#32).getLsbD 0=false;decide) rt2147488678 fun o => ?_
    change Observed.interp B img o (exec c71 _ _) r58 0 [] [] = ⟨.ok c72 r59 [],[]⟩
    have v8 : c71.get 8=2164258836#32 := by simp [c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v14 : c71.get 14=2164258944#32 := by simp [c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v14,show 2164258836#32+716#32=sp+3920#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 980 (by decide +kernel)) (Memory.block_access stack (off := 3920) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t72 : Quiet.Step B img ⟨c72,r59⟩ ⟨c73,r60⟩ := by
    refine Quiet.step_of (by change (0x800013aa#32).getLsbD 0=false;decide) rt2147488682 fun o => ?_
    change Observed.interp B img o (exec c72 _ _) r59 0 [] [] = ⟨.ok c73 r60 [],[]⟩
    have v8 : c72.get 8=2164258836#32 := by simp [c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v10 : c72.get 10=2164255676#32 := by simp [c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v10,show 2164258836#32+720#32=sp+3924#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 981 (by decide +kernel)) (Memory.block_access stack (off := 3924) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t73 : Quiet.Step B img ⟨c73,r60⟩ ⟨c74,r61⟩ := by
    refine Quiet.step_of (by change (0x800013ae#32).getLsbD 0=false;decide) rt2147488686 fun o => ?_
    change Observed.interp B img o (exec c73 _ _) r60 0 [] [] = ⟨.ok c74 r61 [],[]⟩
    have v8 : c73.get 8=2164258836#32 := by simp [c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v11 : c73.get 11=2164258004#32 := by simp [c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v11,show 2164258836#32+724#32=sp+3928#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 982 (by decide +kernel)) (Memory.block_access stack (off := 3928) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t74 : Quiet.Step B img ⟨c74,r61⟩ ⟨c75,r62⟩ := by
    refine Quiet.step_of (by change (0x800013b2#32).getLsbD 0=false;decide) rt2147488690 fun o => ?_
    change Observed.interp B img o (exec c74 _ _) r61 0 [] [] = ⟨.ok c75 r62 [],[]⟩
    have v8 : c74.get 8=2164258836#32 := by simp [c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v12 : c74.get 12=832#32 := by simp [c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v12,show 2164258836#32+728#32=sp+3932#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 983 (by decide +kernel)) (Memory.block_access stack (off := 3932) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t75 : Quiet.Step B img ⟨c75,r62⟩ ⟨c76,r63⟩ := by
    refine Quiet.step_of (by change (0x800013b6#32).getLsbD 0=false;decide) rt2147488694 fun o => ?_
    change Observed.interp B img o (exec c75 _ _) r62 0 [] [] = ⟨.ok c76 r63 [],[]⟩
    have v8 : c75.get 8=2164258836#32 := by simp [c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    have v22 : c75.get 22=1#32 := by simp [c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
    rw [exec_store,v8,v22,show 2164258836#32+732#32=sp+3936#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3936) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c76,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.step t29 (.step t30 (.step t31 (.step t32 (.step t33 (.step t34 (.step t35 (.step t36 (.step t37 (.step t38 (.step t39 (.step t40 (.step t41 (.step t42 (.step t43 (.step t44 (.step t45 (.step t46 (.step t47 (.step t48 (.step t49 (.step t50 (.step t51 (.step t52 (.step t53 (.step t54 (.step t55 (.step t56 (.step t57 (.step t58 (.step t59 (.step t60 (.step t61 (.step t62 (.step t63 (.step t64 (.step t65 (.step t66 (.step t67 (.step t68 (.step t69 (.step t70 (.step t71 (.step t72 (.step t73 (.step t74 (.single t75))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
  · simp [c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
  · simp [c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
  · simp [c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
  · simp [c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
  · simp [c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
  · simp [c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22]
  · intro reg h11 h13 h10 h12 h14 h18 h15;simp [c76,c75,c74,c73,c72,c71,c70,c69,c68,c67,c66,c65,c64,c63,c62,c61,c60,c59,c58,c57,c56,c55,c54,c53,c52,c51,c50,c49,c48,c47,c46,c45,c44,c43,c42,c41,c40,c39,c38,c37,c36,c35,c34,c33,c32,c31,c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h12,h22,h11,h13,h10,h12,h14,h18,h15]

/-- Exact writable future interval; live App/route/Request/RX regions lie outside it. -/
theorem frame (ram : Word → BitVec 8) (off size : Nat) (bound : off+size≤5232)
    (apart : off+size≤3688 ∨ 3937≤off) : ViewFrame.Region ram (memory ram) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold memory
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    exact FrameOffsets.ne sp off 3936 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3932 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3928 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3924 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3920 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3916 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3908 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3904 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3900 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3896 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3892 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    exact FrameOffsets.ne sp off 3912 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3888 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3884 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3880 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3876 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3872 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3864 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3860 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3856 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3852 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3848 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    exact FrameOffsets.ne sp off 3868 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3844 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3840 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3836 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3832 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3828 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3820 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3816 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3812 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3808 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3804 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    exact FrameOffsets.ne sp off 3824 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3800 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3796 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3792 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3788 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3784 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3776 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3772 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3768 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3764 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3760 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    exact FrameOffsets.ne sp off 3780 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3756 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3752 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3748 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3744 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3740 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .b (fun j => by
    exact FrameOffsets.ne sp off 3736 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3732 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3728 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3724 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3720 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3716 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3712 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3708 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3704 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3700 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3696 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3692 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    exact FrameOffsets.ne sp off 3688 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<4 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<4 at hj;rcases apart with h|h <;>omega))]

/-- These five fields are the actual Read future consumed by the main caller. -/
theorem state_future (ram : Word → BitVec 8) :
    ∀ i : Fin 5, ramRead (memory ram) (0x80fff814#32+BitVec.ofNat 32 (688+4*i.val)) .w=
      (match i.val with | 0 => 0x80ffebf8#32 | 1 => 0x80fff880#32 | 2 => 0x80ffebbc#32 | 3 => 0x80fff4d4#32 | _ => 832#32) := by
  intro i
  have choices : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 := by have := i.isLt;omega
  rcases choices with hi|hi|hi|hi|hi
  · have address : 0x80fff814#32+BitVec.ofNat 32 (688+4*i.val)=sp+3892#32 := by rw [hi];decide +kernel
    rw [address,hi]
    unfold memory
    rw [FrameOffsets.word _ sp _ 3892 3936 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3892 3932 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3892 3928 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3892 3924 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3892 3920 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3892 3916 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3892 3908 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3892 3904 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3892 3900 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3892 3896 .w (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
  · have address : 0x80fff814#32+BitVec.ofNat 32 (688+4*i.val)=sp+3896#32 := by rw [hi];decide +kernel
    rw [address,hi]
    unfold memory
    rw [FrameOffsets.word _ sp _ 3896 3936 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3896 3932 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3896 3928 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3896 3924 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3896 3920 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3896 3916 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3896 3908 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3896 3904 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3896 3900 .w (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
  · have address : 0x80fff814#32+BitVec.ofNat 32 (688+4*i.val)=sp+3900#32 := by rw [hi];decide +kernel
    rw [address,hi]
    unfold memory
    rw [FrameOffsets.word _ sp _ 3900 3936 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3900 3932 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3900 3928 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3900 3924 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3900 3920 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3900 3916 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3900 3908 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3900 3904 .w (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
  · have address : 0x80fff814#32+BitVec.ofNat 32 (688+4*i.val)=sp+3904#32 := by rw [hi];decide +kernel
    rw [address,hi]
    unfold memory
    rw [FrameOffsets.word _ sp _ 3904 3936 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3904 3932 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3904 3928 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3904 3924 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3904 3920 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3904 3916 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3904 3908 .w (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
  · have address : 0x80fff814#32+BitVec.ofNat 32 (688+4*i.val)=sp+3908#32 := by rw [hi];decide +kernel
    rw [address,hi]
    unfold memory
    rw [FrameOffsets.word _ sp _ 3908 3936 .b (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3908 3932 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3908 3928 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3908 3924 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3908 3920 .w (by decide) (by decide) (by decide)]
    rw [FrameOffsets.word _ sp _ 3908 3916 .w (by decide) (by decide) (by decide)]
    exact ramRead_ramWrite_w _ _ _
end E5R.Thermostat.MainRouterSetup
