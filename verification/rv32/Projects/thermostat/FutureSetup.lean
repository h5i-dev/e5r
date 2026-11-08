import Projects.thermostat.FutureCode
import Projects.thermostat.Memory
import Projects.thermostat.Init
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.FutureSetup
open E5R E5R.Thermostat

def execute (c : Core) (ram : Word → BitVec 8) : Machine :=
  let c1 := c.wr 12 0#32 2147486074#32
  let r1 := ramWrite ram 2164255672#32 (0#32) .w
  let c2 := c1.goto 2147486076#32
  let c3 := c2.wr 14 1024#32 2147486080#32
  let r2 := ramWrite r1 2164258836#32 (1024#32) .w
  let c4 := c3.goto 2147486082#32
  let r3 := ramWrite r2 2164258840#32 (1024#32) .w
  let c5 := c4.goto 2147486084#32
  let c6 := c5.wr 10 100#32 2147486088#32
  let r4 := ramWrite r3 2164258844#32 (100#32) .w
  let c7 := c6.goto 2147486090#32
  let r5 := ramWrite r4 2164258848#32 (0x80fff814#32) .w
  let c8 := c7.goto 2147486092#32
  let c9 := c8.wr 15 2164255704#32 2147486094#32
  let r6 := ramWrite r5 2164258852#32 (2164255704#32) .w
  let c10 := c9.goto 2147486096#32
  let c11 := c10.wr 16 2164255676#32 2147486100#32
  let r7 := ramWrite r6 2164258856#32 (2164255676#32) .w
  let c12 := c11.goto 2147486104#32
  let c13 := c12.wr 11 2164255764#32 2147486106#32
  let r8 := ramWrite r7 2164258860#32 (2164255764#32) .w
  let c14 := c13.goto 2147486108#32
  let v14 := extend .w true (ramRead r8 2164255648#32 .w)
  let c15 := c14.wr 10 v14 2147486110#32
  let r9 := ramWrite r8 2164258864#32 (v14) .w
  let c16 := c15.goto 2147486112#32
  let r10 := ramWrite r9 2164258916#32 (1024#32) .w
  let c17 := c16.goto 2147486114#32
  let r11 := ramWrite r10 2164258920#32 (0#32) .w
  let c18 := c17.goto 2147486118#32
  let r12 := ramWrite r11 2164258924#32 (0#32) .w
  let c19 := c18.goto 2147486122#32
  let r13 := ramWrite r12 2164258932#32 (0#32) .b
  let c20 := c19.goto 2147486126#32
  let c21 := c20.wr 13 2164257679#32 2147486130#32
  let c22 := c21.wr 13 2164257812#32 2147486134#32
  let r14 := ramWrite r13 2164258868#32 (2164257812#32) .w
  let c23 := c22.goto 2147486136#32
  let r15 := ramWrite r14 2164258872#32 (1024#32) .w
  let c24 := c23.goto 2147486138#32
  let c25 := c24.wr 17 4096#32 2147486140#32
  let c26 := c25.wr 17 5175#32 2147486144#32
  let c27 := c26.wr 17 2164260807#32 2147486146#32
  let r16 := ramWrite r15 2164258876#32 (2164260807#32) .w
  let c28 := c27.goto 2147486150#32
  let r17 := ramWrite r16 2164258880#32 (0x80fff814#32) .w
  let c29 := c28.goto 2147486152#32
  let r18 := ramWrite r17 2164258884#32 (2164255704#32) .w
  let c30 := c29.goto 2147486154#32
  let r19 := ramWrite r18 2164258888#32 (2164255676#32) .w
  let c31 := c30.goto 2147486158#32
  let r20 := ramWrite r19 2164258892#32 (2164255764#32) .w
  let c32 := c31.goto 2147486160#32
  let r21 := ramWrite r20 2164258896#32 (v14) .w
  let c33 := c32.goto 2147486162#32
  let r22 := ramWrite r21 2164258900#32 (2164257812#32) .w
  let c34 := c33.goto 2147486164#32
  let r23 := ramWrite r22 2164258904#32 (1024#32) .w
  let c35 := c34.goto 2147486166#32
  let r24 := ramWrite r23 2164258908#32 (2164260807#32) .w
  let c36 := c35.goto 2147486170#32
  let r25 := ramWrite r24 2164258912#32 (1024#32) .w
  let c37 := c36.goto 2147486172#32
  let c38 := c37.wr 14 2164257679#32 2147486176#32
  let c39 := c38.wr 14 2164258920#32 2147486180#32
  let r26 := ramWrite r25 2164259272#32 (2164258920#32) .w
  let c40 := c39.goto 2147486184#32
  let r27 := ramWrite r26 2164259276#32 (2164260807#32) .w
  let c41 := c40.goto 2147486188#32
  let r28 := ramWrite r27 2164259284#32 (0#32) .b
  let c42 := c41.goto 2147486192#32
  let c43 := c42.wr 13 2164257679#32 2147486196#32
  let c44 := c43.wr 13 2164258912#32 2147486200#32
  let r29 := ramWrite r28 2164259256#32 (2164258912#32) .w
  let c45 := c44.goto 2147486204#32
  let r30 := ramWrite r29 2164259260#32 (2164258920#32) .w
  let c46 := c45.goto 2147486208#32
  let r31 := ramWrite r30 2164259264#32 (2164260807#32) .w
  let c47 := c46.goto 2147486212#32
  let r32 := ramWrite r31 2164259268#32 (2164258912#32) .w
  let c48 := c47.goto 2147486216#32
  let r33 := ramWrite r32 2164258936#32 (2164255764#32) .w
  let c49 := c48.goto 2147486218#32
  let r34 := ramWrite r33 2164258940#32 (v14) .w
  let c50 := c49.goto 2147486220#32
  let r35 := ramWrite r34 2164258944#32 (2164255764#32) .w
  let c51 := c50.goto 2147486222#32
  let r36 := ramWrite r35 2164258948#32 (v14) .w
  let c52 := c51.goto 2147486224#32
  let v52 := extend .w true (ramRead r36 2164258944#32 .w)
  let c53 := c52.wr 11 v52 2147486226#32
  let v53 := extend .w true (ramRead r36 2164259268#32 .w)
  let c54 := c53.wr 13 v53 2147486230#32
  let c55 := c54.wr 10 4096#32 2147486232#32
  let c56 := c55.wr 10 4520#32 2147486236#32
  let c57 := c56.wr 10 2164260152#32 2147486238#32
  let c58 := c57.wr 1 2147494430#32 2147486242#32
  let c59 := c58.wr 1 2147486246#32 2147494982#32
  ⟨c59,r36⟩

def memory (ram : Word → BitVec 8) : Word → BitVec 8 :=
  let r1 := ramWrite ram 2164255672#32 (0#32) .w
  let r2 := ramWrite r1 2164258836#32 (1024#32) .w
  let r3 := ramWrite r2 2164258840#32 (1024#32) .w
  let r4 := ramWrite r3 2164258844#32 (100#32) .w
  let r5 := ramWrite r4 2164258848#32 (0x80fff814#32) .w
  let r6 := ramWrite r5 2164258852#32 (2164255704#32) .w
  let r7 := ramWrite r6 2164258856#32 (2164255676#32) .w
  let r8 := ramWrite r7 2164258860#32 (2164255764#32) .w
  let v14 := extend .w true (ramRead r8 2164255648#32 .w)
  let r9 := ramWrite r8 2164258864#32 (v14) .w
  let r10 := ramWrite r9 2164258916#32 (1024#32) .w
  let r11 := ramWrite r10 2164258920#32 (0#32) .w
  let r12 := ramWrite r11 2164258924#32 (0#32) .w
  let r13 := ramWrite r12 2164258932#32 (0#32) .b
  let r14 := ramWrite r13 2164258868#32 (2164257812#32) .w
  let r15 := ramWrite r14 2164258872#32 (1024#32) .w
  let r16 := ramWrite r15 2164258876#32 (2164260807#32) .w
  let r17 := ramWrite r16 2164258880#32 (0x80fff814#32) .w
  let r18 := ramWrite r17 2164258884#32 (2164255704#32) .w
  let r19 := ramWrite r18 2164258888#32 (2164255676#32) .w
  let r20 := ramWrite r19 2164258892#32 (2164255764#32) .w
  let r21 := ramWrite r20 2164258896#32 (v14) .w
  let r22 := ramWrite r21 2164258900#32 (2164257812#32) .w
  let r23 := ramWrite r22 2164258904#32 (1024#32) .w
  let r24 := ramWrite r23 2164258908#32 (2164260807#32) .w
  let r25 := ramWrite r24 2164258912#32 (1024#32) .w
  let r26 := ramWrite r25 2164259272#32 (2164258920#32) .w
  let r27 := ramWrite r26 2164259276#32 (2164260807#32) .w
  let r28 := ramWrite r27 2164259284#32 (0#32) .b
  let r29 := ramWrite r28 2164259256#32 (2164258912#32) .w
  let r30 := ramWrite r29 2164259260#32 (2164258920#32) .w
  let r31 := ramWrite r30 2164259264#32 (2164260807#32) .w
  let r32 := ramWrite r31 2164259268#32 (2164258912#32) .w
  let r33 := ramWrite r32 2164258936#32 (2164255764#32) .w
  let r34 := ramWrite r33 2164258940#32 (v14) .w
  let r35 := ramWrite r34 2164258944#32 (2164255764#32) .w
  let r36 := ramWrite r35 2164258948#32 (v14) .w
  r36

def beforeLength (ram : Word → BitVec 8) : Word → BitVec 8 :=
  let r1 := ramWrite ram 2164255672#32 (0#32) .w
  let r2 := ramWrite r1 2164258836#32 (1024#32) .w
  let r3 := ramWrite r2 2164258840#32 (1024#32) .w
  let r4 := ramWrite r3 2164258844#32 (100#32) .w
  let r5 := ramWrite r4 2164258848#32 (0x80fff814#32) .w
  let r6 := ramWrite r5 2164258852#32 (2164255704#32) .w
  let r7 := ramWrite r6 2164258856#32 (2164255676#32) .w
  let r8 := ramWrite r7 2164258860#32 (2164255764#32) .w
  r8

def initialized (ram : Word → BitVec 8) : Word → BitVec 8 :=
  let r1 := ramWrite ram 2164255672#32 (0#32) .w
  let r2 := ramWrite r1 2164258836#32 (1024#32) .w
  let r3 := ramWrite r2 2164258840#32 (1024#32) .w
  let r4 := ramWrite r3 2164258844#32 (100#32) .w
  let r5 := ramWrite r4 2164258848#32 (0x80fff814#32) .w
  let r6 := ramWrite r5 2164258852#32 (2164255704#32) .w
  let r7 := ramWrite r6 2164258856#32 (2164255676#32) .w
  let r8 := ramWrite r7 2164258860#32 (2164255764#32) .w
  let v14 := 2048#32
  let r9 := ramWrite r8 2164258864#32 (v14) .w
  let r10 := ramWrite r9 2164258916#32 (1024#32) .w
  let r11 := ramWrite r10 2164258920#32 (0#32) .w
  let r12 := ramWrite r11 2164258924#32 (0#32) .w
  let r13 := ramWrite r12 2164258932#32 (0#32) .b
  let r14 := ramWrite r13 2164258868#32 (2164257812#32) .w
  let r15 := ramWrite r14 2164258872#32 (1024#32) .w
  let r16 := ramWrite r15 2164258876#32 (2164260807#32) .w
  let r17 := ramWrite r16 2164258880#32 (0x80fff814#32) .w
  let r18 := ramWrite r17 2164258884#32 (2164255704#32) .w
  let r19 := ramWrite r18 2164258888#32 (2164255676#32) .w
  let r20 := ramWrite r19 2164258892#32 (2164255764#32) .w
  let r21 := ramWrite r20 2164258896#32 (v14) .w
  let r22 := ramWrite r21 2164258900#32 (2164257812#32) .w
  let r23 := ramWrite r22 2164258904#32 (1024#32) .w
  let r24 := ramWrite r23 2164258908#32 (2164260807#32) .w
  let r25 := ramWrite r24 2164258912#32 (1024#32) .w
  let r26 := ramWrite r25 2164259272#32 (2164258920#32) .w
  let r27 := ramWrite r26 2164259276#32 (2164260807#32) .w
  let r28 := ramWrite r27 2164259284#32 (0#32) .b
  let r29 := ramWrite r28 2164259256#32 (2164258912#32) .w
  let r30 := ramWrite r29 2164259260#32 (2164258920#32) .w
  let r31 := ramWrite r30 2164259264#32 (2164260807#32) .w
  let r32 := ramWrite r31 2164259268#32 (2164258912#32) .w
  let r33 := ramWrite r32 2164258936#32 (2164255764#32) .w
  let r34 := ramWrite r33 2164258940#32 (v14) .w
  let r35 := ramWrite r34 2164258944#32 (2164255764#32) .w
  let r36 := ramWrite r35 2164258948#32 (v14) .w
  r36

theorem execute_ram (c : Core) (ram : Word → BitVec 8) : (execute c ram).ram = memory ram := rfl

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 2147486072#32) (hsp : c.get 2 = 0x80ffeb90#32)
    (hfp : c.get 8 = 0x80fff814#32) (hm : Memory.Block B 0x80ffeb90#32 5232) :
    DetSteps B img 59 ⟨c,ram⟩ (execute c ram) := by
  let c1 := c.wr 12 0#32 2147486074#32
  let r1 := ramWrite ram 2164255672#32 (0#32) .w
  let c2 := c1.goto 2147486076#32
  let c3 := c2.wr 14 1024#32 2147486080#32
  let r2 := ramWrite r1 2164258836#32 (1024#32) .w
  let c4 := c3.goto 2147486082#32
  let r3 := ramWrite r2 2164258840#32 (1024#32) .w
  let c5 := c4.goto 2147486084#32
  let c6 := c5.wr 10 100#32 2147486088#32
  let r4 := ramWrite r3 2164258844#32 (100#32) .w
  let c7 := c6.goto 2147486090#32
  let r5 := ramWrite r4 2164258848#32 (0x80fff814#32) .w
  let c8 := c7.goto 2147486092#32
  let c9 := c8.wr 15 2164255704#32 2147486094#32
  let r6 := ramWrite r5 2164258852#32 (2164255704#32) .w
  let c10 := c9.goto 2147486096#32
  let c11 := c10.wr 16 2164255676#32 2147486100#32
  let r7 := ramWrite r6 2164258856#32 (2164255676#32) .w
  let c12 := c11.goto 2147486104#32
  let c13 := c12.wr 11 2164255764#32 2147486106#32
  let r8 := ramWrite r7 2164258860#32 (2164255764#32) .w
  let c14 := c13.goto 2147486108#32
  let v14 := extend .w true (ramRead r8 2164255648#32 .w)
  let c15 := c14.wr 10 v14 2147486110#32
  let r9 := ramWrite r8 2164258864#32 (v14) .w
  let c16 := c15.goto 2147486112#32
  let r10 := ramWrite r9 2164258916#32 (1024#32) .w
  let c17 := c16.goto 2147486114#32
  let r11 := ramWrite r10 2164258920#32 (0#32) .w
  let c18 := c17.goto 2147486118#32
  let r12 := ramWrite r11 2164258924#32 (0#32) .w
  let c19 := c18.goto 2147486122#32
  let r13 := ramWrite r12 2164258932#32 (0#32) .b
  let c20 := c19.goto 2147486126#32
  let c21 := c20.wr 13 2164257679#32 2147486130#32
  let c22 := c21.wr 13 2164257812#32 2147486134#32
  let r14 := ramWrite r13 2164258868#32 (2164257812#32) .w
  let c23 := c22.goto 2147486136#32
  let r15 := ramWrite r14 2164258872#32 (1024#32) .w
  let c24 := c23.goto 2147486138#32
  let c25 := c24.wr 17 4096#32 2147486140#32
  let c26 := c25.wr 17 5175#32 2147486144#32
  let c27 := c26.wr 17 2164260807#32 2147486146#32
  let r16 := ramWrite r15 2164258876#32 (2164260807#32) .w
  let c28 := c27.goto 2147486150#32
  let r17 := ramWrite r16 2164258880#32 (0x80fff814#32) .w
  let c29 := c28.goto 2147486152#32
  let r18 := ramWrite r17 2164258884#32 (2164255704#32) .w
  let c30 := c29.goto 2147486154#32
  let r19 := ramWrite r18 2164258888#32 (2164255676#32) .w
  let c31 := c30.goto 2147486158#32
  let r20 := ramWrite r19 2164258892#32 (2164255764#32) .w
  let c32 := c31.goto 2147486160#32
  let r21 := ramWrite r20 2164258896#32 (v14) .w
  let c33 := c32.goto 2147486162#32
  let r22 := ramWrite r21 2164258900#32 (2164257812#32) .w
  let c34 := c33.goto 2147486164#32
  let r23 := ramWrite r22 2164258904#32 (1024#32) .w
  let c35 := c34.goto 2147486166#32
  let r24 := ramWrite r23 2164258908#32 (2164260807#32) .w
  let c36 := c35.goto 2147486170#32
  let r25 := ramWrite r24 2164258912#32 (1024#32) .w
  let c37 := c36.goto 2147486172#32
  let c38 := c37.wr 14 2164257679#32 2147486176#32
  let c39 := c38.wr 14 2164258920#32 2147486180#32
  let r26 := ramWrite r25 2164259272#32 (2164258920#32) .w
  let c40 := c39.goto 2147486184#32
  let r27 := ramWrite r26 2164259276#32 (2164260807#32) .w
  let c41 := c40.goto 2147486188#32
  let r28 := ramWrite r27 2164259284#32 (0#32) .b
  let c42 := c41.goto 2147486192#32
  let c43 := c42.wr 13 2164257679#32 2147486196#32
  let c44 := c43.wr 13 2164258912#32 2147486200#32
  let r29 := ramWrite r28 2164259256#32 (2164258912#32) .w
  let c45 := c44.goto 2147486204#32
  let r30 := ramWrite r29 2164259260#32 (2164258920#32) .w
  let c46 := c45.goto 2147486208#32
  let r31 := ramWrite r30 2164259264#32 (2164260807#32) .w
  let c47 := c46.goto 2147486212#32
  let r32 := ramWrite r31 2164259268#32 (2164258912#32) .w
  let c48 := c47.goto 2147486216#32
  let r33 := ramWrite r32 2164258936#32 (2164255764#32) .w
  let c49 := c48.goto 2147486218#32
  let r34 := ramWrite r33 2164258940#32 (v14) .w
  let c50 := c49.goto 2147486220#32
  let r35 := ramWrite r34 2164258944#32 (2164255764#32) .w
  let c51 := c50.goto 2147486222#32
  let r36 := ramWrite r35 2164258948#32 (v14) .w
  let c52 := c51.goto 2147486224#32
  let v52 := extend .w true (ramRead r36 2164258944#32 .w)
  let c53 := c52.wr 11 v52 2147486226#32
  let v53 := extend .w true (ramRead r36 2164259268#32 .w)
  let c54 := c53.wr 13 v53 2147486230#32
  let c55 := c54.wr 10 4096#32 2147486232#32
  let c56 := c55.wr 10 4520#32 2147486236#32
  let c57 := c56.wr 10 2164260152#32 2147486238#32
  let c58 := c57.wr 1 2147494430#32 2147486242#32
  let c59 := c58.wr 1 2147486246#32 2147494982#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact fu2147486072) fun o => ?_
    have ha : c.get 0 = 0#32 := by simp [Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha,hp]
    simp only [alu]
    rw [show (0#32)+(0x00000000#32) = 0#32 by decide +kernel]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine detStep_of (by change (2147486074#32).getLsbD 0 = false;decide) fu2147486074 fun o => ?_
    have haddr : c1.get 2+0x00000028#32 = 2164255672#32 := by simp [c1,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164255672#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 40) (width := 4) hm (by decide) (by decide)
    have hval : c1.get 0 = 0#32 := by simp [c1,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164255672#32) o (by decide) hmem]
    rfl
  have s2 : DetStep B img ⟨c2,r1⟩ ⟨c3,r1⟩ := by
    refine detStep_of (by change (2147486076#32).getLsbD 0 = false;decide) fu2147486076 fun o => ?_
    have ha : c2.get 0 = 0#32 := by simp [c1,c2,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000400#32) = 1024#32 by decide +kernel]
    rfl
  have s3 : DetStep B img ⟨c3,r1⟩ ⟨c4,r2⟩ := by
    refine detStep_of (by change (2147486080#32).getLsbD 0 = false;decide) fu2147486080 fun o => ?_
    have haddr : c3.get 8+0x00000000#32 = 2164258836#32 := by simp [c1,c2,c3,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258836#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3204) (width := 4) hm (by decide) (by decide)
    have hval : c3.get 14 = 1024#32 := by simp [c1,c2,c3,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258836#32) o (by decide) hmem]
    rfl
  have s4 : DetStep B img ⟨c4,r2⟩ ⟨c5,r3⟩ := by
    refine detStep_of (by change (2147486082#32).getLsbD 0 = false;decide) fu2147486082 fun o => ?_
    have haddr : c4.get 8+0x00000004#32 = 2164258840#32 := by simp [c1,c2,c3,c4,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258840#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3208) (width := 4) hm (by decide) (by decide)
    have hval : c4.get 14 = 1024#32 := by simp [c1,c2,c3,c4,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258840#32) o (by decide) hmem]
    rfl
  have s5 : DetStep B img ⟨c5,r3⟩ ⟨c6,r3⟩ := by
    refine detStep_of (by change (2147486084#32).getLsbD 0 = false;decide) fu2147486084 fun o => ?_
    have ha : c5.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0#32)+(0x00000064#32) = 100#32 by decide +kernel]
    rfl
  have s6 : DetStep B img ⟨c6,r3⟩ ⟨c7,r4⟩ := by
    refine detStep_of (by change (2147486088#32).getLsbD 0 = false;decide) fu2147486088 fun o => ?_
    have haddr : c6.get 8+0x00000008#32 = 2164258844#32 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258844#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3212) (width := 4) hm (by decide) (by decide)
    have hval : c6.get 10 = 100#32 := by simp [c1,c2,c3,c4,c5,c6,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258844#32) o (by decide) hmem]
    rfl
  have s7 : DetStep B img ⟨c7,r4⟩ ⟨c8,r5⟩ := by
    refine detStep_of (by change (2147486090#32).getLsbD 0 = false;decide) fu2147486090 fun o => ?_
    have haddr : c7.get 8+0x0000000c#32 = 2164258848#32 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258848#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3216) (width := 4) hm (by decide) (by decide)
    have hval : c7.get 8 = 0x80fff814#32 := by simp [c1,c2,c3,c4,c5,c6,c7,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258848#32) o (by decide) hmem]
    rfl
  have s8 : DetStep B img ⟨c8,r5⟩ ⟨c9,r5⟩ := by
    refine detStep_of (by change (2147486092#32).getLsbD 0 = false;decide) fu2147486092 fun o => ?_
    have ha : c8.get 2 = 0x80ffeb90#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0x80ffeb90#32)+(0x00000048#32) = 2164255704#32 by decide +kernel]
    rfl
  have s9 : DetStep B img ⟨c9,r5⟩ ⟨c10,r6⟩ := by
    refine detStep_of (by change (2147486094#32).getLsbD 0 = false;decide) fu2147486094 fun o => ?_
    have haddr : c9.get 8+0x00000010#32 = 2164258852#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258852#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3220) (width := 4) hm (by decide) (by decide)
    have hval : c9.get 15 = 2164255704#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258852#32) o (by decide) hmem]
    rfl
  have s10 : DetStep B img ⟨c10,r6⟩ ⟨c11,r6⟩ := by
    refine detStep_of (by change (2147486096#32).getLsbD 0 = false;decide) fu2147486096 fun o => ?_
    have ha : c10.get 2 = 0x80ffeb90#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0x80ffeb90#32)+(0x0000002c#32) = 2164255676#32 by decide +kernel]
    rfl
  have s11 : DetStep B img ⟨c11,r6⟩ ⟨c12,r7⟩ := by
    refine detStep_of (by change (2147486100#32).getLsbD 0 = false;decide) fu2147486100 fun o => ?_
    have haddr : c11.get 8+0x00000014#32 = 2164258856#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258856#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3224) (width := 4) hm (by decide) (by decide)
    have hval : c11.get 16 = 2164255676#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258856#32) o (by decide) hmem]
    rfl
  have s12 : DetStep B img ⟨c12,r7⟩ ⟨c13,r7⟩ := by
    refine detStep_of (by change (2147486104#32).getLsbD 0 = false;decide) fu2147486104 fun o => ?_
    have ha : c12.get 2 = 0x80ffeb90#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0x80ffeb90#32)+(0x00000084#32) = 2164255764#32 by decide +kernel]
    rfl
  have s13 : DetStep B img ⟨c13,r7⟩ ⟨c14,r8⟩ := by
    refine detStep_of (by change (2147486106#32).getLsbD 0 = false;decide) fu2147486106 fun o => ?_
    have haddr : c13.get 8+0x00000018#32 = 2164258860#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258860#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3228) (width := 4) hm (by decide) (by decide)
    have hval : c13.get 11 = 2164255764#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258860#32) o (by decide) hmem]
    rfl
  have s14 : DetStep B img ⟨c14,r8⟩ ⟨c15,r8⟩ := by
    refine detStep_of (by change (2147486108#32).getLsbD 0 = false;decide) fu2147486108 fun o => ?_
    have haddr : c14.get 2+0x00000010#32 = 2164255648#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164255648#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 16) (width := 4) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164255648#32) o (by decide) hmem]
    rfl
  have s15 : DetStep B img ⟨c15,r8⟩ ⟨c16,r9⟩ := by
    refine detStep_of (by change (2147486110#32).getLsbD 0 = false;decide) fu2147486110 fun o => ?_
    have haddr : c15.get 8+0x0000001c#32 = 2164258864#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258864#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3232) (width := 4) hm (by decide) (by decide)
    have hval : c15.get 10 = v14 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258864#32) o (by decide) hmem]
    rfl
  have s16 : DetStep B img ⟨c16,r9⟩ ⟨c17,r10⟩ := by
    refine detStep_of (by change (2147486112#32).getLsbD 0 = false;decide) fu2147486112 fun o => ?_
    have haddr : c16.get 8+0x00000050#32 = 2164258916#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258916#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3284) (width := 4) hm (by decide) (by decide)
    have hval : c16.get 14 = 1024#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258916#32) o (by decide) hmem]
    rfl
  have s17 : DetStep B img ⟨c17,r10⟩ ⟨c18,r11⟩ := by
    refine detStep_of (by change (2147486114#32).getLsbD 0 = false;decide) fu2147486114 fun o => ?_
    have haddr : c17.get 8+0x00000054#32 = 2164258920#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258920#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3288) (width := 4) hm (by decide) (by decide)
    have hval : c17.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258920#32) o (by decide) hmem]
    rfl
  have s18 : DetStep B img ⟨c18,r11⟩ ⟨c19,r12⟩ := by
    refine detStep_of (by change (2147486118#32).getLsbD 0 = false;decide) fu2147486118 fun o => ?_
    have haddr : c18.get 8+0x00000058#32 = 2164258924#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258924#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3292) (width := 4) hm (by decide) (by decide)
    have hval : c18.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258924#32) o (by decide) hmem]
    rfl
  have s19 : DetStep B img ⟨c19,r12⟩ ⟨c20,r13⟩ := by
    refine detStep_of (by change (2147486122#32).getLsbD 0 = false;decide) fu2147486122 fun o => ?_
    have haddr : c19.get 8+0x00000060#32 = 2164258932#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258932#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3300) (width := 1) hm (by decide) (by decide)
    have hval : c19.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164258932#32) o (by decide) hmem]
    rfl
  have s20 : DetStep B img ⟨c20,r13⟩ ⟨c21,r13⟩ := by
    refine detStep_of (by change (2147486126#32).getLsbD 0 = false;decide) fu2147486126 fun o => ?_
    have ha : c20.get 2 = 0x80ffeb90#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0x80ffeb90#32)+(0x000007ff#32) = 2164257679#32 by decide +kernel]
    rfl
  have s21 : DetStep B img ⟨c21,r13⟩ ⟨c22,r13⟩ := by
    refine detStep_of (by change (2147486130#32).getLsbD 0 = false;decide) fu2147486130 fun o => ?_
    have ha : c21.get 13 = 2164257679#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2164257679#32)+(0x00000085#32) = 2164257812#32 by decide +kernel]
    rfl
  have s22 : DetStep B img ⟨c22,r13⟩ ⟨c23,r14⟩ := by
    refine detStep_of (by change (2147486134#32).getLsbD 0 = false;decide) fu2147486134 fun o => ?_
    have haddr : c22.get 8+0x00000020#32 = 2164258868#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258868#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3236) (width := 4) hm (by decide) (by decide)
    have hval : c22.get 13 = 2164257812#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258868#32) o (by decide) hmem]
    rfl
  have s23 : DetStep B img ⟨c23,r14⟩ ⟨c24,r15⟩ := by
    refine detStep_of (by change (2147486136#32).getLsbD 0 = false;decide) fu2147486136 fun o => ?_
    have haddr : c23.get 8+0x00000024#32 = 2164258872#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258872#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3240) (width := 4) hm (by decide) (by decide)
    have hval : c23.get 14 = 1024#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258872#32) o (by decide) hmem]
    rfl
  have s24 : DetStep B img ⟨c24,r15⟩ ⟨c25,r15⟩ := by
    refine detStep_of (by change (2147486138#32).getLsbD 0 = false;decide) fu2147486138 fun o => ?_
    rw [exec_lui]
    rfl
  have s25 : DetStep B img ⟨c25,r15⟩ ⟨c26,r15⟩ := by
    refine detStep_of (by change (2147486140#32).getLsbD 0 = false;decide) fu2147486140 fun o => ?_
    have ha : c25.get 17 = 4096#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (4096#32)+(0x00000437#32) = 5175#32 by decide +kernel]
    rfl
  have s26 : DetStep B img ⟨c26,r15⟩ ⟨c27,r15⟩ := by
    refine detStep_of (by change (2147486144#32).getLsbD 0 = false;decide) fu2147486144 fun o => ?_
    have ha : c26.get 17 = 5175#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hb : c26.get 2 = 0x80ffeb90#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_op,ha,hb]
    simp only [alu]
    rw [show (5175#32)+(0x80ffeb90#32) = 2164260807#32 by decide +kernel]
    rfl
  have s27 : DetStep B img ⟨c27,r15⟩ ⟨c28,r16⟩ := by
    refine detStep_of (by change (2147486146#32).getLsbD 0 = false;decide) fu2147486146 fun o => ?_
    have haddr : c27.get 8+0x00000028#32 = 2164258876#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258876#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3244) (width := 4) hm (by decide) (by decide)
    have hval : c27.get 17 = 2164260807#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258876#32) o (by decide) hmem]
    rfl
  have s28 : DetStep B img ⟨c28,r16⟩ ⟨c29,r17⟩ := by
    refine detStep_of (by change (2147486150#32).getLsbD 0 = false;decide) fu2147486150 fun o => ?_
    have haddr : c28.get 8+0x0000002c#32 = 2164258880#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258880#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3248) (width := 4) hm (by decide) (by decide)
    have hval : c28.get 8 = 0x80fff814#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258880#32) o (by decide) hmem]
    rfl
  have s29 : DetStep B img ⟨c29,r17⟩ ⟨c30,r18⟩ := by
    refine detStep_of (by change (2147486152#32).getLsbD 0 = false;decide) fu2147486152 fun o => ?_
    have haddr : c29.get 8+0x00000030#32 = 2164258884#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258884#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3252) (width := 4) hm (by decide) (by decide)
    have hval : c29.get 15 = 2164255704#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258884#32) o (by decide) hmem]
    rfl
  have s30 : DetStep B img ⟨c30,r18⟩ ⟨c31,r19⟩ := by
    refine detStep_of (by change (2147486154#32).getLsbD 0 = false;decide) fu2147486154 fun o => ?_
    have haddr : c30.get 8+0x00000034#32 = 2164258888#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258888#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3256) (width := 4) hm (by decide) (by decide)
    have hval : c30.get 16 = 2164255676#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258888#32) o (by decide) hmem]
    rfl
  have s31 : DetStep B img ⟨c31,r19⟩ ⟨c32,r20⟩ := by
    refine detStep_of (by change (2147486158#32).getLsbD 0 = false;decide) fu2147486158 fun o => ?_
    have haddr : c31.get 8+0x00000038#32 = 2164258892#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258892#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3260) (width := 4) hm (by decide) (by decide)
    have hval : c31.get 11 = 2164255764#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258892#32) o (by decide) hmem]
    rfl
  have s32 : DetStep B img ⟨c32,r20⟩ ⟨c33,r21⟩ := by
    refine detStep_of (by change (2147486160#32).getLsbD 0 = false;decide) fu2147486160 fun o => ?_
    have haddr : c32.get 8+0x0000003c#32 = 2164258896#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258896#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3264) (width := 4) hm (by decide) (by decide)
    have hval : c32.get 10 = v14 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258896#32) o (by decide) hmem]
    rfl
  have s33 : DetStep B img ⟨c33,r21⟩ ⟨c34,r22⟩ := by
    refine detStep_of (by change (2147486162#32).getLsbD 0 = false;decide) fu2147486162 fun o => ?_
    have haddr : c33.get 8+0x00000040#32 = 2164258900#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258900#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3268) (width := 4) hm (by decide) (by decide)
    have hval : c33.get 13 = 2164257812#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258900#32) o (by decide) hmem]
    rfl
  have s34 : DetStep B img ⟨c34,r22⟩ ⟨c35,r23⟩ := by
    refine detStep_of (by change (2147486164#32).getLsbD 0 = false;decide) fu2147486164 fun o => ?_
    have haddr : c34.get 8+0x00000044#32 = 2164258904#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258904#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3272) (width := 4) hm (by decide) (by decide)
    have hval : c34.get 14 = 1024#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258904#32) o (by decide) hmem]
    rfl
  have s35 : DetStep B img ⟨c35,r23⟩ ⟨c36,r24⟩ := by
    refine detStep_of (by change (2147486166#32).getLsbD 0 = false;decide) fu2147486166 fun o => ?_
    have haddr : c35.get 8+0x00000048#32 = 2164258908#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258908#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3276) (width := 4) hm (by decide) (by decide)
    have hval : c35.get 17 = 2164260807#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258908#32) o (by decide) hmem]
    rfl
  have s36 : DetStep B img ⟨c36,r24⟩ ⟨c37,r25⟩ := by
    refine detStep_of (by change (2147486170#32).getLsbD 0 = false;decide) fu2147486170 fun o => ?_
    have haddr : c36.get 8+0x0000004c#32 = 2164258912#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258912#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3280) (width := 4) hm (by decide) (by decide)
    have hval : c36.get 14 = 1024#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258912#32) o (by decide) hmem]
    rfl
  have s37 : DetStep B img ⟨c37,r25⟩ ⟨c38,r25⟩ := by
    refine detStep_of (by change (2147486172#32).getLsbD 0 = false;decide) fu2147486172 fun o => ?_
    have ha : c37.get 2 = 0x80ffeb90#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0x80ffeb90#32)+(0x000007ff#32) = 2164257679#32 by decide +kernel]
    rfl
  have s38 : DetStep B img ⟨c38,r25⟩ ⟨c39,r25⟩ := by
    refine detStep_of (by change (2147486176#32).getLsbD 0 = false;decide) fu2147486176 fun o => ?_
    have ha : c38.get 14 = 2164257679#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2164257679#32)+(0x000004d9#32) = 2164258920#32 by decide +kernel]
    rfl
  have s39 : DetStep B img ⟨c39,r25⟩ ⟨c40,r26⟩ := by
    refine detStep_of (by change (2147486180#32).getLsbD 0 = false;decide) fu2147486180 fun o => ?_
    have haddr : c39.get 8+0x000001b4#32 = 2164259272#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164259272#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3640) (width := 4) hm (by decide) (by decide)
    have hval : c39.get 14 = 2164258920#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164259272#32) o (by decide) hmem]
    rfl
  have s40 : DetStep B img ⟨c40,r26⟩ ⟨c41,r27⟩ := by
    refine detStep_of (by change (2147486184#32).getLsbD 0 = false;decide) fu2147486184 fun o => ?_
    have haddr : c40.get 8+0x000001b8#32 = 2164259276#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164259276#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3644) (width := 4) hm (by decide) (by decide)
    have hval : c40.get 17 = 2164260807#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164259276#32) o (by decide) hmem]
    rfl
  have s41 : DetStep B img ⟨c41,r27⟩ ⟨c42,r28⟩ := by
    refine detStep_of (by change (2147486188#32).getLsbD 0 = false;decide) fu2147486188 fun o => ?_
    have haddr : c41.get 8+0x000001c0#32 = 2164259284#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164259284#32) 1 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3652) (width := 1) hm (by decide) (by decide)
    have hval : c41.get 0 = 0#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .b) (a := 2164259284#32) o (by decide) hmem]
    rfl
  have s42 : DetStep B img ⟨c42,r28⟩ ⟨c43,r28⟩ := by
    refine detStep_of (by change (2147486192#32).getLsbD 0 = false;decide) fu2147486192 fun o => ?_
    have ha : c42.get 2 = 0x80ffeb90#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (0x80ffeb90#32)+(0x000007ff#32) = 2164257679#32 by decide +kernel]
    rfl
  have s43 : DetStep B img ⟨c43,r28⟩ ⟨c44,r28⟩ := by
    refine detStep_of (by change (2147486196#32).getLsbD 0 = false;decide) fu2147486196 fun o => ?_
    have ha : c43.get 13 = 2164257679#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (2164257679#32)+(0x000004d1#32) = 2164258912#32 by decide +kernel]
    rfl
  have s44 : DetStep B img ⟨c44,r28⟩ ⟨c45,r29⟩ := by
    refine detStep_of (by change (2147486200#32).getLsbD 0 = false;decide) fu2147486200 fun o => ?_
    have haddr : c44.get 8+0x000001a4#32 = 2164259256#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164259256#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3624) (width := 4) hm (by decide) (by decide)
    have hval : c44.get 13 = 2164258912#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164259256#32) o (by decide) hmem]
    rfl
  have s45 : DetStep B img ⟨c45,r29⟩ ⟨c46,r30⟩ := by
    refine detStep_of (by change (2147486204#32).getLsbD 0 = false;decide) fu2147486204 fun o => ?_
    have haddr : c45.get 8+0x000001a8#32 = 2164259260#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164259260#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3628) (width := 4) hm (by decide) (by decide)
    have hval : c45.get 14 = 2164258920#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164259260#32) o (by decide) hmem]
    rfl
  have s46 : DetStep B img ⟨c46,r30⟩ ⟨c47,r31⟩ := by
    refine detStep_of (by change (2147486208#32).getLsbD 0 = false;decide) fu2147486208 fun o => ?_
    have haddr : c46.get 8+0x000001ac#32 = 2164259264#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164259264#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3632) (width := 4) hm (by decide) (by decide)
    have hval : c46.get 17 = 2164260807#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164259264#32) o (by decide) hmem]
    rfl
  have s47 : DetStep B img ⟨c47,r31⟩ ⟨c48,r32⟩ := by
    refine detStep_of (by change (2147486212#32).getLsbD 0 = false;decide) fu2147486212 fun o => ?_
    have haddr : c47.get 8+0x000001b0#32 = 2164259268#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164259268#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3636) (width := 4) hm (by decide) (by decide)
    have hval : c47.get 13 = 2164258912#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164259268#32) o (by decide) hmem]
    rfl
  have s48 : DetStep B img ⟨c48,r32⟩ ⟨c49,r33⟩ := by
    refine detStep_of (by change (2147486216#32).getLsbD 0 = false;decide) fu2147486216 fun o => ?_
    have haddr : c48.get 8+0x00000064#32 = 2164258936#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258936#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3304) (width := 4) hm (by decide) (by decide)
    have hval : c48.get 11 = 2164255764#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258936#32) o (by decide) hmem]
    rfl
  have s49 : DetStep B img ⟨c49,r33⟩ ⟨c50,r34⟩ := by
    refine detStep_of (by change (2147486218#32).getLsbD 0 = false;decide) fu2147486218 fun o => ?_
    have haddr : c49.get 8+0x00000068#32 = 2164258940#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258940#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3308) (width := 4) hm (by decide) (by decide)
    have hval : c49.get 10 = v14 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258940#32) o (by decide) hmem]
    rfl
  have s50 : DetStep B img ⟨c50,r34⟩ ⟨c51,r35⟩ := by
    refine detStep_of (by change (2147486220#32).getLsbD 0 = false;decide) fu2147486220 fun o => ?_
    have haddr : c50.get 8+0x0000006c#32 = 2164258944#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258944#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3312) (width := 4) hm (by decide) (by decide)
    have hval : c50.get 11 = 2164255764#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258944#32) o (by decide) hmem]
    rfl
  have s51 : DetStep B img ⟨c51,r35⟩ ⟨c52,r36⟩ := by
    refine detStep_of (by change (2147486222#32).getLsbD 0 = false;decide) fu2147486222 fun o => ?_
    have haddr : c51.get 8+0x00000070#32 = 2164258948#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,c51,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258948#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3316) (width := 4) hm (by decide) (by decide)
    have hval : c51.get 10 = v14 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,c51,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_store,haddr,hval,interp_store_ram (B := B) (img := img) (w := .w) (a := 2164258948#32) o (by decide) hmem]
    rfl
  have s52 : DetStep B img ⟨c52,r36⟩ ⟨c53,r36⟩ := by
    refine detStep_of (by change (2147486224#32).getLsbD 0 = false;decide) fu2147486224 fun o => ?_
    have haddr : c52.get 8+0x0000006c#32 = 2164258944#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,c51,c52,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164258944#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3312) (width := 4) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164258944#32) o (by decide) hmem]
    rfl
  have s53 : DetStep B img ⟨c53,r36⟩ ⟨c54,r36⟩ := by
    refine detStep_of (by change (2147486226#32).getLsbD 0 = false;decide) fu2147486226 fun o => ?_
    have haddr : c53.get 8+0x000001b0#32 = 2164259268#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,c51,c52,c53,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hmem : B.inRam (2164259268#32) 4 = true := Memory.block_access (B := B) (p := 0x80ffeb90#32) (n := 5232) (off := 3636) (width := 4) hm (by decide) (by decide)
    rw [exec_load,haddr,interp_load_ram (B := B) (img := img) (w := .w) (a := 2164259268#32) o (by decide) hmem]
    rfl
  have s54 : DetStep B img ⟨c54,r36⟩ ⟨c55,r36⟩ := by
    refine detStep_of (by change (2147486230#32).getLsbD 0 = false;decide) fu2147486230 fun o => ?_
    rw [exec_lui]
    rfl
  have s55 : DetStep B img ⟨c55,r36⟩ ⟨c56,r36⟩ := by
    refine detStep_of (by change (2147486232#32).getLsbD 0 = false;decide) fu2147486232 fun o => ?_
    have ha : c55.get 10 = 4096#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,c51,c52,c53,c54,c55,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_opimm,ha]
    simp only [alu]
    rw [show (4096#32)+(0x000001a8#32) = 4520#32 by decide +kernel]
    rfl
  have s56 : DetStep B img ⟨c56,r36⟩ ⟨c57,r36⟩ := by
    refine detStep_of (by change (2147486236#32).getLsbD 0 = false;decide) fu2147486236 fun o => ?_
    have ha : c56.get 10 = 4520#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,c51,c52,c53,c54,c55,c56,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    have hb : c56.get 2 = 0x80ffeb90#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,c51,c52,c53,c54,c55,c56,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_op,ha,hb]
    simp only [alu]
    rw [show (4520#32)+(0x80ffeb90#32) = 2164260152#32 by decide +kernel]
    rfl
  have s57 : DetStep B img ⟨c57,r36⟩ ⟨c58,r36⟩ := by
    refine detStep_of (by change (2147486238#32).getLsbD 0 = false;decide) fu2147486238 fun o => ?_
    rw [exec_auipc]
    change interp B img o (.done (c57.wr 1 (2147486238#32+0x00002000#32) 2147486242#32)) r36 0 [] = _
    rw [show 2147486238#32+0x00002000#32 = 2147494430#32 by decide +kernel]
    rfl
  have s58 : DetStep B img ⟨c58,r36⟩ ⟨c59,r36⟩ := by
    refine detStep_of (by change (2147486242#32).getLsbD 0 = false;decide) fu2147486242 fun o => ?_
    have hv : c58.get 1 = 2147494430#32 := by simp [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,c51,c52,c53,c54,c55,c56,c57,c58,Core.wr_get,Core.wr_get_ne,Core.get_zero,hsp,hfp]
    rw [exec_jalr,hv]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.step s16 (.step s17 (.step s18 (.step s19 (.step s20 (.step s21 (.step s22 (.step s23 (.step s24 (.step s25 (.step s26 (.step s27 (.step s28 (.step s29 (.step s30 (.step s31 (.step s32 (.step s33 (.step s34 (.step s35 (.step s36 (.step s37 (.step s38 (.step s39 (.step s40 (.step s41 (.step s42 (.step s43 (.step s44 (.step s45 (.step s46 (.step s47 (.step s48 (.step s49 (.step s50 (.step s51 (.step s52 (.step s53 (.step s54 (.step s55 (.step s56 (.step s57 (.single s58))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem fields (c : Core) (ram : Word → BitVec 8) :
    (execute c ram).core.pc = 0x80002c46#32 ∧ (execute c ram).core.get 1 = 0x80000a26#32 ∧
    (execute c ram).core.get 10 = 0x80fffd38#32 ∧ (execute c ram).core.get 11 = 0x80ffec14#32 ∧
    (execute c ram).core.get 12 = 0#32 ∧ (execute c ram).core.get 13 = 0x80fff860#32 ∧
    (∀ rr : Reg, rr ≠ 1 → rr ≠ 10 → rr ≠ 11 → rr ≠ 12 → rr ≠ 13 → rr ≠ 14 → rr ≠ 15 → rr ≠ 16 → rr ≠ 17 →
      (execute c ram).core.get rr = c.get rr) ∧ (execute c ram).core.sameCsr c := by
  refine ⟨rfl,rfl,rfl,?_,rfl,?_,?_,by rfl⟩
  · simp [execute,Core.wr_get,Core.wr_get_ne,ramRead,ramWrite,ramPut,byteOf,extend]
  · simp [execute,Core.wr_get,Core.wr_get_ne,ramRead,ramWrite,ramPut,byteOf,extend]
  · intro rr h1 h10 h11 h12 h13 h14 h15 h16 h17
    simp [execute,Core.wr_get_ne,h1,h10,h11,h12,h13,h14,h15,h16,h17]

theorem frame (ram : Word → BitVec 8) (x : Word)
    (hf : ∀ i : Fin 449, x ≠ 0x80fff814#32+BitVec.ofNat 32 i.val)
    (hc : ∀ i : Fin 4, x ≠ 0x80ffebb8#32+BitVec.ofNat 32 i.val) : memory ram x = ram x := by
  unfold memory
  rw [Init.write_frame _ 2164258948#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258948#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (112+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨112+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258944#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258944#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (108+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨108+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258940#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258940#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (104+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨104+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258936#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258936#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (100+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨100+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164259268#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164259268#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (432+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨432+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164259264#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164259264#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (428+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨428+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164259260#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164259260#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (424+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨424+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164259256#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164259256#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (420+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨420+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164259284#32 _ x .b (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164259284#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (448+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨448+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164259276#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164259276#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (440+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨440+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164259272#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164259272#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (436+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨436+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258912#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258912#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (76+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨76+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258908#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258908#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (72+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨72+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258904#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258904#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (68+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨68+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258900#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258900#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (64+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨64+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258896#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258896#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (60+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨60+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258892#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258892#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (56+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨56+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258888#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258888#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (52+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨52+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258884#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258884#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (48+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨48+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258880#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258880#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (44+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨44+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258876#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258876#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (40+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨40+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258872#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258872#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (36+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨36+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258868#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258868#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (32+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨32+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258932#32 _ x .b (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258932#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (96+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨96+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258924#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258924#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (88+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨88+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258920#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258920#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (84+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨84+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258916#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258916#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (80+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨80+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258864#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258864#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (28+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨28+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258860#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258860#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (24+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨24+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258856#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258856#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (20+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨20+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258852#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258852#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (16+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨16+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258848#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258848#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (12+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨12+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258844#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258844#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (8+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨8+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258840#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258840#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (4+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨4+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164258836#32 _ x .w (by
      intro j
      have hj := j.isLt
      simp only [Width.bytes] at hj
      have ha : 2164258836#32+BitVec.ofNat 32 j.val = 0x80fff814#32+BitVec.ofNat 32 (0+j.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
      rw [ha]
      exact hf ⟨0+j.val,by omega⟩)]
  rw [Init.write_frame _ 2164255672#32 _ x .w hc]


theorem length_read (ram : Word → BitVec 8) :
    ramRead (beforeLength ram) 0x80ffeba0#32 .w = ramRead ram 0x80ffeba0#32 .w := by
  apply ramRead_w_congr
  intro k hk
  have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hc with h|h|h|h
  all_goals simp [h,beforeLength,ramWrite,ramPut]

theorem memory_initialized (ram : Word → BitVec 8) (hsize : ramRead ram 0x80ffeba0#32 .w = 2048#32) :
    memory ram = initialized ram := by
  have hh := length_read ram
  unfold beforeLength at hh
  unfold memory initialized
  dsimp only at hh ⊢
  rw [hh,hsize]
  rfl

structure Layout (ram : Word → BitVec 8) : Prop where
  limit : ramRead ram 0x80fff860#32 .w = 1024#32
  filled : ramRead ram 0x80fff868#32 .w = 0#32
  used : ramRead ram (0x80fff814#32+88#32) .w = 0#32
  rx : ramRead ram (0x80fff814#32+108#32) .w = 0x80ffec14#32
  capacity : ramRead ram (0x80fff814#32+112#32) .w = 2048#32
  filledPtr : ramRead ram (0x80fff814#32+436#32) .w = 0x80fff868#32
  uartPtr : ramRead ram (0x80fff814#32+440#32) .w = 0x80ffffc7#32
  poll : ram (0x80fff814#32+448#32) = 0#8

theorem layout (ram : Word → BitVec 8) (hsize : ramRead ram 0x80ffeba0#32 .w = 2048#32) :
    Layout (memory ram) := by
  rw [memory_initialized ram hsize]
  constructor <;> simp [initialized,ramRead,ramWrite,ramPut,byteOf]


theorem layout_preserve (ram ram' : Word → BitVec 8) (h : Layout ram)
    (hf : ∀ i : Fin 449, ram' (0x80fff814#32+BitVec.ofNat 32 i.val) = ram (0x80fff814#32+BitVec.ofNat 32 i.val)) :
    Layout ram' := by
  have hw (off : Nat) (ho : off+4 ≤ 449) :
      ramRead ram' (0x80fff814#32+BitVec.ofNat 32 off) .w = ramRead ram (0x80fff814#32+BitVec.ofNat 32 off) .w := by
    apply ramRead_w_congr
    intro k hk
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hf ⟨off+k,by omega⟩
  exact ⟨(hw 76 (by decide)).trans h.limit,(hw 84 (by decide)).trans h.filled,
    (hw 88 (by decide)).trans h.used,(hw 108 (by decide)).trans h.rx,
    (hw 112 (by decide)).trans h.capacity,(hw 436 (by decide)).trans h.filledPtr,
    (hw 440 (by decide)).trans h.uartPtr,(hf ⟨448,by decide⟩).trans h.poll⟩

end E5R.Thermostat.FutureSetup
