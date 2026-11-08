import Projects.thermostat.ResponseHeadAppendReasonCRLF
import Projects.thermostat.ResponseHeadAppendCTName
import Projects.thermostat.ResponseHeadAppendCTValue
import Projects.thermostat.ResponseHeadAppendCTEnd
import Projects.thermostat.ResponseHeadAppendCLName
import Projects.thermostat.ResponseHeadAppendCLEnd
import Projects.thermostat.ResponseHeadAppendConnection
import Projects.thermostat.ResponseHeadAppendFinalCRLF
import Projects.thermostat.ResponseHeadDecimal
import Projects.thermostat.ResponseHeadSources
import Projects.thermostat.ResponseHeadEnvelope
import Projects.thermostat.HttpReasonEffect
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ResponseHeadSuffix
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

theorem put_time (pos len : Nat) : HttpPut.duration 192 pos len≤7*len+15 := by
  unfold HttpPut.duration;split <;> (first | (split <;> omega) | omega)

theorem contract (c : Core) (ram : Word → BitVec 8) (frame dst ctptr : Word)
    (status body : Nat) (ct : List (BitVec 8)) (close : Bool)
    (hlo : 100≤status) (hhi : status≤599) (hbody : body≤832) (hct : ct.length≤16)
    (hm : Memory.Block B frame 96) (ha : frame.toNat%4=0) (hd : Memory.Block B dst 192)
    (hsep : WordRegions.Disjoint frame 96 dst 192)
    (hsrc : ReadBytes.Span B img ram ctptr ct) (hsstack : WordRegions.Disjoint ctptr ct.length frame 96)
    (hsout : WordRegions.Disjoint ctptr ct.length dst 192)
    (hprefix : Bytes.Span B ram dst (ResponseHeadPrefixSpec.bytes status))
    (hcap : ramRead ram (frame+40#32) .w=192#32)
    (hstatus : ramRead ram (frame+36#32) .w=BitVec.ofNat 32 status)
    (hblen : ramRead ram (frame+28#32) .w=BitVec.ofNat 32 body)
    (hclose : ramRead ram (frame+32#32) .w=ResponseHeadBodyMath.boolWord close)
    (hp : c.pc=0x80003584#32) (h1 : c.get 1=0x80003ffa#32)
    (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=13#32) (h13 : c.get 13=BitVec.ofNat 32 status)
    (h2 : c.get 2=frame+16#32) (h8 : c.get 8=ResponseHeadSources.connection close) (h9 : c.get 9=ResponseHeadSources.clName status) (h18 : c.get 18=ResponseHeadSources.ctEnd ct) (h19 : c.get 19=ResponseHeadSources.clEnd status) (h20 : c.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length) (h21 : c.get 21=ResponseHeadSources.ctName ct) (h23 : c.get 23=dst) (h24 : c.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length) (h25 : c.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status)) (h26 : c.get 26=BitVec.ofNat 32 ct.length) (h27 : c.get 27=ctptr) :
    ∃ d n after, n≤2000 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=0x800040f8#32 ∧ d.get 2=frame+16#32 ∧ d.get 10=1#32 ∧
      d.get 11=BitVec.ofNat 32 (ResponseHeadSpec.bytes status ct body close).length ∧ d.sameCsr c ∧
      Bytes.Span B after dst (ResponseHeadSpec.bytes status ct body close) ∧ ResponseHeadEnvelope.Frame ram after frame dst := by
  have hb := ResponseHeadPlan.bounds status ct body close hlo hhi hct hbody
  let z0 := ResponseHeadPrefixSpec.bytes status
  let z1 := WireSpec.ascii (ResponseHeadSpec.reason status)
  let z2 := WireSpec.ascii "\r\n"
  let z3 := ResponseHeadPlan.ctName ct
  let z4 := ct
  let z5 := ResponseHeadPlan.ctEnd ct
  let z6 := ResponseHeadPlan.clName status
  let z7 := ResponseHeadPlan.decimal status body
  let z8 := ResponseHeadPlan.clEnd status
  let z9 := ResponseHeadSpec.connection close
  let z10 := WireSpec.ascii "\r\n"
  let xs0 := z0
  let xs1 := xs0++z1
  let xs2 := xs1++z2
  let xs3 := xs2++z3
  let xs4 := xs3++z4
  let xs5 := xs4++z5
  let xs6 := xs5++z6
  let xs7 := xs6++z7
  let xs8 := xs7++z8
  let xs9 := xs8++z9
  let xs10 := xs9++z10
  have eq0 : xs0=ResponseHeadPlan.part status ct body close 1 := by
    simp only [xs0,z0,ResponseHeadPlan.part,ResponseHeadPlan.chunks,List.take,List.flatten,List.append_eq,List.append_nil,List.append_assoc]
  have bound0 : xs0.length≤120 := by rw [eq0];exact hb.1 ⟨1,by decide⟩
  have eq1 : xs1=ResponseHeadPlan.part status ct body close 2 := by
    simp only [xs1,xs0,z0,z1,ResponseHeadPlan.part,ResponseHeadPlan.chunks,List.take,List.flatten,List.append_eq,List.append_nil,List.append_assoc]
  have bound1 : xs1.length≤120 := by rw [eq1];exact hb.1 ⟨2,by decide⟩
  have eq2 : xs2=ResponseHeadPlan.part status ct body close 3 := by
    simp only [xs2,xs1,xs0,z0,z1,z2,ResponseHeadPlan.part,ResponseHeadPlan.chunks,List.take,List.flatten,List.append_eq,List.append_nil,List.append_assoc]
  have bound2 : xs2.length≤120 := by rw [eq2];exact hb.1 ⟨3,by decide⟩
  have eq3 : xs3=ResponseHeadPlan.part status ct body close 4 := by
    simp only [xs3,xs2,xs1,xs0,z0,z1,z2,z3,ResponseHeadPlan.part,ResponseHeadPlan.chunks,List.take,List.flatten,List.append_eq,List.append_nil,List.append_assoc]
  have bound3 : xs3.length≤120 := by rw [eq3];exact hb.1 ⟨4,by decide⟩
  have eq4 : xs4=ResponseHeadPlan.part status ct body close 5 := by
    simp only [xs4,xs3,xs2,xs1,xs0,z0,z1,z2,z3,z4,ResponseHeadPlan.part,ResponseHeadPlan.chunks,List.take,List.flatten,List.append_eq,List.append_nil,List.append_assoc]
  have bound4 : xs4.length≤120 := by rw [eq4];exact hb.1 ⟨5,by decide⟩
  have eq5 : xs5=ResponseHeadPlan.part status ct body close 6 := by
    simp only [xs5,xs4,xs3,xs2,xs1,xs0,z0,z1,z2,z3,z4,z5,ResponseHeadPlan.part,ResponseHeadPlan.chunks,List.take,List.flatten,List.append_eq,List.append_nil,List.append_assoc]
  have bound5 : xs5.length≤120 := by rw [eq5];exact hb.1 ⟨6,by decide⟩
  have eq6 : xs6=ResponseHeadPlan.part status ct body close 7 := by
    simp only [xs6,xs5,xs4,xs3,xs2,xs1,xs0,z0,z1,z2,z3,z4,z5,z6,ResponseHeadPlan.part,ResponseHeadPlan.chunks,List.take,List.flatten,List.append_eq,List.append_nil,List.append_assoc]
  have bound6 : xs6.length≤120 := by rw [eq6];exact hb.1 ⟨7,by decide⟩
  have eq7 : xs7=ResponseHeadPlan.part status ct body close 8 := by
    simp only [xs7,xs6,xs5,xs4,xs3,xs2,xs1,xs0,z0,z1,z2,z3,z4,z5,z6,z7,ResponseHeadPlan.part,ResponseHeadPlan.chunks,List.take,List.flatten,List.append_eq,List.append_nil,List.append_assoc]
  have bound7 : xs7.length≤120 := by rw [eq7];exact hb.1 ⟨8,by decide⟩
  have eq8 : xs8=ResponseHeadPlan.part status ct body close 9 := by
    simp only [xs8,xs7,xs6,xs5,xs4,xs3,xs2,xs1,xs0,z0,z1,z2,z3,z4,z5,z6,z7,z8,ResponseHeadPlan.part,ResponseHeadPlan.chunks,List.take,List.flatten,List.append_eq,List.append_nil,List.append_assoc]
  have bound8 : xs8.length≤120 := by rw [eq8];exact hb.1 ⟨9,by decide⟩
  have eq9 : xs9=ResponseHeadPlan.part status ct body close 10 := by
    simp only [xs9,xs8,xs7,xs6,xs5,xs4,xs3,xs2,xs1,xs0,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,ResponseHeadPlan.part,ResponseHeadPlan.chunks,List.take,List.flatten,List.append_eq,List.append_nil,List.append_assoc]
  have bound9 : xs9.length≤120 := by rw [eq9];exact hb.1 ⟨10,by decide⟩
  have eq10 : xs10=ResponseHeadPlan.part status ct body close 11 := by
    simp only [xs10,xs9,xs8,xs7,xs6,xs5,xs4,xs3,xs2,xs1,xs0,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,ResponseHeadPlan.part,ResponseHeadPlan.chunks,List.take,List.flatten,List.append_eq,List.append_nil,List.append_assoc]
  have bound10 : xs10.length≤120 := by rw [eq10];exact hb.1 ⟨11,by decide⟩
  have len0 : xs0.length=13 := ResponseHeadPrefixSpec.length status hlo hhi
  have decpos : xs6.length≤94 := by rw [eq6];exact hb.2
  have sep0 : WordRegions.Disjoint dst 192 frame 0 := WordRegions.shrink (WordRegions.symm hsep) (by decide) (by decide)
  have sep16 : WordRegions.Disjoint dst 192 frame 16 := WordRegions.shrink (WordRegions.symm hsep) (by decide) (by decide)
  obtain ⟨c1,n1,bn1,t1,r1,v1_10,v1_11,ef1⟩ := HttpReasonEffect.contract c ram frame dst status hlo hhi hp h10 h11 h12 h13 hd
  let m1 := ByteWrite.write ram (dst+13#32) z1
  have p1 : c1.pc=0x80003ffa#32 := by rw [r1.pc,h1];decide +kernel
  have g1_2 : c1.get 2=frame+16#32 := (ResponseHeadCallee.returned r1 2 (by decide)).trans h2
  have g1_8 : c1.get 8=ResponseHeadSources.connection close := (ResponseHeadCallee.returned r1 8 (by decide)).trans h8
  have g1_9 : c1.get 9=ResponseHeadSources.clName status := (ResponseHeadCallee.returned r1 9 (by decide)).trans h9
  have g1_18 : c1.get 18=ResponseHeadSources.ctEnd ct := (ResponseHeadCallee.returned r1 18 (by decide)).trans h18
  have g1_19 : c1.get 19=ResponseHeadSources.clEnd status := (ResponseHeadCallee.returned r1 19 (by decide)).trans h19
  have g1_20 : c1.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length := (ResponseHeadCallee.returned r1 20 (by decide)).trans h20
  have g1_21 : c1.get 21=ResponseHeadSources.ctName ct := (ResponseHeadCallee.returned r1 21 (by decide)).trans h21
  have g1_23 : c1.get 23=dst := (ResponseHeadCallee.returned r1 23 (by decide)).trans h23
  have g1_24 : c1.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length := (ResponseHeadCallee.returned r1 24 (by decide)).trans h24
  have g1_25 : c1.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) := (ResponseHeadCallee.returned r1 25 (by decide)).trans h25
  have g1_26 : c1.get 26=BitVec.ofNat 32 ct.length := (ResponseHeadCallee.returned r1 26 (by decide)).trans h26
  have g1_27 : c1.get 27=ctptr := (ResponseHeadCallee.returned r1 27 (by decide)).trans h27
  have k1 : c1.sameCsr c := r1.csr
  have e1 : ResponseHeadEnvelope.Frame ram m1 frame dst := ResponseHeadEnvelope.effect ef1 (by decide) (by have hr := ResponseHeadSpec.reason_bound status;omega)
  have ep1 : OutputEffect.Effect B ram m1 frame dst 0 xs0.length z1 := by rw [len0];exact ef1
  have x1 : Bytes.Span B m1 dst xs1 := by
    apply OutputEffect.accumulates ep1 hd (by decide) (by have hr := ResponseHeadSpec.reason_bound status;change xs0.length+z1.length≤192;dsimp [z1];omega) sep0 hprefix
  have vpos1 : c1.get 11=BitVec.ofNat 32 xs1.length := by simpa only [xs1,List.length_append,len0] using v1_11
  have cap1 := (ResponseHeadEnvelope.word e1 hsep 40 (by decide) (by decide)).trans hcap
  have src2 := ResponseHeadLiterals.span m1 0
  have sep2 := ResponseHeadLiterals.disjoint dst 192 hd 0
  obtain ⟨c2,t2,p2,upd2_22,f2,kk2,v2_10,v2_11,ef2⟩ := ResponseHeadAppendReasonCRLF.contract B c1 m1 frame dst (0#32) (0#32) xs1.length z2 g1_2 vpos1 g1_23 hm ha cap1 v1_10 (by rfl) (by have hh := bound2;simpa only [xs2,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) src2 hd sep2 p1
  let m2 := HttpPut.memory m1 dst 192#32 xs1.length z2
  have g2_2 : c2.get 2=frame+16#32 := (f2 2 (by decide) (by decide)).trans g1_2
  have g2_8 : c2.get 8=ResponseHeadSources.connection close := (f2 8 (by decide) (by decide)).trans g1_8
  have g2_9 : c2.get 9=ResponseHeadSources.clName status := (f2 9 (by decide) (by decide)).trans g1_9
  have g2_18 : c2.get 18=ResponseHeadSources.ctEnd ct := (f2 18 (by decide) (by decide)).trans g1_18
  have g2_19 : c2.get 19=ResponseHeadSources.clEnd status := (f2 19 (by decide) (by decide)).trans g1_19
  have g2_20 : c2.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length := (f2 20 (by decide) (by decide)).trans g1_20
  have g2_21 : c2.get 21=ResponseHeadSources.ctName ct := (f2 21 (by decide) (by decide)).trans g1_21
  have g2_23 : c2.get 23=dst := (f2 23 (by decide) (by decide)).trans g1_23
  have g2_24 : c2.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length := (f2 24 (by decide) (by decide)).trans g1_24
  have g2_25 : c2.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) := (f2 25 (by decide) (by decide)).trans g1_25
  have g2_26 : c2.get 26=BitVec.ofNat 32 ct.length := (f2 26 (by decide) (by decide)).trans g1_26
  have g2_27 : c2.get 27=ctptr := (f2 27 (by decide) (by decide)).trans g1_27
  have g2_22 : c2.get 22=1#32 := upd2_22
  have k2 : c2.sameCsr c := kk2.trans k1
  have e2 := ResponseHeadEnvelope.trans e1 (ResponseHeadEnvelope.effect ef2 (by decide) (by have hh := bound2;simpa only [xs2,List.length_append] using Nat.le_trans hh (by decide : 120≤192)))
  have x2 : Bytes.Span B m2 dst xs2 := OutputEffect.accumulates ef2 hd (by decide) (by have hh := bound2;simpa only [xs2,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) sep0 x1
  have vpos2 : c2.get 11=BitVec.ofNat 32 xs2.length := by simpa only [xs2,List.length_append] using v2_11
  have zn2 : z2.length≤19 := by
    decide +kernel
  have bn2 : 10+HttpPut.duration 192 xs1.length z2.length≤200 := by have hh := put_time xs1.length z2.length;omega
  have cap2 := (ResponseHeadEnvelope.word e2 hsep 40 (by decide) (by decide)).trans hcap
  obtain ⟨src3,sep3⟩ := ResponseHeadSources.ct_name m2 dst ct hd
  obtain ⟨c3,t3,p3,f3,kk3,v3_10,v3_11,ef3⟩ := ResponseHeadAppendCTName.contract B c2 m2 frame dst (ResponseHeadSources.ctName ct) (BitVec.ofNat 32 z3.length) xs2.length z3 g2_2 vpos2 g2_23 hm ha cap2 v2_10 g2_21 g2_24 g2_22 (by rfl) (by have hh := bound3;simpa only [xs3,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) src3 hd sep3 p2
  let m3 := HttpPut.memory m2 dst 192#32 xs2.length z3
  have g3_2 : c3.get 2=frame+16#32 := (f3 2 (by decide) (by decide)).trans g2_2
  have g3_8 : c3.get 8=ResponseHeadSources.connection close := (f3 8 (by decide) (by decide)).trans g2_8
  have g3_9 : c3.get 9=ResponseHeadSources.clName status := (f3 9 (by decide) (by decide)).trans g2_9
  have g3_18 : c3.get 18=ResponseHeadSources.ctEnd ct := (f3 18 (by decide) (by decide)).trans g2_18
  have g3_19 : c3.get 19=ResponseHeadSources.clEnd status := (f3 19 (by decide) (by decide)).trans g2_19
  have g3_20 : c3.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length := (f3 20 (by decide) (by decide)).trans g2_20
  have g3_21 : c3.get 21=ResponseHeadSources.ctName ct := (f3 21 (by decide) (by decide)).trans g2_21
  have g3_23 : c3.get 23=dst := (f3 23 (by decide) (by decide)).trans g2_23
  have g3_24 : c3.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length := (f3 24 (by decide) (by decide)).trans g2_24
  have g3_25 : c3.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) := (f3 25 (by decide) (by decide)).trans g2_25
  have g3_26 : c3.get 26=BitVec.ofNat 32 ct.length := (f3 26 (by decide) (by decide)).trans g2_26
  have g3_27 : c3.get 27=ctptr := (f3 27 (by decide) (by decide)).trans g2_27
  have g3_22 : c3.get 22=1#32 := (f3 22 (by decide) (by decide)).trans g2_22
  have k3 : c3.sameCsr c := kk3.trans k2
  have e3 := ResponseHeadEnvelope.trans e2 (ResponseHeadEnvelope.effect ef3 (by decide) (by have hh := bound3;simpa only [xs3,List.length_append] using Nat.le_trans hh (by decide : 120≤192)))
  have x3 : Bytes.Span B m3 dst xs3 := OutputEffect.accumulates ef3 hd (by decide) (by have hh := bound3;simpa only [xs3,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) sep0 x2
  have vpos3 : c3.get 11=BitVec.ofNat 32 xs3.length := by simpa only [xs3,List.length_append] using v3_11
  have zn3 : z3.length≤19 := by
    dsimp [z3,ResponseHeadPlan.ctName];split <;> decide +kernel
  have bn3 : 8+HttpPut.duration 192 xs2.length z3.length≤200 := by have hh := put_time xs2.length z3.length;omega
  have cap3 := (ResponseHeadEnvelope.word e3 hsep 40 (by decide) (by decide)).trans hcap
  have src4 := ReadFrame.span hsrc (ResponseHeadEnvelope.region e3 (WordRegions.shrink hsstack (by omega) (by decide)) hsout)
  obtain ⟨c4,t4,p4,upd4_21,f4,kk4,v4_10,v4_11,ef4⟩ := ResponseHeadAppendCTValue.contract B c3 m3 frame dst (ctptr) (BitVec.ofNat 32 ct.length) xs3.length z4 g3_2 vpos3 g3_23 hm ha cap3 v3_10 g3_27 g3_26 (by rfl) (by have hh := bound4;simpa only [xs4,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) src4 hd hsout p3
  let m4 := HttpPut.memory m3 dst 192#32 xs3.length z4
  have g4_2 : c4.get 2=frame+16#32 := (f4 2 (by decide) (by decide)).trans g3_2
  have g4_8 : c4.get 8=ResponseHeadSources.connection close := (f4 8 (by decide) (by decide)).trans g3_8
  have g4_9 : c4.get 9=ResponseHeadSources.clName status := (f4 9 (by decide) (by decide)).trans g3_9
  have g4_18 : c4.get 18=ResponseHeadSources.ctEnd ct := (f4 18 (by decide) (by decide)).trans g3_18
  have g4_19 : c4.get 19=ResponseHeadSources.clEnd status := (f4 19 (by decide) (by decide)).trans g3_19
  have g4_20 : c4.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length := (f4 20 (by decide) (by decide)).trans g3_20
  have g4_21 : c4.get 21=1#32 := upd4_21
  have g4_23 : c4.get 23=dst := (f4 23 (by decide) (by decide)).trans g3_23
  have g4_24 : c4.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length := (f4 24 (by decide) (by decide)).trans g3_24
  have g4_25 : c4.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) := (f4 25 (by decide) (by decide)).trans g3_25
  have g4_26 : c4.get 26=BitVec.ofNat 32 ct.length := (f4 26 (by decide) (by decide)).trans g3_26
  have g4_27 : c4.get 27=ctptr := (f4 27 (by decide) (by decide)).trans g3_27
  have g4_22 : c4.get 22=1#32 := (f4 22 (by decide) (by decide)).trans g3_22
  have k4 : c4.sameCsr c := kk4.trans k3
  have e4 := ResponseHeadEnvelope.trans e3 (ResponseHeadEnvelope.effect ef4 (by decide) (by have hh := bound4;simpa only [xs4,List.length_append] using Nat.le_trans hh (by decide : 120≤192)))
  have x4 : Bytes.Span B m4 dst xs4 := OutputEffect.accumulates ef4 hd (by decide) (by have hh := bound4;simpa only [xs4,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) sep0 x3
  have vpos4 : c4.get 11=BitVec.ofNat 32 xs4.length := by simpa only [xs4,List.length_append] using v4_11
  have zn4 : z4.length≤19 := by
    exact Nat.le_trans hct (by decide)
  have bn4 : 9+HttpPut.duration 192 xs3.length z4.length≤200 := by have hh := put_time xs3.length z4.length;omega
  have cap4 := (ResponseHeadEnvelope.word e4 hsep 40 (by decide) (by decide)).trans hcap
  obtain ⟨src5,sep5⟩ := ResponseHeadSources.ct_end m4 dst ct hd
  obtain ⟨c5,t5,p5,f5,kk5,v5_10,v5_11,ef5⟩ := ResponseHeadAppendCTEnd.contract B c4 m4 frame dst (ResponseHeadSources.ctEnd ct) (BitVec.ofNat 32 z5.length) xs4.length z5 g4_2 vpos4 g4_23 hm ha cap4 v4_10 g4_18 g4_20 g4_21 (by rfl) (by have hh := bound5;simpa only [xs5,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) src5 hd sep5 p4
  let m5 := HttpPut.memory m4 dst 192#32 xs4.length z5
  have g5_2 : c5.get 2=frame+16#32 := (f5 2 (by decide) (by decide)).trans g4_2
  have g5_8 : c5.get 8=ResponseHeadSources.connection close := (f5 8 (by decide) (by decide)).trans g4_8
  have g5_9 : c5.get 9=ResponseHeadSources.clName status := (f5 9 (by decide) (by decide)).trans g4_9
  have g5_18 : c5.get 18=ResponseHeadSources.ctEnd ct := (f5 18 (by decide) (by decide)).trans g4_18
  have g5_19 : c5.get 19=ResponseHeadSources.clEnd status := (f5 19 (by decide) (by decide)).trans g4_19
  have g5_20 : c5.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length := (f5 20 (by decide) (by decide)).trans g4_20
  have g5_21 : c5.get 21=1#32 := (f5 21 (by decide) (by decide)).trans g4_21
  have g5_23 : c5.get 23=dst := (f5 23 (by decide) (by decide)).trans g4_23
  have g5_24 : c5.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length := (f5 24 (by decide) (by decide)).trans g4_24
  have g5_25 : c5.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) := (f5 25 (by decide) (by decide)).trans g4_25
  have g5_26 : c5.get 26=BitVec.ofNat 32 ct.length := (f5 26 (by decide) (by decide)).trans g4_26
  have g5_27 : c5.get 27=ctptr := (f5 27 (by decide) (by decide)).trans g4_27
  have g5_22 : c5.get 22=1#32 := (f5 22 (by decide) (by decide)).trans g4_22
  have k5 : c5.sameCsr c := kk5.trans k4
  have e5 := ResponseHeadEnvelope.trans e4 (ResponseHeadEnvelope.effect ef5 (by decide) (by have hh := bound5;simpa only [xs5,List.length_append] using Nat.le_trans hh (by decide : 120≤192)))
  have x5 : Bytes.Span B m5 dst xs5 := OutputEffect.accumulates ef5 hd (by decide) (by have hh := bound5;simpa only [xs5,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) sep0 x4
  have vpos5 : c5.get 11=BitVec.ofNat 32 xs5.length := by simpa only [xs5,List.length_append] using v5_11
  have zn5 : z5.length≤19 := by
    dsimp [z5,ResponseHeadPlan.ctEnd];split <;> decide +kernel
  have bn5 : 8+HttpPut.duration 192 xs4.length z5.length≤200 := by have hh := put_time xs4.length z5.length;omega
  have cap5 := (ResponseHeadEnvelope.word e5 hsep 40 (by decide) (by decide)).trans hcap
  obtain ⟨src6,sep6,len6⟩ := ResponseHeadSources.cl_name m5 dst status hd
  obtain ⟨c6,t6,p6,upd6_18,f6,kk6,v6_10,v6_11,ef6⟩ := ResponseHeadAppendCLName.contract B c5 m5 frame dst (ResponseHeadSources.clName status) (ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status)) xs5.length z6 g5_2 vpos5 g5_23 hm ha cap5 v5_10 g5_25 g5_9 len6 (by have hh := bound6;simpa only [xs6,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) src6 hd sep6 p5
  let m6 := HttpPut.memory m5 dst 192#32 xs5.length z6
  have g6_2 : c6.get 2=frame+16#32 := (f6 2 (by decide) (by decide)).trans g5_2
  have g6_8 : c6.get 8=ResponseHeadSources.connection close := (f6 8 (by decide) (by decide)).trans g5_8
  have g6_9 : c6.get 9=ResponseHeadSources.clName status := (f6 9 (by decide) (by decide)).trans g5_9
  have g6_18 : c6.get 18=1#32 := upd6_18
  have g6_19 : c6.get 19=ResponseHeadSources.clEnd status := (f6 19 (by decide) (by decide)).trans g5_19
  have g6_20 : c6.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length := (f6 20 (by decide) (by decide)).trans g5_20
  have g6_21 : c6.get 21=1#32 := (f6 21 (by decide) (by decide)).trans g5_21
  have g6_23 : c6.get 23=dst := (f6 23 (by decide) (by decide)).trans g5_23
  have g6_24 : c6.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length := (f6 24 (by decide) (by decide)).trans g5_24
  have g6_25 : c6.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) := (f6 25 (by decide) (by decide)).trans g5_25
  have g6_26 : c6.get 26=BitVec.ofNat 32 ct.length := (f6 26 (by decide) (by decide)).trans g5_26
  have g6_27 : c6.get 27=ctptr := (f6 27 (by decide) (by decide)).trans g5_27
  have g6_22 : c6.get 22=1#32 := (f6 22 (by decide) (by decide)).trans g5_22
  have k6 : c6.sameCsr c := kk6.trans k5
  have e6 := ResponseHeadEnvelope.trans e5 (ResponseHeadEnvelope.effect ef6 (by decide) (by have hh := bound6;simpa only [xs6,List.length_append] using Nat.le_trans hh (by decide : 120≤192)))
  have x6 : Bytes.Span B m6 dst xs6 := OutputEffect.accumulates ef6 hd (by decide) (by have hh := bound6;simpa only [xs6,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) sep0 x5
  have vpos6 : c6.get 11=BitVec.ofNat 32 xs6.length := by simpa only [xs6,List.length_append] using v6_11
  have zn6 : z6.length≤19 := by
    dsimp [z6,ResponseHeadPlan.clName];split <;> decide +kernel
  have bn6 : 9+HttpPut.duration 192 xs5.length z6.length≤200 := by have hh := put_time xs5.length z6.length;omega
  have cap6 := (ResponseHeadEnvelope.word e6 hsep 40 (by decide) (by decide)).trans hcap
  have stat6 := (ResponseHeadEnvelope.word e6 hsep 36 (by decide) (by decide)).trans hstatus
  have body6 := (ResponseHeadEnvelope.word e6 hsep 28 (by decide) (by decide)).trans hblen
  obtain ⟨c7,n7,bn7,t7,p7,v7_12,f7,kk7,ef7⟩ := ResponseHeadDecimal.contract B c6 m6 frame dst xs6.length status body hhi hbody decpos g6_2 vpos6 v6_10 g6_18 g6_23 hm ha hd hsep cap6 stat6 body6 p6
  let m7 := ResponseHeadDecimal.memory m6 frame dst xs6.length status body
  have g7_2 : c7.get 2=frame+16#32 := (f7 2 (by decide) (by decide)).trans g6_2
  have g7_8 : c7.get 8=ResponseHeadSources.connection close := (f7 8 (by decide) (by decide)).trans g6_8
  have g7_9 : c7.get 9=ResponseHeadSources.clName status := (f7 9 (by decide) (by decide)).trans g6_9
  have g7_18 : c7.get 18=1#32 := (f7 18 (by decide) (by decide)).trans g6_18
  have g7_19 : c7.get 19=ResponseHeadSources.clEnd status := (f7 19 (by decide) (by decide)).trans g6_19
  have g7_20 : c7.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length := (f7 20 (by decide) (by decide)).trans g6_20
  have g7_21 : c7.get 21=1#32 := (f7 21 (by decide) (by decide)).trans g6_21
  have g7_23 : c7.get 23=dst := (f7 23 (by decide) (by decide)).trans g6_23
  have g7_24 : c7.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length := (f7 24 (by decide) (by decide)).trans g6_24
  have g7_25 : c7.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) := (f7 25 (by decide) (by decide)).trans g6_25
  have g7_26 : c7.get 26=BitVec.ofNat 32 ct.length := (f7 26 (by decide) (by decide)).trans g6_26
  have g7_27 : c7.get 27=ctptr := (f7 27 (by decide) (by decide)).trans g6_27
  have g7_22 : c7.get 22=1#32 := (f7 22 (by decide) (by decide)).trans g6_22
  have k7 : c7.sameCsr c := kk7.trans k6
  have e7 := ResponseHeadEnvelope.trans e6 (ResponseHeadEnvelope.effect ef7 (by decide) (by have hh := bound7;simpa only [xs7,List.length_append] using Nat.le_trans hh (by decide : 120≤192)))
  have x7 : Bytes.Span B m7 dst xs7 := OutputEffect.accumulates ef7 hd (by decide) (by have hh := bound7;simpa only [xs7,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) sep16 x6
  have vpos7 : c7.get 12=BitVec.ofNat 32 xs7.length := by simpa only [xs7,List.length_append] using v7_12
  have cap7 := (ResponseHeadEnvelope.word e7 hsep 40 (by decide) (by decide)).trans hcap
  obtain ⟨src8,sep8,len8⟩ := ResponseHeadSources.cl_end m7 dst status hd
  obtain ⟨c8,t8,p8,f8,kk8,v8_10,v8_11,ef8⟩ := ResponseHeadAppendCLEnd.contract B c7 m7 frame dst (ResponseHeadSources.clEnd status) (ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status)) xs7.length z8 g7_2 g7_23 hm ha cap7 g7_25 g7_19 vpos7 len8 (by have hh := bound8;simpa only [xs8,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) src8 hd sep8 p7
  let m8 := HttpPut.memory m7 dst 192#32 xs7.length z8
  have g8_2 : c8.get 2=frame+16#32 := (f8 2 (by decide) (by decide)).trans g7_2
  have g8_8 : c8.get 8=ResponseHeadSources.connection close := (f8 8 (by decide) (by decide)).trans g7_8
  have g8_9 : c8.get 9=ResponseHeadSources.clName status := (f8 9 (by decide) (by decide)).trans g7_9
  have g8_18 : c8.get 18=1#32 := (f8 18 (by decide) (by decide)).trans g7_18
  have g8_19 : c8.get 19=ResponseHeadSources.clEnd status := (f8 19 (by decide) (by decide)).trans g7_19
  have g8_20 : c8.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length := (f8 20 (by decide) (by decide)).trans g7_20
  have g8_21 : c8.get 21=1#32 := (f8 21 (by decide) (by decide)).trans g7_21
  have g8_23 : c8.get 23=dst := (f8 23 (by decide) (by decide)).trans g7_23
  have g8_24 : c8.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length := (f8 24 (by decide) (by decide)).trans g7_24
  have g8_25 : c8.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) := (f8 25 (by decide) (by decide)).trans g7_25
  have g8_26 : c8.get 26=BitVec.ofNat 32 ct.length := (f8 26 (by decide) (by decide)).trans g7_26
  have g8_27 : c8.get 27=ctptr := (f8 27 (by decide) (by decide)).trans g7_27
  have g8_22 : c8.get 22=1#32 := (f8 22 (by decide) (by decide)).trans g7_22
  have k8 : c8.sameCsr c := kk8.trans k7
  have e8 := ResponseHeadEnvelope.trans e7 (ResponseHeadEnvelope.effect ef8 (by decide) (by have hh := bound8;simpa only [xs8,List.length_append] using Nat.le_trans hh (by decide : 120≤192)))
  have x8 : Bytes.Span B m8 dst xs8 := OutputEffect.accumulates ef8 hd (by decide) (by have hh := bound8;simpa only [xs8,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) sep0 x7
  have vpos8 : c8.get 11=BitVec.ofNat 32 xs8.length := by simpa only [xs8,List.length_append] using v8_11
  have zn8 : z8.length≤19 := by
    dsimp [z8,ResponseHeadPlan.clEnd];split <;> decide +kernel
  have bn8 : 6+HttpPut.duration 192 xs7.length z8.length≤200 := by have hh := put_time xs7.length z8.length;omega
  have cap8 := (ResponseHeadEnvelope.word e8 hsep 40 (by decide) (by decide)).trans hcap
  obtain ⟨src9,sep9,len9⟩ := ResponseHeadSources.connection_data m8 dst close hd
  have close8 := (ResponseHeadEnvelope.word e8 hsep 32 (by decide) (by decide)).trans hclose
  obtain ⟨c9,t9,p9,f9,kk9,v9_10,v9_11,ef9⟩ := ResponseHeadAppendConnection.contract B c8 m8 frame dst (ResponseHeadSources.connection close) (ResponseHeadBodyMath.boolWord close) xs8.length z9 g8_2 vpos8 g8_23 hm ha cap8 v8_10 g8_8 close8 len9 (by have hh := bound9;simpa only [xs9,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) src9 hd sep9 p8
  let m9 := HttpPut.memory m8 dst 192#32 xs8.length z9
  have g9_2 : c9.get 2=frame+16#32 := (f9 2 (by decide) (by decide)).trans g8_2
  have g9_8 : c9.get 8=ResponseHeadSources.connection close := (f9 8 (by decide) (by decide)).trans g8_8
  have g9_9 : c9.get 9=ResponseHeadSources.clName status := (f9 9 (by decide) (by decide)).trans g8_9
  have g9_18 : c9.get 18=1#32 := (f9 18 (by decide) (by decide)).trans g8_18
  have g9_19 : c9.get 19=ResponseHeadSources.clEnd status := (f9 19 (by decide) (by decide)).trans g8_19
  have g9_20 : c9.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length := (f9 20 (by decide) (by decide)).trans g8_20
  have g9_21 : c9.get 21=1#32 := (f9 21 (by decide) (by decide)).trans g8_21
  have g9_23 : c9.get 23=dst := (f9 23 (by decide) (by decide)).trans g8_23
  have g9_24 : c9.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length := (f9 24 (by decide) (by decide)).trans g8_24
  have g9_25 : c9.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) := (f9 25 (by decide) (by decide)).trans g8_25
  have g9_26 : c9.get 26=BitVec.ofNat 32 ct.length := (f9 26 (by decide) (by decide)).trans g8_26
  have g9_27 : c9.get 27=ctptr := (f9 27 (by decide) (by decide)).trans g8_27
  have g9_22 : c9.get 22=1#32 := (f9 22 (by decide) (by decide)).trans g8_22
  have k9 : c9.sameCsr c := kk9.trans k8
  have e9 := ResponseHeadEnvelope.trans e8 (ResponseHeadEnvelope.effect ef9 (by decide) (by have hh := bound9;simpa only [xs9,List.length_append] using Nat.le_trans hh (by decide : 120≤192)))
  have x9 : Bytes.Span B m9 dst xs9 := OutputEffect.accumulates ef9 hd (by decide) (by have hh := bound9;simpa only [xs9,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) sep0 x8
  have vpos9 : c9.get 11=BitVec.ofNat 32 xs9.length := by simpa only [xs9,List.length_append] using v9_11
  have zn9 : z9.length≤19 := by
    cases close <;> decide +kernel
  have bn9 : 11+HttpPut.duration 192 xs8.length z9.length≤200 := by have hh := put_time xs8.length z9.length;omega
  have cap9 := (ResponseHeadEnvelope.word e9 hsep 40 (by decide) (by decide)).trans hcap
  have src10 := ResponseHeadLiterals.span m9 0
  have sep10 := ResponseHeadLiterals.disjoint dst 192 hd 0
  obtain ⟨c10,t10,p10,f10,kk10,v10_10,v10_11,ef10⟩ := ResponseHeadAppendFinalCRLF.contract B c9 m9 frame dst (0#32) (0#32) xs9.length z10 g9_2 vpos9 g9_23 hm ha cap9 v9_10 (by rfl) (by have hh := bound10;simpa only [xs10,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) src10 hd sep10 p9
  let m10 := HttpPut.memory m9 dst 192#32 xs9.length z10
  have g10_2 : c10.get 2=frame+16#32 := (f10 2 (by decide) (by decide)).trans g9_2
  have g10_8 : c10.get 8=ResponseHeadSources.connection close := (f10 8 (by decide) (by decide)).trans g9_8
  have g10_9 : c10.get 9=ResponseHeadSources.clName status := (f10 9 (by decide) (by decide)).trans g9_9
  have g10_18 : c10.get 18=1#32 := (f10 18 (by decide) (by decide)).trans g9_18
  have g10_19 : c10.get 19=ResponseHeadSources.clEnd status := (f10 19 (by decide) (by decide)).trans g9_19
  have g10_20 : c10.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length := (f10 20 (by decide) (by decide)).trans g9_20
  have g10_21 : c10.get 21=1#32 := (f10 21 (by decide) (by decide)).trans g9_21
  have g10_23 : c10.get 23=dst := (f10 23 (by decide) (by decide)).trans g9_23
  have g10_24 : c10.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length := (f10 24 (by decide) (by decide)).trans g9_24
  have g10_25 : c10.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status) := (f10 25 (by decide) (by decide)).trans g9_25
  have g10_26 : c10.get 26=BitVec.ofNat 32 ct.length := (f10 26 (by decide) (by decide)).trans g9_26
  have g10_27 : c10.get 27=ctptr := (f10 27 (by decide) (by decide)).trans g9_27
  have g10_22 : c10.get 22=1#32 := (f10 22 (by decide) (by decide)).trans g9_22
  have k10 : c10.sameCsr c := kk10.trans k9
  have e10 := ResponseHeadEnvelope.trans e9 (ResponseHeadEnvelope.effect ef10 (by decide) (by have hh := bound10;simpa only [xs10,List.length_append] using Nat.le_trans hh (by decide : 120≤192)))
  have x10 : Bytes.Span B m10 dst xs10 := OutputEffect.accumulates ef10 hd (by decide) (by have hh := bound10;simpa only [xs10,List.length_append] using Nat.le_trans hh (by decide : 120≤192)) sep0 x9
  have vpos10 : c10.get 11=BitVec.ofNat 32 xs10.length := by simpa only [xs10,List.length_append] using v10_11
  have zn10 : z10.length≤19 := by
    decide +kernel
  have bn10 : 10+HttpPut.duration 192 xs9.length z10.length≤200 := by have hh := put_time xs9.length z10.length;omega
  have hall : xs10=ResponseHeadSpec.bytes status ct body close := eq10.trans (ResponseHeadPlan.all status ct body close)
  refine ⟨c10,n1+(10+HttpPut.duration 192 xs1.length z2.length)+(8+HttpPut.duration 192 xs2.length z3.length)+(9+HttpPut.duration 192 xs3.length z4.length)+(8+HttpPut.duration 192 xs4.length z5.length)+(9+HttpPut.duration 192 xs5.length z6.length)+n7+(6+HttpPut.duration 192 xs7.length z8.length)+(11+HttpPut.duration 192 xs8.length z9.length)+(10+HttpPut.duration 192 xs9.length z10.length),m10,by omega,(((((((((t1).trans t2).trans t3).trans t4).trans t5).trans t6).trans t7).trans t8).trans t9).trans t10,p10,g10_2,v10_10,?_,k10,?_,e10⟩
  · simpa only [hall] using vpos10
  · simpa only [hall] using x10
end E5R.Thermostat.ResponseHeadSuffix
