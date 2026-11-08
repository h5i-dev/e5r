import Projects.thermostat.ResponseHeadPrefixPart0
import Projects.thermostat.ResponseHeadPrefixPart1
import Projects.thermostat.ResponseHeadPrefixPart2
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ResponseHeadPrefix
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (frame dst ctptr body flag : Word) (status ctlen : Nat) :=
  ResponseHeadPrefixPart2.memory (ResponseHeadPrefixPart1.memory (ResponseHeadPrefixPart0.memory (ram) frame dst ctptr body flag status ctlen) frame dst ctptr body flag status ctlen) frame dst ctptr body flag status ctlen

/-- Actual status-line stores, saved argument cache and the real call to
    put_reason. The prefix is not replaced by a semantic printf summary. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame dst ctptr body flag : Word)
    (status ctlen : Nat) (hlo : 100≤status) (hhi : status≤599) (hct : ctlen≤16)
    (h2 : c.get 2=(frame+16#32)) (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=(BitVec.ofNat 32 status)) (h13 : c.get 13=ctptr) (h14 : c.get 14=(BitVec.ofNat 32 ctlen)) (h15 : c.get 15=body) (h16 : c.get 16=flag) (h17 : c.get 17=9#32)
    (hstack : Memory.Block B frame 96) (ha : frame.toNat%4=0) (hdst : Memory.Block B dst 192)
    (hp : c.pc=0x80003f26#32) :
    ∃ d, Quiet.Steps B img 62 ⟨c,ram⟩ ⟨d,memory ram frame dst ctptr body flag status ctlen⟩ ∧ d.pc=0x80003584#32 ∧
      d.get 5=13#32 ∧ d.get 6=(BitVec.ofNat 32 (48+(status/10)%10)) ∧ d.get 7=(((BitVec.ofNat 32 (status/100))) <<< 1) ∧ d.get 28=32#32 ∧ d.get 17=(BitVec.ofNat 32 (48+status%10)) ∧ d.get 27=ctptr ∧ d.get 26=(BitVec.ofNat 32 ctlen) ∧ d.get 13=(BitVec.ofNat 32 status) ∧ d.get 12=13#32 ∧ d.get 23=dst ∧ d.get 1=0x80003ffa#32 ∧
      (∀ r : Reg, r≠5 → r≠6 → r≠7 → r≠28 → r≠17 → r≠27 → r≠26 → r≠13 → r≠12 → r≠23 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let m1 := ResponseHeadPrefixPart0.memory ram frame dst ctptr body flag status ctlen
  obtain ⟨a1,t1,p1,v1_5,v1_6,v1_7,v1_28,v1_17,f1,k1⟩ := ResponseHeadPrefixPart0.contract B c ram frame dst ctptr body flag status ctlen hlo hhi hct (h2) (h10) (h11) (h12) (h13) (h14) (h15) (h16) (h17) hstack ha hdst hp
  let m2 := ResponseHeadPrefixPart1.memory m1 frame dst ctptr body flag status ctlen
  obtain ⟨a2,t2,p2,v2_5,v2_6,v2_7,v2_17,f2,k2⟩ := ResponseHeadPrefixPart1.contract B a1 m1 frame dst ctptr body flag status ctlen hlo hhi hct ((f1 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h2)) (v1_5) (v1_6) (v1_7) ((f1 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h10)) ((f1 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h11)) ((f1 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h12)) ((f1 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h13)) ((f1 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h14)) ((f1 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h15)) ((f1 16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h16)) (v1_17) (v1_28) hstack ha hdst p1
  let m3 := ResponseHeadPrefixPart2.memory m2 frame dst ctptr body flag status ctlen
  obtain ⟨a3,t3,p3,v3_27,v3_26,v3_13,v3_12,v3_23,v3_1,f3,k3⟩ := ResponseHeadPrefixPart2.contract B a2 m2 frame dst ctptr body flag status ctlen hlo hhi hct ((f2 2 (by decide) (by decide) (by decide) (by decide)).trans ((f1 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h2))) (v2_5) (v2_6) (v2_7) ((f2 10 (by decide) (by decide) (by decide) (by decide)).trans ((f1 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h10))) ((f2 11 (by decide) (by decide) (by decide) (by decide)).trans ((f1 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h11))) ((f2 12 (by decide) (by decide) (by decide) (by decide)).trans ((f1 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h12))) ((f2 13 (by decide) (by decide) (by decide) (by decide)).trans ((f1 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h13))) ((f2 14 (by decide) (by decide) (by decide) (by decide)).trans ((f1 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h14))) ((f2 15 (by decide) (by decide) (by decide) (by decide)).trans ((f1 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h15))) ((f2 16 (by decide) (by decide) (by decide) (by decide)).trans ((f1 16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h16))) (v2_17) ((f2 28 (by decide) (by decide) (by decide) (by decide)).trans (v1_28)) hstack ha hdst p2
  refine ⟨a3,?_,p3,((f3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (v2_5)),((f3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (v2_6)),((f3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (v2_7)),((f3 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((f2 28 (by decide) (by decide) (by decide) (by decide)).trans (v1_28))),((f3 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (v2_17)),(v3_27),(v3_26),(v3_13),(v3_12),(v3_23),(v3_1),?_, k3.trans (k2.trans (k1))⟩
  · have tt := ((t1).trans t2).trans t3
    simpa only [memory,m1,m2,m3] using tt
  · intro r h5 h6 h7 h28 h17 h27 h26 h13 h12 h23 h1
    exact (f3 r h27 h26 h13 h12 h23 h1).trans ((f2 r h5 h6 h7 h17).trans ((f1 r h5 h6 h7 h28 h17)))
end E5R.Thermostat.ResponseHeadPrefix
