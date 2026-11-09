import Projects.thermostat.HttpReason431
import Projects.thermostat.ReasonBoardHttpReason431Part0
import Projects.thermostat.ReasonBoardHttpReason431Part1
import Projects.thermostat.ReasonBoardHttpReason431Part2
import Projects.thermostat.ReasonBoardHttpReason431Part3
import Projects.thermostat.ReasonBoardHttpReason431Part4
import Projects.thermostat.ReasonBoardHttpReason431Part5
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReasonBoardHttpReason431
open E5R E5R.Thermostat HttpReason431
abbrev B := StackBoard.board

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word) (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=13#32) (h13 : c.get 13=431#32) (hm : Memory.Block B dst 192)
    (hp : c.pc=0x80003584#32) :
    ∃ d, Quiet.Steps B img 178 ⟨c,ram⟩ ⟨d,memory ram dst⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      d.get 14=(dst+44#32) ∧ d.get 15=431#32 ∧ d.get 10=1#32 ∧ d.get 11=44#32 ∧ d.get 13=101#32 ∧ d.get 12=44#32 ∧ (∀ r : Reg, r≠14 → r≠15 → r≠10 → r≠11 → r≠13 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by

  let r1 := HttpReason431Part0.memory ram dst
  obtain ⟨a1,t1,p1,h1_14,h1_15,h1_10,h1_11,h1_13,f1,k1⟩ := ReasonBoardHttpReason431Part0.contract c ram dst (h10) (h11) (h12) (h13) hm hp
  let r2 := HttpReason431Part1.memory r1 dst
  obtain ⟨a2,t2,p2,h2_14,h2_11,h2_13,f2,k2⟩ := ReasonBoardHttpReason431Part1.contract a1 r1 dst (h1_10) (h1_11) ((f1 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h12)) (h1_13) (h1_14) (h1_15) hm p1
  let r3 := HttpReason431Part2.memory r2 dst
  obtain ⟨a3,t3,p3,h3_14,h3_11,h3_13,f3,k3⟩ := ReasonBoardHttpReason431Part2.contract a2 r2 dst ((f2 10 (by decide) (by decide) (by decide)).trans (h1_10)) (h2_11) ((f2 12 (by decide) (by decide) (by decide)).trans ((f1 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h12))) (h2_13) (h2_14) ((f2 15 (by decide) (by decide) (by decide)).trans (h1_15)) hm p2
  let r4 := HttpReason431Part3.memory r3 dst
  obtain ⟨a4,t4,p4,h4_14,h4_11,h4_13,f4,k4⟩ := ReasonBoardHttpReason431Part3.contract a3 r3 dst ((f3 10 (by decide) (by decide) (by decide)).trans ((f2 10 (by decide) (by decide) (by decide)).trans (h1_10))) (h3_11) ((f3 12 (by decide) (by decide) (by decide)).trans ((f2 12 (by decide) (by decide) (by decide)).trans ((f1 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h12)))) (h3_13) (h3_14) ((f3 15 (by decide) (by decide) (by decide)).trans ((f2 15 (by decide) (by decide) (by decide)).trans (h1_15))) hm p3
  let r5 := HttpReason431Part4.memory r4 dst
  obtain ⟨a5,t5,p5,h5_14,h5_11,h5_13,f5,k5⟩ := ReasonBoardHttpReason431Part4.contract a4 r4 dst ((f4 10 (by decide) (by decide) (by decide)).trans ((f3 10 (by decide) (by decide) (by decide)).trans ((f2 10 (by decide) (by decide) (by decide)).trans (h1_10)))) (h4_11) ((f4 12 (by decide) (by decide) (by decide)).trans ((f3 12 (by decide) (by decide) (by decide)).trans ((f2 12 (by decide) (by decide) (by decide)).trans ((f1 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h12))))) (h4_13) (h4_14) ((f4 15 (by decide) (by decide) (by decide)).trans ((f3 15 (by decide) (by decide) (by decide)).trans ((f2 15 (by decide) (by decide) (by decide)).trans (h1_15)))) hm p4
  let r6 := HttpReason431Part5.memory r5 dst
  obtain ⟨a6,t6,p6,h6_14,h6_11,h6_13,h6_12,h6_10,f6,k6⟩ := ReasonBoardHttpReason431Part5.contract a5 r5 dst ((f5 10 (by decide) (by decide) (by decide)).trans ((f4 10 (by decide) (by decide) (by decide)).trans ((f3 10 (by decide) (by decide) (by decide)).trans ((f2 10 (by decide) (by decide) (by decide)).trans (h1_10))))) (h5_11) ((f5 12 (by decide) (by decide) (by decide)).trans ((f4 12 (by decide) (by decide) (by decide)).trans ((f3 12 (by decide) (by decide) (by decide)).trans ((f2 12 (by decide) (by decide) (by decide)).trans ((f1 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h12)))))) (h5_13) (h5_14) ((f5 15 (by decide) (by decide) (by decide)).trans ((f4 15 (by decide) (by decide) (by decide)).trans ((f3 15 (by decide) (by decide) (by decide)).trans ((f2 15 (by decide) (by decide) (by decide)).trans (h1_15))))) hm p5
  have tt := (((((t1).trans t2).trans t3).trans t4).trans t5).trans t6
  refine ⟨a6,?_,?_, (h6_14),((f6 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((f5 15 (by decide) (by decide) (by decide)).trans ((f4 15 (by decide) (by decide) (by decide)).trans ((f3 15 (by decide) (by decide) (by decide)).trans ((f2 15 (by decide) (by decide) (by decide)).trans (h1_15)))))),(h6_10),(h6_11),(h6_13),(h6_12),?_,?_⟩
  · simpa only [memory,HttpReason431Part0.memory,HttpReason431Part1.memory,HttpReason431Part2.memory,HttpReason431Part3.memory,HttpReason431Part4.memory,HttpReason431Part5.memory,r1,r2,r3,r4,r5,r6] using tt
  · rw [p6]
    rw [(f5 1 (by decide) (by decide) (by decide)).trans ((f4 1 (by decide) (by decide) (by decide)).trans ((f3 1 (by decide) (by decide) (by decide)).trans ((f2 1 (by decide) (by decide) (by decide)).trans ((f1 1 (by decide) (by decide) (by decide) (by decide) (by decide))))))]
  · intro r h14 h15 h10 h11 h13 h12
    exact (f6 r h14 h11 h13 h12 h10).trans ((f5 r h14 h11 h13).trans ((f4 r h14 h11 h13).trans ((f3 r h14 h11 h13).trans ((f2 r h14 h11 h13).trans ((f1 r h14 h15 h10 h11 h13))))))
  · exact k6.trans (k5.trans (k4.trans (k3.trans (k2.trans (k1)))))
end E5R.Thermostat.ReasonBoardHttpReason431
