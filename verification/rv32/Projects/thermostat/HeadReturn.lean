import Projects.thermostat.HeadSaved
import Projects.thermostat.HeadRestore
import Projects.thermostat.HeadRet
namespace E5R.Thermostat.HeadReturn
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word)
    (hp : c.pc=0x80002d6a#32) (h2 : c.get 2=sp) (hm : Memory.Block B sp 384) (ha : sp.toNat%4=0)
    (hs : HeadSaved.At ram sp saved) :
    ∃ d, Quiet.Steps B img 15 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=saved 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧
      HeadSaved.CoreAt d saved ∧
      (∀ r : Reg, r≠1 → r≠8 → r≠9 → r≠18 → r≠19 → r≠20 → r≠21 → r≠22 → r≠23 → r≠24 → r≠25 → r≠26 → r≠27 → r≠2 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,restore,pc,v1,v8,v9,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v2,frame,csr⟩ := HeadRestore.contract B c ram sp h2 hm ha hp
  obtain ⟨d,ret,pc2,frame2,csr2⟩ := HeadRet.contract B a ram pc
  refine ⟨d,restore.trans ret,?_,(frame2 2).trans v2,?_,?_,csr2.trans csr⟩
  · simpa only [v1,hs.x1] using pc2
  · exact ⟨(frame2 1).trans (v1.trans hs.x1),
      (frame2 8).trans (v8.trans hs.x8),
      (frame2 9).trans (v9.trans hs.x9),
      (frame2 18).trans (v18.trans hs.x18),
      (frame2 19).trans (v19.trans hs.x19),
      (frame2 20).trans (v20.trans hs.x20),
      (frame2 21).trans (v21.trans hs.x21),
      (frame2 22).trans (v22.trans hs.x22),
      (frame2 23).trans (v23.trans hs.x23),
      (frame2 24).trans (v24.trans hs.x24),
      (frame2 25).trans (v25.trans hs.x25),
      (frame2 26).trans (v26.trans hs.x26),
      (frame2 27).trans (v27.trans hs.x27)⟩
  · intro r h1 h8 h9 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h2
    exact (frame2 r).trans (frame r h1 h8 h9 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h2)
end E5R.Thermostat.HeadReturn
