import Projects.thermostat.HeadVersionCase00
import Projects.thermostat.HeadVersionCase01
import Projects.thermostat.HeadVersionCase02
import Projects.thermostat.HeadVersionCase03
import Projects.thermostat.HeadVersionCase04
import Projects.thermostat.HeadVersionCase05
import Projects.thermostat.HeadVersionCase06
import Projects.thermostat.HeadVersionFlow
namespace E5R.Thermostat.HeadVersionDigits
open E5R E5R.Thermostat HttpRequestSpec

/-- Every real version-digit path, classified by independent versionDigits.
    Rejects retain the actual status and result pointer; successes establish
    the minor-version and inverse flags used by header processing. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (sp pos base limits buf dst : Word) (major dot minor : BitVec 8)
    (hp : c.pc=0x80002eaa#32) (h2 : c.get 2=sp) (h7 : c.get 7=pos) (h6 : c.get 6=base)
    (h13 : c.get 13=limits) (h15 : c.get 15=400#32)
    (hm : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hbuf : ramRead ram (sp+44#32) .w=buf) (hdst : ramRead ram (sp+52#32) .w=dst)
    (hmmajor : B.inRam (buf+pos+7#32) 1=true) (hmajor : ram (buf+pos+7#32)=major)
    (hmdot : B.inRam (base+8#32) 1=true) (hdot : ram (base+8#32)=dot)
    (hmminor : B.inRam (base+9#32) 1=true) (hminor : ram (base+9#32)=minor) :
    let v := versionDigits major.toNat dot.toNat minor.toNat
    ∃ n d, 6≤n ∧ n≤25 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      (if v<2 then d.pc=0x80002f0e#32 ∧ d.get 8=BitVec.ofNat 32 v ∧ d.get 18=BitVec.ofNat 32 (1-v) ∧ d.get 20=limits
       else (d.pc=0x80002efa#32 ∨ d.pc=0x80002efc#32) ∧ d.get 15=(if v=3 then 400#32 else 505#32) ∧
         (d.pc=0x80002efc#32 → d.get 10=dst)) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → r≠20 → r≠8 → r≠18 → d.get r=c.get r) ∧ d.sameCsr c := by
  cases hb0 : HeadVersionFlow.badDigit major with
  | true =>
    obtain ⟨d,trace,pc,out10,out11,out12,frame,csr⟩ := HeadVersionCase00.contract B c ram sp pos base limits buf dst major dot minor h2 h7 h6 h13 h15 hm ha hbuf hdst hmmajor hmajor hmdot hdot hmminor hminor hb0 hp
    have flow : HeadVersionFlow.flow major dot minor=3 := by
      simp only [HeadVersionFlow.flow,hb0,Bool.false_eq_true,ite_false,ite_true]
    have classification : versionDigits major.toNat dot.toNat minor.toNat=3 := (HeadVersionFlow.classification major dot minor).symm.trans flow
    refine ⟨6,d,by decide,by decide,trace,?_,?_,csr⟩
    · simp only [classification]
      change (d.pc=0x80002efa#32 ∨ d.pc=0x80002efc#32) ∧ d.get 15=400#32 ∧ (d.pc=0x80002efc#32 → d.get 10=dst)
      refine ⟨Or.inl pc,?_,?_⟩
      · simpa only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add] using ((frame 15 (by decide) (by decide) (by decide)).trans h15)
      · intro wrong
        have ne : 0x80002efa#32≠0x80002efc#32 := by decide +kernel
        exact False.elim (ne (pc.symm.trans wrong))
    · intro r h10 h11 h12 h13 h14 h15 h20 h8 h18
      exact frame r h10 h11 h12
  | false =>
    cases hb1 : taken .ne (BitVec.ofNat 32 dot.toNat) 46#32 with
    | true =>
      obtain ⟨d,trace,pc,out10,out11,out12,frame,csr⟩ := HeadVersionCase01.contract B c ram sp pos base limits buf dst major dot minor h2 h7 h6 h13 h15 hm ha hbuf hdst hmmajor hmajor hmdot hdot hmminor hminor hb0 hb1 hp
      have flow : HeadVersionFlow.flow major dot minor=3 := by
        simp only [HeadVersionFlow.flow,hb0,hb1,Bool.false_eq_true,ite_false,ite_true]
      have classification : versionDigits major.toNat dot.toNat minor.toNat=3 := (HeadVersionFlow.classification major dot minor).symm.trans flow
      refine ⟨9,d,by decide,by decide,trace,?_,?_,csr⟩
      · simp only [classification]
        change (d.pc=0x80002efa#32 ∨ d.pc=0x80002efc#32) ∧ d.get 15=400#32 ∧ (d.pc=0x80002efc#32 → d.get 10=dst)
        refine ⟨Or.inl pc,?_,?_⟩
        · simpa only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add] using ((frame 15 (by decide) (by decide) (by decide)).trans h15)
        · intro wrong
          have ne : 0x80002efa#32≠0x80002efc#32 := by decide +kernel
          exact False.elim (ne (pc.symm.trans wrong))
      · intro r h10 h11 h12 h13 h14 h15 h20 h8 h18
        exact frame r h10 h11 h12
    | false =>
      cases hb2 : HeadVersionFlow.badDigit minor with
      | true =>
        obtain ⟨d,trace,pc,out10,out11,out12,out20,out13,out14,frame,csr⟩ := HeadVersionCase02.contract B c ram sp pos base limits buf dst major dot minor h2 h7 h6 h13 h15 hm ha hbuf hdst hmmajor hmajor hmdot hdot hmminor hminor hb0 hb1 hb2 hp
        have flow : HeadVersionFlow.flow major dot minor=3 := by
          simp only [HeadVersionFlow.flow,hb0,hb1,hb2,Bool.false_eq_true,ite_false,ite_true]
        have classification : versionDigits major.toNat dot.toNat minor.toNat=3 := (HeadVersionFlow.classification major dot minor).symm.trans flow
        refine ⟨15,d,by decide,by decide,trace,?_,?_,csr⟩
        · simp only [classification]
          change (d.pc=0x80002efa#32 ∨ d.pc=0x80002efc#32) ∧ d.get 15=400#32 ∧ (d.pc=0x80002efc#32 → d.get 10=dst)
          refine ⟨Or.inr pc,?_,?_⟩
          · simpa only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add] using ((frame 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h15)
          · intro _;exact out10
        · intro r h10 h11 h12 h13 h14 h15 h20 h8 h18
          exact frame r h10 h11 h12 h20 h13 h14
      | false =>
        cases hb3 : taken .ne (BitVec.ofNat 32 major.toNat) 49#32 with
        | true =>
          obtain ⟨d,trace,pc,out10,out11,out12,out20,out13,out14,out15,frame,csr⟩ := HeadVersionCase03.contract B c ram sp pos base limits buf dst major dot minor h2 h7 h6 h13 h15 hm ha hbuf hdst hmmajor hmajor hmdot hdot hmminor hminor hb0 hb1 hb2 hb3 hp
          have flow : HeadVersionFlow.flow major dot minor=2 := by
            simp only [HeadVersionFlow.flow,hb0,hb1,hb2,hb3,Bool.false_eq_true,ite_false,ite_true]
          have classification : versionDigits major.toNat dot.toNat minor.toNat=2 := (HeadVersionFlow.classification major dot minor).symm.trans flow
          refine ⟨18,d,by decide,by decide,trace,?_,?_,csr⟩
          · simp only [classification]
            change (d.pc=0x80002efa#32 ∨ d.pc=0x80002efc#32) ∧ d.get 15=505#32 ∧ (d.pc=0x80002efc#32 → d.get 10=dst)
            refine ⟨Or.inl pc,?_,?_⟩
            · simpa only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add] using out15
            · intro wrong
              have ne : 0x80002efa#32≠0x80002efc#32 := by decide +kernel
              exact False.elim (ne (pc.symm.trans wrong))
          · intro r h10 h11 h12 h13 h14 h15 h20 h8 h18
            exact frame r h10 h11 h12 h20 h13 h14 h15
        | false =>
          cases hb4 : taken .eq (BitVec.ofNat 32 minor.toNat) 49#32 with
          | true =>
            obtain ⟨d,trace,pc,out10,out11,out12,out20,out13,out14,out15,out18,out8,frame,csr⟩ := HeadVersionCase04.contract B c ram sp pos base limits buf dst major dot minor h2 h7 h6 h13 h15 hm ha hbuf hdst hmmajor hmajor hmdot hdot hmminor hminor hb0 hb1 hb2 hb3 hb4 hp
            have flow : HeadVersionFlow.flow major dot minor=1 := by
              simp only [HeadVersionFlow.flow,hb0,hb1,hb2,hb3,hb4,Bool.false_eq_true,ite_false,ite_true]
            have classification : versionDigits major.toNat dot.toNat minor.toNat=1 := (HeadVersionFlow.classification major dot minor).symm.trans flow
            refine ⟨21,d,by decide,by decide,trace,?_,?_,csr⟩
            · simp only [classification]
              change d.pc=0x80002f0e#32 ∧ d.get 8=1#32 ∧ d.get 18=0#32 ∧ d.get 20=limits
              refine ⟨pc,?_,?_,?_⟩
              · simpa only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add] using out8
              · simpa only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add] using out18
              · simpa only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add] using out20
            · intro r h10 h11 h12 h13 h14 h15 h20 h8 h18
              exact frame r h10 h11 h12 h20 h13 h14 h15 h18 h8
          | false =>
            cases hb5 : taken .ne (BitVec.ofNat 32 minor.toNat) 48#32 with
            | true =>
              obtain ⟨d,trace,pc,out10,out11,out12,out20,out13,out14,out15,frame,csr⟩ := HeadVersionCase05.contract B c ram sp pos base limits buf dst major dot minor h2 h7 h6 h13 h15 hm ha hbuf hdst hmmajor hmajor hmdot hdot hmminor hminor hb0 hb1 hb2 hb3 hb4 hb5 hp
              have flow : HeadVersionFlow.flow major dot minor=2 := by
                simp only [HeadVersionFlow.flow,hb0,hb1,hb2,hb3,hb4,hb5,Bool.false_eq_true,ite_false,ite_true]
              have classification : versionDigits major.toNat dot.toNat minor.toNat=2 := (HeadVersionFlow.classification major dot minor).symm.trans flow
              refine ⟨22,d,by decide,by decide,trace,?_,?_,csr⟩
              · simp only [classification]
                change (d.pc=0x80002efa#32 ∨ d.pc=0x80002efc#32) ∧ d.get 15=505#32 ∧ (d.pc=0x80002efc#32 → d.get 10=dst)
                refine ⟨Or.inr pc,?_,?_⟩
                · simpa only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add] using out15
                · intro _;exact out10
              · intro r h10 h11 h12 h13 h14 h15 h20 h8 h18
                exact frame r h10 h11 h12 h20 h13 h14 h15
            | false =>
              obtain ⟨d,trace,pc,out10,out11,out12,out20,out13,out14,out15,out8,out18,frame,csr⟩ := HeadVersionCase06.contract B c ram sp pos base limits buf dst major dot minor h2 h7 h6 h13 h15 hm ha hbuf hdst hmmajor hmajor hmdot hdot hmminor hminor hb0 hb1 hb2 hb3 hb4 hb5 hp
              have flow : HeadVersionFlow.flow major dot minor=0 := by
                simp only [HeadVersionFlow.flow,hb0,hb1,hb2,hb3,hb4,hb5,Bool.false_eq_true,ite_false,ite_true]
              have classification : versionDigits major.toNat dot.toNat minor.toNat=0 := (HeadVersionFlow.classification major dot minor).symm.trans flow
              refine ⟨25,d,by decide,by decide,trace,?_,?_,csr⟩
              · simp only [classification]
                change d.pc=0x80002f0e#32 ∧ d.get 8=0#32 ∧ d.get 18=1#32 ∧ d.get 20=limits
                refine ⟨pc,?_,?_,?_⟩
                · simpa only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add] using out8
                · simpa only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add] using out18
                · simpa only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add] using out20
              · intro r h10 h11 h12 h13 h14 h15 h20 h8 h18
                exact frame r h10 h11 h12 h20 h13 h14 h15 h8 h18
end E5R.Thermostat.HeadVersionDigits
