import Projects.thermostat.HeadNameCase00
import Projects.thermostat.HeadNameCase01
import Projects.thermostat.HeadNameCase02
import Projects.thermostat.HeadNameCase03
import Projects.thermostat.HeadNameCase04
import Projects.thermostat.HeadNameCase05
import Projects.thermostat.HeadNameCase06
import Projects.thermostat.HeadNameCase07
import Projects.thermostat.HeadNameCase08
import Projects.thermostat.HeadNameCase09
import Projects.thermostat.HeadNameCase10
import Projects.thermostat.HeadNameCase11
import Projects.thermostat.HeadNameCase12
import Projects.thermostat.HeadNameCase13
import Projects.thermostat.HeadNameCase14
import Projects.thermostat.HeadNameFlow
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.HeadNameClass
open E5R E5R.Thermostat HttpRequestSpec

structure Constants (c : Core) : Prop where
  x5 : c.get 5=33#32
  x6 : c.get 6=48#32
  x7 : c.get 7=14#32
  x28 : c.get 28=58#32
  x27 : c.get 27=91#32

/-- Actual header-name classification, including the last-name-byte guard.
    Colon candidates are checked separately against the exact colon value. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp last count : Word) (b : BitVec 8)
    (hp : c.pc=0x80002ff8#32) (h30 : c.get 30=BitVec.ofNat 32 b.toNat)
    (h15 : c.get 15=last) (h14 : c.get 14=count) (h2 : c.get 2=sp) (hc : Constants c)
    (hmask : ramRead ram (sp+32#32) .w=9409#32) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    ∃ n d, 1≤n ∧ n≤17 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if 58≤b.toNat ∧ b.toNat<65 then 0x80003056#32 else if isTchar b.toNat ∧ taken .eq last count=false then 0x80002fe0#32 else 0x8000342c#32) ∧
      (d.pc=0x80003056#32 → d.get 30=BitVec.ofNat 32 b.toNat) ∧
      (∀ r : Reg, r≠30 → r≠19 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let v := BitVec.ofNat 32 b.toNat
  cases hb0 : taken .ltu (v) (33#32) with
  | false =>
    cases hb1 : taken .geu (v) (48#32) with
    | false =>
      cases hb2 : taken .geu (alu .and (alu .add (v) (0xffffffde#32)) (255#32)) (14#32) with
      | false =>
        cases hb3 : taken .eq (last) (count) with
        | false =>
          cases hb4 : taken .eq (alu .and (alu .srl (9409#32) (alu .add (v) (0xffffffde#32))) (1#32)) ((0 : Word)) with
          | false =>
            obtain ⟨d,trace,pc,out30,out19,out12,frame,csr⟩ := HeadNameCase00.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hb4 hp
            have flow : HeadNameFlow.flow b (taken .eq last count)=0x8000342c#32 := by
              simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,hb4,Bool.false_eq_true,ite_true,ite_false]
            refine ⟨11,d,by decide,by decide,trace,?_,?_,?_,csr⟩
            simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3,hb4] using pc.trans flow.symm
            · intro colon
              exact False.elim ((by decide : 0x8000342c#32≠0x80003056#32) (pc.symm.trans colon))
            · intro r h30 h19 h12
              exact frame r h30 h19 h12
          | true =>
            obtain ⟨d,trace,pc,out30,out19,out12,frame,csr⟩ := HeadNameCase01.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hb4 hp
            have flow : HeadNameFlow.flow b (taken .eq last count)=0x80002fe0#32 := by
              simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,hb4,Bool.false_eq_true,ite_true,ite_false]
            refine ⟨10,d,by decide,by decide,trace,?_,?_,?_,csr⟩
            simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3,hb4] using pc.trans flow.symm
            · intro colon
              exact False.elim ((by decide : 0x80002fe0#32≠0x80003056#32) (pc.symm.trans colon))
            · intro r h30 h19 h12
              exact frame r h30 h19 h12
        | true =>
          obtain ⟨d,trace,pc,out30,out19,frame,csr⟩ := HeadNameCase02.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hp
          have flow : HeadNameFlow.flow b (taken .eq last count)=0x8000342c#32 := by
            simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,Bool.false_eq_true,ite_true,ite_false]
          refine ⟨6,d,by decide,by decide,trace,?_,?_,?_,csr⟩
          simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3] using pc.trans flow.symm
          · intro colon
            exact False.elim ((by decide : 0x8000342c#32≠0x80003056#32) (pc.symm.trans colon))
          · intro r h30 h19 h12
            exact frame r h30 h19
      | true =>
        cases hb3 : taken .eq (last) (count) with
        | false =>
          obtain ⟨d,trace,pc,out30,out19,frame,csr⟩ := HeadNameCase03.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hp
          have flow : HeadNameFlow.flow b (taken .eq last count)=0x80002fe0#32 := by
            simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,Bool.false_eq_true,ite_true,ite_false]
          refine ⟨6,d,by decide,by decide,trace,?_,?_,?_,csr⟩
          simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3] using pc.trans flow.symm
          · intro colon
            exact False.elim ((by decide : 0x80002fe0#32≠0x80003056#32) (pc.symm.trans colon))
          · intro r h30 h19 h12
            exact frame r h30 h19
        | true =>
          obtain ⟨d,trace,pc,out30,out19,frame,csr⟩ := HeadNameCase04.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hp
          have flow : HeadNameFlow.flow b (taken .eq last count)=0x8000342c#32 := by
            simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,Bool.false_eq_true,ite_true,ite_false]
          refine ⟨6,d,by decide,by decide,trace,?_,?_,?_,csr⟩
          simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3] using pc.trans flow.symm
          · intro colon
            exact False.elim ((by decide : 0x8000342c#32≠0x80003056#32) (pc.symm.trans colon))
          · intro r h30 h19 h12
            exact frame r h30 h19
    | true =>
      cases hb2 : taken .ltu (v) (58#32) with
      | false =>
        cases hb3 : taken .ltu (v) (alu .add ((0 : Word)) (65#32)) with
        | false =>
          cases hb4 : taken .ltu (v) (91#32) with
          | false =>
            cases hb5 : taken .ltu (v) (alu .add ((0 : Word)) (94#32)) with
            | false =>
              cases hb6 : taken .eq (last) (count) with
              | false =>
                cases hb7 : taken .eq (alu .and (alu .xor (alu .sltu (v) (123#32)) (0xffffffff#32)) (alu .sltu ((0 : Word)) (alu .add (alu .and (v) (253#32)) (0xffffff84#32)))) ((0 : Word)) with
                | false =>
                  obtain ⟨d,trace,pc,out12,out19,out30,frame,csr⟩ := HeadNameCase05.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hp
                  have flow : HeadNameFlow.flow b (taken .eq last count)=0x8000342c#32 := by
                    simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,hb4,hb5,hb6,hb7,Bool.false_eq_true,ite_true,ite_false]
                  refine ⟨17,d,by decide,by decide,trace,?_,?_,?_,csr⟩
                  simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3,hb4,hb5,hb6,hb7] using pc.trans flow.symm
                  · intro colon
                    exact False.elim ((by decide : 0x8000342c#32≠0x80003056#32) (pc.symm.trans colon))
                  · intro r h30 h19 h12
                    exact frame r h12 h19 h30
                | true =>
                  obtain ⟨d,trace,pc,out12,out19,out30,frame,csr⟩ := HeadNameCase06.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hp
                  have flow : HeadNameFlow.flow b (taken .eq last count)=0x80002fe0#32 := by
                    simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,hb4,hb5,hb6,hb7,Bool.false_eq_true,ite_true,ite_false]
                  refine ⟨16,d,by decide,by decide,trace,?_,?_,?_,csr⟩
                  simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3,hb4,hb5,hb6,hb7] using pc.trans flow.symm
                  · intro colon
                    exact False.elim ((by decide : 0x80002fe0#32≠0x80003056#32) (pc.symm.trans colon))
                  · intro r h30 h19 h12
                    exact frame r h12 h19 h30
              | true =>
                obtain ⟨d,trace,pc,out12,frame,csr⟩ := HeadNameCase07.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hb4 hb5 hb6 hp
                have flow : HeadNameFlow.flow b (taken .eq last count)=0x8000342c#32 := by
                  simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,hb4,hb5,hb6,Bool.false_eq_true,ite_true,ite_false]
                refine ⟨9,d,by decide,by decide,trace,?_,?_,?_,csr⟩
                simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3,hb4,hb5,hb6] using pc.trans flow.symm
                · intro colon
                  exact False.elim ((by decide : 0x8000342c#32≠0x80003056#32) (pc.symm.trans colon))
                · intro r h30 h19 h12
                  exact frame r h12
            | true =>
              obtain ⟨d,trace,pc,out12,frame,csr⟩ := HeadNameCase08.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hb4 hb5 hp
              have flow : HeadNameFlow.flow b (taken .eq last count)=0x8000342c#32 := by
                simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,hb4,hb5,Bool.false_eq_true,ite_true,ite_false]
              refine ⟨8,d,by decide,by decide,trace,?_,?_,?_,csr⟩
              simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3,hb4,hb5] using pc.trans flow.symm
              · intro colon
                exact False.elim ((by decide : 0x8000342c#32≠0x80003056#32) (pc.symm.trans colon))
              · intro r h30 h19 h12
                exact frame r h12
          | true =>
            cases hb5 : taken .eq (last) (count) with
            | false =>
              obtain ⟨d,trace,pc,out12,frame,csr⟩ := HeadNameCase09.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hb4 hb5 hp
              have flow : HeadNameFlow.flow b (taken .eq last count)=0x80002fe0#32 := by
                simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,hb4,hb5,Bool.false_eq_true,ite_true,ite_false]
              refine ⟨7,d,by decide,by decide,trace,?_,?_,?_,csr⟩
              simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3,hb4,hb5] using pc.trans flow.symm
              · intro colon
                exact False.elim ((by decide : 0x80002fe0#32≠0x80003056#32) (pc.symm.trans colon))
              · intro r h30 h19 h12
                exact frame r h12
            | true =>
              obtain ⟨d,trace,pc,out12,frame,csr⟩ := HeadNameCase10.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hb4 hb5 hp
              have flow : HeadNameFlow.flow b (taken .eq last count)=0x8000342c#32 := by
                simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,hb4,hb5,Bool.false_eq_true,ite_true,ite_false]
              refine ⟨7,d,by decide,by decide,trace,?_,?_,?_,csr⟩
              simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3,hb4,hb5] using pc.trans flow.symm
              · intro colon
                exact False.elim ((by decide : 0x8000342c#32≠0x80003056#32) (pc.symm.trans colon))
              · intro r h30 h19 h12
                exact frame r h12
        | true =>
          obtain ⟨d,trace,pc,out12,frame,csr⟩ := HeadNameCase11.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hp
          have flow : HeadNameFlow.flow b (taken .eq last count)=0x80003056#32 := by
            simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,Bool.false_eq_true,ite_true,ite_false]
          refine ⟨5,d,by decide,by decide,trace,?_,?_,?_,csr⟩
          simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3] using pc.trans flow.symm
          · intro colon
            exact (frame 30 (by decide)).trans h30
          · intro r h30 h19 h12
            exact frame r h12
      | true =>
        cases hb3 : taken .eq (last) (count) with
        | false =>
          obtain ⟨d,trace,pc,frame,csr⟩ := HeadNameCase12.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hp
          have flow : HeadNameFlow.flow b (taken .eq last count)=0x80002fe0#32 := by
            simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,Bool.false_eq_true,ite_true,ite_false]
          refine ⟨4,d,by decide,by decide,trace,?_,?_,?_,csr⟩
          simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3] using pc.trans flow.symm
          · intro colon
            exact False.elim ((by decide : 0x80002fe0#32≠0x80003056#32) (pc.symm.trans colon))
          · intro r h30 h19 h12
            exact frame r 
        | true =>
          obtain ⟨d,trace,pc,frame,csr⟩ := HeadNameCase13.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hb1 hb2 hb3 hp
          have flow : HeadNameFlow.flow b (taken .eq last count)=0x8000342c#32 := by
            simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,Bool.false_eq_true,ite_true,ite_false]
          refine ⟨4,d,by decide,by decide,trace,?_,?_,?_,csr⟩
          simpa only [HeadNameFlow.byte_classes,hb0,hb1,hb2,hb3] using pc.trans flow.symm
          · intro colon
            exact False.elim ((by decide : 0x8000342c#32≠0x80003056#32) (pc.symm.trans colon))
          · intro r h30 h19 h12
            exact frame r 
  | true =>
    obtain ⟨d,trace,pc,frame,csr⟩ := HeadNameCase14.contract B c ram v last count sp hc.x5 hc.x6 hc.x7 hc.x28 hc.x27 h30 h15 h14 h2 hmask stack ha hb0 hp
    have flow : HeadNameFlow.flow b (taken .eq last count)=0x8000342c#32 := by
      simp only [HeadNameFlow.flow,HeadNameFlow.high,HeadNameFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨1,d,by decide,by decide,trace,?_,?_,?_,csr⟩
    simpa only [HeadNameFlow.byte_classes,hb0] using pc.trans flow.symm
    · intro colon
      exact False.elim ((by decide : 0x8000342c#32≠0x80003056#32) (pc.symm.trans colon))
    · intro r h30 h19 h12
      exact frame r 

theorem preserve {c d} (h : Constants c)
    (frame : ∀ r : Reg, r≠30 → r≠19 → r≠12 → d.get r=c.get r) : Constants d := by
  exact ⟨(frame 5 (by decide) (by decide) (by decide)).trans h.x5,
    (frame 6 (by decide) (by decide) (by decide)).trans h.x6,
    (frame 7 (by decide) (by decide) (by decide)).trans h.x7,
    (frame 28 (by decide) (by decide) (by decide)).trans h.x28,
    (frame 27 (by decide) (by decide) (by decide)).trans h.x27⟩
end E5R.Thermostat.HeadNameClass
