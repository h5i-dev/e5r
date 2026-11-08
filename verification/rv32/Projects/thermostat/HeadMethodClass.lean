import Projects.thermostat.HeadMethodCase00
import Projects.thermostat.HeadMethodCase01
import Projects.thermostat.HeadMethodCase02
import Projects.thermostat.HeadMethodCase03
import Projects.thermostat.HeadMethodCase04
import Projects.thermostat.HeadMethodCase05
import Projects.thermostat.HeadMethodCase06
import Projects.thermostat.HeadMethodCase07
import Projects.thermostat.HeadMethodCase08
import Projects.thermostat.HeadMethodCase09
import Projects.thermostat.HeadMethodFlow
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.HeadMethodClass
open E5R E5R.Thermostat HttpRequestSpec

structure Constants (c : Core) : Prop where
  x5 : c.get 5=9409#32
  x6 : c.get 6=33#32
  x7 : c.get 7=48#32
  x8 : c.get 8=91#32
  x18 : c.get 18=94#32
  x29 : c.get 29=14#32
  x30 : c.get 30=58#32
  x31 : c.get 31=65#32

/-- Every byte takes one of the ten real instruction paths and reaches the
    endpoint selected by the independent tchar specification. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc=0x80002d06#32) (h19 : c.get 19=BitVec.ofNat 32 b.toNat) (hc : Constants c) :
    ∃ n d, 1≤n ∧ n≤13 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if b.toNat<33 then 0x80002da2#32 else if isTchar b.toNat then 0x80002cf4#32 else 0x80002efc#32) ∧
      (b.toNat<33 → d.get 19=BitVec.ofNat 32 b.toNat ∧ d.get 28=c.get 28) ∧
      (∀ r : Reg, r≠19 → r≠28 → d.get r=c.get r) ∧ d.sameCsr c := by
  let v := BitVec.ofNat 32 b.toNat
  cases hb0 : taken .ltu (v) (33#32) with
  | false =>
    cases hb1 : taken .geu (v) (48#32) with
    | false =>
      cases hb2 : taken .geu (alu .and (alu .add (v) (0xffffffde#32)) (255#32)) (14#32) with
      | false =>
        cases hb3 : taken .eq (alu .and (alu .srl (9409#32) (alu .add (v) (0xffffffde#32))) (1#32)) ((0 : Word)) with
        | false =>
          obtain ⟨d,trace,pc,out28,out19,frame,csr⟩ := HeadMethodCase03.contract B c ram v hc.x5 hc.x6 hc.x7 hc.x8 hc.x18 hc.x29 hc.x30 hc.x31 h19 hb0 hb1 hb2 hb3 hp
          have flow : HeadMethodFlow.flow b=0x80002efc#32 := by
            simp only [HeadMethodFlow.flow,HeadMethodFlow.high,HeadMethodFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,Bool.false_eq_true,ite_true,ite_false]
          refine ⟨9,d,by decide,by decide,trace,?_,?_,?_,csr⟩
          · simpa only [HeadMethodFlow.byte_classes] using pc.trans flow.symm
          · intro small
            have contradiction : decide (b.toNat<33)=false := by
              exact (HeadMethodFlow.lt33 b).symm.trans hb0
            rw [show decide (b.toNat<33)=true from decide_eq_true small] at contradiction
            contradiction
          · intro r h19 h28
            exact frame r h28 h19
        | true =>
          obtain ⟨d,trace,pc,out28,out19,frame,csr⟩ := HeadMethodCase02.contract B c ram v hc.x5 hc.x6 hc.x7 hc.x8 hc.x18 hc.x29 hc.x30 hc.x31 h19 hb0 hb1 hb2 hb3 hp
          have flow : HeadMethodFlow.flow b=0x80002cf4#32 := by
            simp only [HeadMethodFlow.flow,HeadMethodFlow.high,HeadMethodFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,Bool.false_eq_true,ite_true,ite_false]
          refine ⟨8,d,by decide,by decide,trace,?_,?_,?_,csr⟩
          · simpa only [HeadMethodFlow.byte_classes] using pc.trans flow.symm
          · intro small
            have contradiction : decide (b.toNat<33)=false := by
              exact (HeadMethodFlow.lt33 b).symm.trans hb0
            rw [show decide (b.toNat<33)=true from decide_eq_true small] at contradiction
            contradiction
          · intro r h19 h28
            exact frame r h28 h19
      | true =>
        obtain ⟨d,trace,pc,out28,out19,frame,csr⟩ := HeadMethodCase01.contract B c ram v hc.x5 hc.x6 hc.x7 hc.x8 hc.x18 hc.x29 hc.x30 hc.x31 h19 hb0 hb1 hb2 hp
        have flow : HeadMethodFlow.flow b=0x80002cf4#32 := by
          simp only [HeadMethodFlow.flow,HeadMethodFlow.high,HeadMethodFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,Bool.false_eq_true,ite_true,ite_false]
        refine ⟨5,d,by decide,by decide,trace,?_,?_,?_,csr⟩
        · simpa only [HeadMethodFlow.byte_classes] using pc.trans flow.symm
        · intro small
          have contradiction : decide (b.toNat<33)=false := by
            exact (HeadMethodFlow.lt33 b).symm.trans hb0
          rw [show decide (b.toNat<33)=true from decide_eq_true small] at contradiction
          contradiction
        · intro r h19 h28
          exact frame r h28 h19
    | true =>
      cases hb2 : taken .ltu (v) (58#32) with
      | false =>
        cases hb3 : taken .ltu (v) (65#32) with
        | false =>
          cases hb4 : taken .ltu (v) (91#32) with
          | false =>
            cases hb5 : taken .ltu (v) (94#32) with
            | false =>
              cases hb6 : taken .ne (alu .or (alu .sltu (v) (123#32)) (alu .sltu (alu .add (alu .and (v) (253#32)) (0xffffff84#32)) (1#32))) ((0 : Word)) with
              | false =>
                obtain ⟨d,trace,pc,out28,out19,frame,csr⟩ := HeadMethodCase09.contract B c ram v hc.x5 hc.x6 hc.x7 hc.x8 hc.x18 hc.x29 hc.x30 hc.x31 h19 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hp
                have flow : HeadMethodFlow.flow b=0x80002efc#32 := by
                  simp only [HeadMethodFlow.flow,HeadMethodFlow.high,HeadMethodFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,hb4,hb5,hb6,Bool.false_eq_true,ite_true,ite_false]
                refine ⟨13,d,by decide,by decide,trace,?_,?_,?_,csr⟩
                · simpa only [HeadMethodFlow.byte_classes] using pc.trans flow.symm
                · intro small
                  have contradiction : decide (b.toNat<33)=false := by
                    exact (HeadMethodFlow.lt33 b).symm.trans hb0
                  rw [show decide (b.toNat<33)=true from decide_eq_true small] at contradiction
                  contradiction
                · intro r h19 h28
                  exact frame r h28 h19
              | true =>
                obtain ⟨d,trace,pc,out28,out19,frame,csr⟩ := HeadMethodCase08.contract B c ram v hc.x5 hc.x6 hc.x7 hc.x8 hc.x18 hc.x29 hc.x30 hc.x31 h19 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hp
                have flow : HeadMethodFlow.flow b=0x80002cf4#32 := by
                  simp only [HeadMethodFlow.flow,HeadMethodFlow.high,HeadMethodFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,hb4,hb5,hb6,Bool.false_eq_true,ite_true,ite_false]
                refine ⟨12,d,by decide,by decide,trace,?_,?_,?_,csr⟩
                · simpa only [HeadMethodFlow.byte_classes] using pc.trans flow.symm
                · intro small
                  have contradiction : decide (b.toNat<33)=false := by
                    exact (HeadMethodFlow.lt33 b).symm.trans hb0
                  rw [show decide (b.toNat<33)=true from decide_eq_true small] at contradiction
                  contradiction
                · intro r h19 h28
                  exact frame r h28 h19
            | true =>
              obtain ⟨d,trace,pc,frame,csr⟩ := HeadMethodCase07.contract B c ram v hc.x5 hc.x6 hc.x7 hc.x8 hc.x18 hc.x29 hc.x30 hc.x31 h19 hb0 hb1 hb2 hb3 hb4 hb5 hp
              have flow : HeadMethodFlow.flow b=0x80002efc#32 := by
                simp only [HeadMethodFlow.flow,HeadMethodFlow.high,HeadMethodFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,hb4,hb5,Bool.false_eq_true,ite_true,ite_false]
              refine ⟨6,d,by decide,by decide,trace,?_,?_,?_,csr⟩
              · simpa only [HeadMethodFlow.byte_classes] using pc.trans flow.symm
              · intro small
                have contradiction : decide (b.toNat<33)=false := by
                  exact (HeadMethodFlow.lt33 b).symm.trans hb0
                rw [show decide (b.toNat<33)=true from decide_eq_true small] at contradiction
                contradiction
              · intro r h19 h28
                exact frame r
          | true =>
            obtain ⟨d,trace,pc,frame,csr⟩ := HeadMethodCase06.contract B c ram v hc.x5 hc.x6 hc.x7 hc.x8 hc.x18 hc.x29 hc.x30 hc.x31 h19 hb0 hb1 hb2 hb3 hb4 hp
            have flow : HeadMethodFlow.flow b=0x80002cf4#32 := by
              simp only [HeadMethodFlow.flow,HeadMethodFlow.high,HeadMethodFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,hb4,Bool.false_eq_true,ite_true,ite_false]
            refine ⟨5,d,by decide,by decide,trace,?_,?_,?_,csr⟩
            · simpa only [HeadMethodFlow.byte_classes] using pc.trans flow.symm
            · intro small
              have contradiction : decide (b.toNat<33)=false := by
                exact (HeadMethodFlow.lt33 b).symm.trans hb0
              rw [show decide (b.toNat<33)=true from decide_eq_true small] at contradiction
              contradiction
            · intro r h19 h28
              exact frame r
        | true =>
          obtain ⟨d,trace,pc,frame,csr⟩ := HeadMethodCase05.contract B c ram v hc.x5 hc.x6 hc.x7 hc.x8 hc.x18 hc.x29 hc.x30 hc.x31 h19 hb0 hb1 hb2 hb3 hp
          have flow : HeadMethodFlow.flow b=0x80002efc#32 := by
            simp only [HeadMethodFlow.flow,HeadMethodFlow.high,HeadMethodFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,hb3,Bool.false_eq_true,ite_true,ite_false]
          refine ⟨4,d,by decide,by decide,trace,?_,?_,?_,csr⟩
          · simpa only [HeadMethodFlow.byte_classes] using pc.trans flow.symm
          · intro small
            have contradiction : decide (b.toNat<33)=false := by
              exact (HeadMethodFlow.lt33 b).symm.trans hb0
            rw [show decide (b.toNat<33)=true from decide_eq_true small] at contradiction
            contradiction
          · intro r h19 h28
            exact frame r
      | true =>
        obtain ⟨d,trace,pc,frame,csr⟩ := HeadMethodCase04.contract B c ram v hc.x5 hc.x6 hc.x7 hc.x8 hc.x18 hc.x29 hc.x30 hc.x31 h19 hb0 hb1 hb2 hp
        have flow : HeadMethodFlow.flow b=0x80002cf4#32 := by
          simp only [HeadMethodFlow.flow,HeadMethodFlow.high,HeadMethodFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,hb1,hb2,Bool.false_eq_true,ite_true,ite_false]
        refine ⟨3,d,by decide,by decide,trace,?_,?_,?_,csr⟩
        · simpa only [HeadMethodFlow.byte_classes] using pc.trans flow.symm
        · intro small
          have contradiction : decide (b.toNat<33)=false := by
            exact (HeadMethodFlow.lt33 b).symm.trans hb0
          rw [show decide (b.toNat<33)=true from decide_eq_true small] at contradiction
          contradiction
        · intro r h19 h28
          exact frame r
  | true =>
    obtain ⟨d,trace,pc,frame,csr⟩ := HeadMethodCase00.contract B c ram v hc.x5 hc.x6 hc.x7 hc.x8 hc.x18 hc.x29 hc.x30 hc.x31 h19 hb0 hp
    have flow : HeadMethodFlow.flow b=0x80002da2#32 := by
      simp only [HeadMethodFlow.flow,HeadMethodFlow.high,HeadMethodFlow.low,←show v=BitVec.ofNat 32 b.toNat from rfl,hb0,Bool.false_eq_true,ite_true,ite_false]
    refine ⟨1,d,by decide,by decide,trace,?_,?_,?_,csr⟩
    · simpa only [HeadMethodFlow.byte_classes] using pc.trans flow.symm
    · intro small
      exact ⟨(frame 19).trans h19,frame 28⟩
    · intro r h19 h28
      exact frame r

theorem preserve_constants {c d} (h : Constants c)
    (frame : ∀ r : Reg, r≠19 → r≠28 → d.get r=c.get r) : Constants d := by
  exact ⟨(frame 5 (by decide) (by decide)).trans h.x5,
    (frame 6 (by decide) (by decide)).trans h.x6,
    (frame 7 (by decide) (by decide)).trans h.x7,
    (frame 8 (by decide) (by decide)).trans h.x8,
    (frame 18 (by decide) (by decide)).trans h.x18,
    (frame 29 (by decide) (by decide)).trans h.x29,
    (frame 30 (by decide) (by decide)).trans h.x30,
    (frame 31 (by decide) (by decide)).trans h.x31⟩

theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc=0x80002d06#32) (h19 : c.get 19=BitVec.ofNat 32 b.toNat) (hc : Constants c) (masked : c.mie_=false) :
    ∃ n d, 1≤n ∧ n≤13 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if b.toNat<33 then 0x80002da2#32 else if isTchar b.toNat then 0x80002cf4#32 else 0x80002efc#32) ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,hlo,hi,trace,pc,small,frame,csr⟩ := contract B c ram b hp h19 hc
  exact ⟨n,d,hlo,hi,Interrupt.close trace.det masked,pc,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩

theorem preserve_constants_except17 {c d} (h : Constants c)
    (frame : ∀ r : Reg, r≠17 → d.get r=c.get r) : Constants d := by
  exact ⟨(frame 5 (by decide)).trans h.x5,(frame 6 (by decide)).trans h.x6,
    (frame 7 (by decide)).trans h.x7,(frame 8 (by decide)).trans h.x8,
    (frame 18 (by decide)).trans h.x18,(frame 29 (by decide)).trans h.x29,
    (frame 30 (by decide)).trans h.x30,(frame 31 (by decide)).trans h.x31⟩
end E5R.Thermostat.HeadMethodClass
