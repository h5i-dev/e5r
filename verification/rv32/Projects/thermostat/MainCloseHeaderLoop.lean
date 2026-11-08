import Projects.thermostat.MainCloseField
import Projects.thermostat.MainCloseHeaderNext
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseHeaderLoop
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠10 → r≠11 → r≠13 → r≠14 → r≠15 → r≠22 → r≠23 → r≠24 → r≠25 → r≠26 → d.get r=c.get r

theorem Frame.trans {a b c : Core} (h : Frame a b) (k : Frame b c) : Frame a c :=
  fun r a b c d e f g i j l => (k r a b c d e f g i j l).trans (h r a b c d e f g i j l)

/-- All actual Request header entries, including duplicate Connection fields.
    Count and descriptor bounds come from Header.Pre; no desired close result
    is assumed. Stack/RAM are unchanged by this entire leaf loop. -/
theorem contract (B : Board) (ram : Word → BitVec 8) (rawPtr : Word) (raw : List (BitVec 8))
    (span : Bytes.Span B ram rawPtr raw) (limit : raw.length≤2048)
    (entries : List HeaderSpec.Entry) (cell : Word) (table : HeaderInput.Table B ram cell raw.length entries)
    (nonempty : entries≠[]) (c : Core) (hp : c.pc=0x8000247a#32)
    (h13 : c.get 13=cell) (h17 : c.get 17=cell+BitVec.ofNat 32 (16*entries.length))
    (h12 : c.get 12=BitVec.ofNat 32 raw.length) (h16 : c.get 16=rawPtr) (h5 : c.get 5=10#32)
    (names : MainCloseNameChain.Literals c) (values : MainCloseValueContext.Literals c) :
    ∃ n d, n≤(77+86*raw.length)*entries.length ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if MainCloseSpec.wantsClose raw entries then 0x800026bc#32 else 0x8000267c#32) ∧ Frame c d ∧ d.sameCsr c := by
  induction entries generalizing cell c with
  | nil => contradiction
  | cons e es ih =>
    obtain ⟨n,a,nb,sa,pa,ar,ac⟩ := MainCloseField.contract B c ram cell rawPtr raw e table.head span limit hp h13 h12 h16 h5 names values
    have fieldBound : (HeaderSpec.value raw e).length≤raw.length := by
      rw [HeaderInput.value_length table.head.bounds]
      have bounds := table.head.bounds
      unfold HeaderSpec.Bounds at bounds
      omega
    have ca : Frame c a := fun r n10 n11 _ n14 n15 n22 n23 n24 n25 n26 => ar r n10 n11 n14 n15 n22 n23 n24 n25 n26
    cases found : MainCloseSpec.field (HeaderSpec.name raw e) (HeaderSpec.value raw e) with
    | true =>
      refine ⟨n,a,by simp only [List.length_cons,Nat.mul_add,Nat.mul_one];omega,sa,?_,ca,ac⟩
      simpa only [MainCloseSpec.wantsClose,List.any_cons,found,Bool.true_or,ite_true] using pa
    | false =>
      have ap : a.pc=0x80002474#32 := by simpa only [found,Bool.false_eq_true,ite_false] using pa
      have a13 : a.get 13=cell := (ar _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13
      have a17 : a.get 17=cell+BitVec.ofNat 32 (16*(e::es).length) := (ar 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h17
      obtain ⟨b,sb,pb,b13,br,bc⟩ := MainCloseHeaderNext.contract B a ram cell (e::es).length (by simp) table.bounded ap a13 a17
      have cb : Frame c b := by
        intro r n10 n11 n13 n14 n15 n22 n23 n24 n25 n26
        exact (br r n13).trans (ca r n10 n11 n13 n14 n15 n22 n23 n24 n25 n26)
      cases es with
      | nil =>
        refine ⟨n+2,b,by simp only [List.length_cons,List.length_nil,Nat.mul_one];omega,sa.trans sb,?_,cb,bc.trans ac⟩
        simpa only [List.length_cons,List.length_nil,ite_true,MainCloseSpec.wantsClose,List.any_cons,List.any_nil,found,Bool.false_or,Bool.false_eq_true,ite_false] using pb
      | cons e' es' =>
        have lengthNe : (e::e'::es').length≠1 := by simp only [List.length_cons];omega
        have bp : b.pc=0x8000247a#32 := by simpa only [lengthNe,ite_false] using pb
        have b17 : b.get 17=(cell+16#32)+BitVec.ofNat 32 (16*(e'::es').length) := by
          rw [(br _ (by decide)).trans a17]
          simp only [List.length_cons,BitVec.add_assoc,←BitVec.ofNat_add]
          congr 2;omega
        have b12 : b.get 12=BitVec.ofNat 32 raw.length := (cb 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12
        have b16 : b.get 16=rawPtr := (cb 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16
        have b5 : b.get 5=10#32 := (cb 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h5
        have bnames : MainCloseNameChain.Literals b := ⟨(cb 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans names.c6,
(cb 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans names.c7,
(cb 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans names.c28,
(cb 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans names.c29,
(cb 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans names.c30,
(cb 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans names.c31⟩
        have bvalues : MainCloseValueContext.Literals b := ⟨⟨(cb 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans values.c6,(cb 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans values.c19,(cb 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans values.c7,(cb 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans values.c20⟩,(cb 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans values.c8,(cb 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans values.c9,(cb 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans values.c18,(cb 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans values.c21,(cb 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans values.c29⟩
        obtain ⟨m,d,mb,sd,pd,dr,dc⟩ := ih (cell+16#32) table.tail (by simp) b bp b13 b17 b12 b16 b5 bnames bvalues
        refine ⟨n+2+m,d,by simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at *;omega,(sa.trans sb).trans sd,?_,cb.trans dr,dc.trans (bc.trans ac)⟩
        have tailResult : MainCloseSpec.wantsClose raw (e::e'::es')=MainCloseSpec.wantsClose raw (e'::es') := by
          change (MainCloseSpec.field _ _ || MainCloseSpec.wantsClose raw (e'::es'))=_
          rw [found,Bool.false_or]
        rw [tailResult];exact pd
end E5R.Thermostat.MainCloseHeaderLoop
