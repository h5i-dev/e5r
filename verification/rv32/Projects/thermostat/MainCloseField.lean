import Projects.thermostat.MainCloseFieldLayout
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseField
open E5R E5R.Thermostat

/-- One actual bounded Header entry, including all length/refusal branches.
    Its name and value bytes derive from the Request's raw slice. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (cell rawPtr : Word) (raw : List (BitVec 8)) (e : HeaderSpec.Entry)
    (stored : HeaderInput.Cell B ram cell raw.length e) (span : Bytes.Span B ram rawPtr raw)
    (limit : raw.length≤2048) (hp : c.pc=0x8000247a#32)
    (h13 : c.get 13=cell) (h12 : c.get 12=BitVec.ofNat 32 raw.length)
    (h16 : c.get 16=rawPtr) (h5 : c.get 5=10#32)
    (names : MainCloseNameChain.Literals c) (values : MainCloseValueContext.Literals c) :
    ∃ n d, n≤75+86*(HeaderSpec.value raw e).length ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if MainCloseSpec.field (HeaderSpec.name raw e) (HeaderSpec.value raw e) then 0x800026bc#32 else 0x80002474#32) ∧
      MainCloseValueContext.Frame c d ∧ d.sameCsr c := by
  have bounds := stored.bounds
  unfold HeaderSpec.Bounds at bounds
  obtain ⟨a,sa,pa,a15,a14,a10,a11,ar,ac⟩ := MainCloseHeaderBounds.contract B c ram cell raw.length e stored limit h13 h12 hp
  obtain ⟨k,b,kb,sb,pb,b15,br,bc⟩ := MainCloseFieldLayout.name B a ram rawPtr e.nameStart e.nameEnd bounds.1 (by omega)
    pa a14 a15 ((ar 16 (by decide) (by decide) (by decide) (by decide)).trans h16)
    ((ar 5 (by decide) (by decide) (by decide) (by decide)).trans h5)
  have ab : MainCloseValueContext.Frame c b := by
    intro r n10 n11 n14 n15 _ _ _ _ _
    exact (br r n14 n15).trans (ar r n15 n14 n10 n11)
  have bcsr := bc.trans ac
  by_cases length : e.nameEnd-e.nameStart=10
  · have bp : b.pc=0x8000249a#32 := by simpa only [length,ite_true] using pb
    obtain ⟨j,d,jb,sd,pd,dr,dc⟩ := MainCloseName.header B b ram rawPtr raw e span stored.bounds length bp (b15 length)
      ⟨(ab _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans names.c6,
       (ab _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans names.c7,
       (ab _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans names.c28,
       (ab _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans names.c29,
       (ab _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans names.c30,
       (ab _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans names.c31⟩
    have cd : MainCloseValueContext.Frame c d := by
      intro r n10 n11 n14 n15 n22 n23 n24 n25 n26
      exact (dr r n14 n15 n22).trans (ab r n10 n11 n14 n15 n22 n23 n24 n25 n26)
    have dc' := dc.trans bcsr
    cases matchesName : HeaderSpec.same (HeaderSpec.name raw e) (WireSpec.ascii "connection") with
    | false =>
      refine ⟨8+k+j,d,by omega,(sa.trans sb).trans sd,?_,cd,dc'⟩
      simpa only [MainCloseSpec.field,matchesName,Bool.false_and,Bool.false_eq_true,ite_false] using pd
    | true =>
      have dp : d.pc=0x80002574#32 := by simpa only [matchesName,ite_true] using pd
      have d10 : d.get 10=BitVec.ofNat 32 e.valueStart := (dr 10 (by decide) (by decide) (by decide)).trans ((br 10 (by decide) (by decide)).trans a10)
      have d11 : d.get 11=BitVec.ofNat 32 e.valueEnd := (dr 11 (by decide) (by decide) (by decide)).trans ((br 11 (by decide) (by decide)).trans a11)
      have d16 : d.get 16=rawPtr := (cd 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16
      obtain ⟨l,f,lb,sf,pf,registers,fr,fc⟩ := MainCloseFieldLayout.value B d ram rawPtr e.valueStart e.valueEnd bounds.2.2.1 (by omega) dp d10 d11 d16
      have cf : MainCloseValueContext.Frame c f := by
        intro r n10 n11 n14 n15 n22 n23 n24 n25 n26
        exact (fr r n14 n15 n22).trans (cd r n10 n11 n14 n15 n22 n23 n24 n25 n26)
      have fc' := fc.trans dc'
      have valueLength := HeaderInput.value_length stored.bounds
      by_cases empty : e.valueEnd-e.valueStart=0
      · have nil : HeaderSpec.value raw e=[] := List.eq_nil_of_length_eq_zero (valueLength.trans empty)
        refine ⟨8+k+j+l,f,by omega,((sa.trans sb).trans sd).trans sf,?_,cf,fc'⟩
        simpa only [MainCloseSpec.field,matchesName,Bool.true_and,nil,MainCloseSpec.hasClose,show (([] : List (BitVec 8)).splitOn 44#8).any (fun token => HeaderSpec.same (TrimMath.trim token) (WireSpec.ascii "close"))=false by decide +kernel,empty,ite_true,Bool.false_eq_true,ite_false] using pf
      · have fp : f.pc=0x80002584#32 := by simpa only [empty,ite_false] using pf
        have metadata := registers empty
        obtain ⟨m,g,mb,sg,pg,gr,gc⟩ := MainCloseValueLoop.contract B f ram _ (HeaderSpec.value raw e)
          (HeaderInput.value_span span stored.bounds) (by omega) fp metadata.1
          (by rw [valueLength];exact metadata.2.1) (by rw [valueLength];exact metadata.2.2) (values.preserve cf)
        refine ⟨8+k+j+l+m,g,by omega,(((sa.trans sb).trans sd).trans sf).trans sg,?_,cf.trans gr,gc.trans fc'⟩
        simpa only [MainCloseSpec.field,matchesName,Bool.true_and] using pg
  · have rejects : HeaderSpec.same (HeaderSpec.name raw e) (WireSpec.ascii "connection")=false := by
      cases matchesName : HeaderSpec.same (HeaderSpec.name raw e) (WireSpec.ascii "connection") with
      | false => rfl
      | true =>
        have maps : (HeaderSpec.name raw e).map HeaderSpec.lower=(WireSpec.ascii "connection").map HeaderSpec.lower := of_decide_eq_true matchesName
        have sizes := congrArg List.length maps
        simp only [List.length_map,HeaderInput.name_length stored.bounds,show (WireSpec.ascii "connection").length=10 by decide +kernel] at sizes
        contradiction
    refine ⟨8+k,b,by omega,sa.trans sb,?_,ab,bcsr⟩
    simpa only [MainCloseSpec.field,rejects,Bool.false_and,length,ite_false,Bool.false_eq_true] using pb
end E5R.Thermostat.MainCloseField
