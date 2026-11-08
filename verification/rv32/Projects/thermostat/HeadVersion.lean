import Projects.thermostat.QuietPrefix
import Projects.thermostat.HeadVersionStorage
import Projects.thermostat.HeadVersionDigitsRun
namespace E5R.Thermostat.HeadVersion
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def memory (ram : Word → BitVec 8) (sp : Word) (c : Core) (te : Nat) :=
  if ram (sp+516#32+BitVec.ofNat 32 (te-1)+2#32)=72#8 then HeadVersionStorage.memory ram sp c else ram

/-- The complete actual version parser, from H through all digit and bounds
    checks, against independent byte-level version. Header processing and the
    rejection epilogue are subsequent obligations. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (m te length : Nat)
    (hp : c.pc=0x80002e20#32) (h2 : c.get 2=sp) (h10 : c.get 10=sp+4904#32) (h11 : c.get 11=sp+516#32)
    (h12 : c.get 12=BitVec.ofNat 32 length) (h17 : c.get 17=BitVec.ofNat 32 m)
    (h30 : c.get 30=BitVec.ofNat 32 (te-m-1)) (h7 : c.get 7=BitVec.ofNat 32 (te-1))
    (h6 : c.get 6=sp+516#32+BitVec.ofNat 32 (te-1)) (h15 : c.get 15=400#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0)
    (hmt : m<te) (hw : te+9≤length) (hlen : length≤2048) :
    let v := HttpRequestSpec.version (bytes ram (sp+516#32)) (te+1) (te+9)
    ∃ n d, 3≤n ∧ n≤68 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,memory ram sp c te⟩ ∧
      HeadVersionResult.At d v (c.get 13) (sp+4904#32) ∧ d.get 2=sp ∧
      (d.pc=0x80002efa#32 → ramRead (memory ram sp c te) (sp+52#32) .w=sp+4904#32) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → r≠20 → r≠8 → r≠18 → r≠30 → r≠28 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let buf := sp+516#32
  let base := buf+BitVec.ofNat 32 (te-1)
  let saved := HeadVersionStorage.memory ram sp c
  have positive : 0<te := by omega
  have stack : Memory.Block B sp 56 := by
    simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 56) (by decide) (by decide)
  have buffer : Memory.Block B buf length := Memory.sub_block hm (off := 516) (by omega) (by omega)
  have access : B.inRam (base+2#32) 1=true := by
    rw [HeadVersionInputSpec.address buf te 1 positive]
    exact Memory.block_access buffer (off := te+1) (by decide) (by change te+1+1≤length;omega)
  obtain ⟨a,first,pc1,byte,constant,frame1,csr1⟩ := Literal.compare_quiet B img 72#8 (ram (base+2#32)) HeadVersionSites.h
    c ram (base+2#32) hp (congrArg (fun x => x+2#32) h6) access rfl
  by_cases goodH : ram (base+2#32)=72#8
  · have atSave : a.pc=0x80002e2c#32 := by simpa only [HeadVersionSites.h,goodH,ite_true] using pc1
    obtain ⟨b,save,pc2,frame2,csr2⟩ := HeadVersionStorage.contract B a ram sp atSave ((frame1 2 (by decide) (by decide)).trans h2) stack ha
    have memEq : HeadVersionStorage.memory ram sp a=saved := HeadVersionStorage.congr_core ram sp c a frame1
    rw [memEq] at save
    have source2 (r : Reg) (h28 : r≠28) (h31 : r≠31) : b.get r=c.get r := (frame2 r).trans (frame1 r h28 h31)
    obtain ⟨n,e,nlo,nhi,tail,pc3,relative,frame3,csr3⟩ := HeadVersionTail.contract B b saved buf m te length pc2
      ((source2 17 (by decide) (by decide)).trans h17) ((source2 12 (by decide) (by decide)).trans h12)
      ((source2 30 (by decide) (by decide)).trans h30) ((source2 6 (by decide) (by decide)).trans h6) hmt hw hlen buffer
    have source3 (r : Reg) (h10 : r≠10) (h11 : r≠11) (h30 : r≠30) (h28 : r≠28) (h31 : r≠31) : e.get r=c.get r :=
      (frame3 r h10 h11 h30).trans (source2 r h28 h31)
    have rx := HeadVersionStorage.region ram sp c 516 2048 (by decide) (by decide)
    have agree (k : Nat) (hk : k<length) : saved (buf+BitVec.ofNat 32 k)=ram (buf+BitVec.ofNat 32 k) :=
      rx ⟨k,by omega⟩
    have tails : HeadVersionTail.Good saved base ↔ HeadVersionTail.Good ram base := by
      unfold HeadVersionTail.Good
      rw [HeadVersionInputSpec.address buf te 2 positive,HeadVersionInputSpec.address buf te 3 positive,
        HeadVersionInputSpec.address buf te 4 positive,HeadVersionInputSpec.address buf te 5 positive]
      rw [agree (te+2) (by omega),agree (te+3) (by omega),agree (te+4) (by omega),agree (te+5) (by omega)]
    have memoryEq : memory ram sp c te=saved := by
      change (if ram (base+2#32)=72#8 then saved else ram)=saved
      simp only [goodH,ite_true]
    by_cases goodTail : HeadVersionTail.Good saved base
    · have atDigits : e.pc=0x80002e8c#32 := by
        change e.pc=(if HeadVersionTail.Good saved base then _ else _) at pc3
        simpa only [goodTail,ite_true] using pc3
      obtain ⟨k,d,klo,khi,digits,result,frame4,csr4⟩ := HeadVersionDigitsRun.contract B e saved sp buf (c.get 13) (sp+4904#32) te length atDigits
        ((source3 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2) ((source3 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h7) ((source3 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h6)
        (source3 13 (by decide) (by decide) (by decide) (by decide) (by decide)) ((source3 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h15)
        ((HeadVersionStorage.buf_word ram sp c).trans h11) ((HeadVersionStorage.length_word ram sp c).trans h12)
        ((HeadVersionStorage.dst_word ram sp c).trans h10) stack ha buffer positive hw hlen
      have spec : HttpRequestSpec.version (bytes ram buf) (te+1) (te+9)=
          versionDigits (bytes saved buf (te+6)) (bytes saved buf (te+7)) (bytes saved buf (te+8)) := by
        rw [HeadVersionInputSpec.version ram buf te positive]
        have originalTail := tails.mp goodTail
        change (if ram (base+2#32)=72#8 ∧ HeadVersionTail.Good ram base then _ else _)=_
        simp only [goodH,originalTail,true_and,ite_true]
        unfold bytes
        rw [agree (te+6) (by omega),agree (te+7) (by omega),agree (te+8) (by omega)]
      refine ⟨3+9+n+k,d,by omega,by omega,?_,?_,?_,?_,?_,csr4.trans (csr3.trans (csr2.trans csr1))⟩
      · rw [memoryEq]
        exact ((first.trans save).trans tail).trans digits
      · change HeadVersionResult.At d (HttpRequestSpec.version (bytes ram buf) (te+1) (te+9)) _ _
        rw [spec]
        exact result
      · exact (frame4 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((source3 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2)
      · intro _
        rw [memoryEq]
        exact (HeadVersionStorage.dst_word ram sp c).trans h10
      · intro r h10 h11 h12 h13 h14 h15 h20 h8 h18 h30 h28 h31
        exact (frame4 r h10 h11 h12 h13 h14 h15 h20 h8 h18).trans (source3 r h10 h11 h30 h28 h31)
    · have atReject : e.pc=0x80002efa#32 := by
        change e.pc=(if HeadVersionTail.Good saved base then _ else _) at pc3
        simpa only [goodTail,ite_false] using pc3
      have originalBad : ¬HeadVersionTail.Good ram base := by intro h;exact goodTail (tails.mpr h)
      have spec : HttpRequestSpec.version (bytes ram buf) (te+1) (te+9)=3 := by
        rw [HeadVersionInputSpec.version ram buf te positive]
        change (if ram (base+2#32)=72#8 ∧ HeadVersionTail.Good ram base then _ else _)=3
        simp only [originalBad,and_false,ite_false]
      refine ⟨3+9+n,e,by omega,by omega,?_,?_,?_,?_,?_,csr3.trans (csr2.trans csr1)⟩
      · rw [memoryEq]
        exact (first.trans save).trans tail
      · change HeadVersionResult.At e (HttpRequestSpec.version (bytes ram buf) (te+1) (te+9)) _ _
        rw [spec]
        change (e.pc=0x80002efa#32 ∨ e.pc=0x80002efc#32) ∧ e.get 15=400#32 ∧ (e.pc=0x80002efc#32 → e.get 10=sp+4904#32)
        refine ⟨Or.inl atReject,(source3 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h15,?_⟩
        intro wrong
        have ne : 0x80002efa#32≠0x80002efc#32 := by decide +kernel
        exact False.elim (ne (atReject.symm.trans wrong))
      · exact (source3 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
      · intro _
        rw [memoryEq]
        exact (HeadVersionStorage.dst_word ram sp c).trans h10
      · intro r h10 h11 h12 h13 h14 h15 h20 h8 h18 h30 h28 h31
        exact source3 r h10 h11 h30 h28 h31
  · have atReject : a.pc=0x80002efc#32 := by simpa only [HeadVersionSites.h,goodH,ite_false] using pc1
    have spec : HttpRequestSpec.version (bytes ram buf) (te+1) (te+9)=3 := by
      rw [HeadVersionInputSpec.version ram buf te positive]
      change (if ram (base+2#32)=72#8 ∧ HeadVersionTail.Good ram base then _ else _)=3
      simp only [goodH,false_and,ite_false]
    have memoryEq : memory ram sp c te=ram := by
      change (if ram (base+2#32)=72#8 then saved else ram)=ram
      simp only [goodH,ite_false]
    refine ⟨3,a,by decide,by decide,?_,?_,?_,?_,?_,csr1⟩
    · rw [memoryEq];exact first
    · change HeadVersionResult.At a (HttpRequestSpec.version (bytes ram buf) (te+1) (te+9)) _ _
      rw [spec]
      change (a.pc=0x80002efa#32 ∨ a.pc=0x80002efc#32) ∧ a.get 15=400#32 ∧ (a.pc=0x80002efc#32 → a.get 10=sp+4904#32)
      exact ⟨Or.inr atReject,(frame1 15 (by decide) (by decide)).trans h15,fun _ => (frame1 10 (by decide) (by decide)).trans h10⟩
    · exact (frame1 2 (by decide) (by decide)).trans h2
    · intro wrong
      have ne : 0x80002efc#32≠0x80002efa#32 := by decide +kernel
      exact False.elim (ne (atReject.symm.trans wrong))

    · intro r h10 h11 h12 h13 h14 h15 h20 h8 h18 h30 h28 h31
      exact frame1 r h28 h31

/-- A valid version necessarily passed the actual H load/comparison, so all
    actual scratch stores are available to the following header parser. -/
theorem memory_accepted (ram : Word → BitVec 8) (sp : Word) (c : Core) (te : Nat) (ht : 0<te)
    (accepted : HttpRequestSpec.version (bytes ram (sp+516#32)) (te+1) (te+9)<2) :
    memory ram sp c te=HeadVersionStorage.memory ram sp c := by
  by_cases good : ram (sp+516#32+BitVec.ofNat 32 (te-1)+2#32)=72#8
  · simp only [memory,good,ite_true]
  · have bad : HttpRequestSpec.version (bytes ram (sp+516#32)) (te+1) (te+9)=3 := by
      rw [HeadVersionInputSpec.version ram (sp+516#32) te ht]
      simp only [good,false_and,ite_false]
    rw [bad] at accepted
    omega

theorem region (ram : Word → BitVec 8) (sp : Word) (c : Core) (te off len : Nat)
    (hb : off+len≤4294967296) (hs : off+len≤20 ∨ 56≤off) :
    ViewFrame.Region ram (memory ram sp c te) (sp+BitVec.ofNat 32 off) len := by
  unfold memory
  split
  · exact HeadVersionStorage.region ram sp c off len hb hs
  · intro i;rfl

theorem saved (ram : Word → BitVec 8) (sp : Word) (c : Core) (te : Nat) (values : Reg → Word)
    (h : HeadSaved.At ram sp values) : HeadSaved.At (memory ram sp c te) sp values := by
  unfold memory
  split
  · exact HeadVersionStorage.saved ram sp c values h
  · exact h

theorem app (ram : Word → BitVec 8) (c : Core) (te : Nat) (state : Spec.Snapshot) (h : AppState.At ram state) :
    AppState.At (memory ram 0x80ffea10#32 c te) state := by
  unfold memory
  split
  · exact HeadVersionStorage.app ram c state h
  · exact h
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (m te length : Nat)
    (hp : c.pc=0x80002e20#32) (h2 : c.get 2=sp) (h10 : c.get 10=sp+4904#32) (h11 : c.get 11=sp+516#32)
    (h12 : c.get 12=BitVec.ofNat 32 length) (h17 : c.get 17=BitVec.ofNat 32 m)
    (h30 : c.get 30=BitVec.ofNat 32 (te-m-1)) (h7 : c.get 7=BitVec.ofNat 32 (te-1))
    (h6 : c.get 6=sp+516#32+BitVec.ofNat 32 (te-1)) (h15 : c.get 15=400#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0)
    (hmt : m<te) (hw : te+9≤length) (hlen : length≤2048) (masked : c.mie_=false) :
    let v := HttpRequestSpec.version (bytes ram (sp+516#32)) (te+1) (te+9)
    ∃ n d, 3≤n ∧ n≤68 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,memory ram sp c te⟩ ∧
      HeadVersionResult.At d v (c.get 13) (sp+4904#32) ∧ d.get 2=sp ∧
      (d.pc=0x80002efa#32 → ramRead (memory ram sp c te) (sp+52#32) .w=sp+4904#32) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → r≠20 → r≠8 → r≠18 → r≠30 → r≠28 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,hlo,hi,trace,result,stack,reloadWord,frame,csr⟩ :=
    contract B c ram sp m te length hp h2 h10 h11 h12 h17 h30 h7 h6 h15 hm ha hmt hw hlen
  exact ⟨n,d,hlo,hi,Interrupt.close trace.det masked,result,stack,reloadWord,frame,csr,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadVersion
