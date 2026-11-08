import Projects.thermostat.HeadTargetPrefix
import Projects.thermostat.HeadTargetValidationSpec
namespace E5R.Thermostat.HeadTargetChecked
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Real target parsing through the version-prefix cutpoint or refusal.
    Delimiters, origin-form slash and the eight-byte version width are derived
    from the input RAM, including every actual load/bounds check. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (m j length : Nat)
    (hp : c.pc=0x80002dc0#32) (h17 : c.get 17=BitVec.ofNat 32 m) (h9 : c.get 9=BitVec.ofNat 32 j)
    (h12 : c.get 12=BitVec.ofNat 32 length) (h28 : c.get 28=buf+BitVec.ofNat 32 m)
    (hm : m<j) (hj : j≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) :
    let g := bytes ram buf
    let te := scan isTargetByte g (m+1) j
    ∃ steps d, 0<steps ∧ steps≤16+11*(j-(m+1)) ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeadTargetValidationSpec.Good g m te j then 0x80002e20#32 else 0x80002efc#32) ∧
      (HeadTargetValidationSpec.Good g m te j →
        d.get 18=BitVec.ofNat 32 te ∧ d.get 6=buf+BitVec.ofNat 32 (te-1) ∧
        d.get 29=BitVec.ofNat 32 (m+1) ∧ d.get 30=BitVec.ofNat 32 (te-m-1) ∧ d.get 7=BitVec.ofNat 32 (te-1)) ∧
      (∀ r : Reg, r≠29 → r≠30 → r≠31 → r≠8 → r≠19 → r≠7 → r≠18 → r≠6 → r≠20 → r≠21 → r≠28 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let te := scan isTargetByte g (m+1) j
  have lower : m+1≤te := scan_ge isTargetByte g (m+1) j
  have upper : te≤j := scan_le isTargetByte g (m+1) j (by omega)
  obtain ⟨n,a,positive,bound,scanTrace,pc,start,cache,frame,csr⟩ := HeadTargetPrefix.contract B c ram buf m j length hp h17 h9 h12 h28 hm hj hlen mem
  by_cases inside : te<j
  · have atCheck : a.pc=0x80002dfe#32 := by
      change a.pc=HeadTargetSpec.pc te j at pc
      simpa only [HeadTargetSpec.pc,inside,ite_true] using pc
    let front := ram (buf+BitVec.ofNat 32 (m+1))
    let last := ram (buf+BitVec.ofNat 32 te)
    have address : buf+BitVec.ofNat 32 m+1#32=buf+BitVec.ofNat 32 (m+1) := by rw [BitVec.add_assoc,HeadScanMath.next_word]
    have access : B.inRam (buf+BitVec.ofNat 32 m+1#32) 1=true := by
      rw [address]
      exact Memory.block_access mem (off := m+1) (by decide) (by change m+1+1≤length;omega)
    obtain ⟨index,value,addr,offset,rem,sumIndex⟩ := cache inside
    obtain ⟨k,d,klo,khi,validate,endPC,frame2,csr2⟩ := HeadTargetValidate.contract B a ram
      (BitVec.ofNat 32 (te-m-1)) (BitVec.ofNat 32 te) (BitVec.ofNat 32 j) (BitVec.ofNat 32 last.toNat)
      (buf+BitVec.ofNat 32 m) (BitVec.ofNat 32 (j-te)) front atCheck offset index
      ((frame 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h9) value ((frame 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28) rem access (by rw [address])
    have meaning : HeadTargetValidate.pc (BitVec.ofNat 32 (te-m-1)) (BitVec.ofNat 32 te) (BitVec.ofNat 32 j)
        (BitVec.ofNat 32 last.toNat) front (BitVec.ofNat 32 (j-te))=
        if HeadTargetValidationSpec.Good g m te j then 0x80002e20#32 else 0x80002efc#32 := by
      rw [HeadTargetValidationSpec.pc (te-m-1) te j (j-te) last front (by omega) (by omega) (by omega) (by omega)]
      have eq := HeadTargetValidationSpec.good_iff g m te j lower
      change (if te-m-1≠0 ∧ te<j ∧ g te=32 ∧ g (m+1)=47 ∧ j-te=9 then _ else _) = _
      simp only [←eq]
    refine ⟨n+k,d,by omega,by omega,scanTrace.trans validate,endPC.trans meaning,?_,?_,csr2.trans csr⟩
    · intro good
      exact ⟨(frame2 18 (by decide) (by decide)).trans index,(frame2 6 (by decide) (by decide)).trans addr,
        (frame2 29 (by decide) (by decide)).trans start,(frame2 30 (by decide) (by decide)).trans offset,(frame2 7 (by decide) (by decide)).trans sumIndex⟩
    · intro r h29 h30 h31 h8 h19 h7 h18 h6 h20 h21 h28
      exact (frame2 r h8 h28).trans (frame r h29 h30 h31 h8 h19 h7 h18 h6 h20 h21)
  · have bad : ¬HeadTargetValidationSpec.Good g m te j := by intro good;exact inside good.2.1
    refine ⟨n,a,positive,by omega,scanTrace,?_,fun good => False.elim (bad good),?_,csr⟩
    · change a.pc=HeadTargetSpec.pc te j at pc
      change a.pc=(if HeadTargetValidationSpec.Good g m te j then _ else _)
      simpa only [HeadTargetSpec.pc,inside,bad,ite_false] using pc
    · intro r h29 h30 h31 h8 h19 h7 h18 h6 h20 h21 h28
      exact frame r h29 h30 h31 h8 h19 h7 h18 h6 h20 h21
end E5R.Thermostat.HeadTargetChecked
