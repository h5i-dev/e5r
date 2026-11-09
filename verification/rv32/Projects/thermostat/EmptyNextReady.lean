import Projects.thermostat.MainHeaderToBody
import Projects.thermostat.EmptyNextLoads
import Projects.thermostat.EmptyNextCall
import Projects.thermostat.EmptyNextStoreMemory
import Projects.thermostat.EmptyNextTailMemory
import Projects.thermostat.RuntimeNext
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.EmptyNextReady
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

def high0 (ram : Word → BitVec 8) := extend .h false (ramRead ram (sp+4532#32) .h)
def high1 (ram : Word → BitVec 8) := extend .h false (ramRead ram (sp+4530#32) .h)
def high2 (ram : Word → BitVec 8) := extend .h true (ramRead ram (sp+4534#32) .h)
def low (ram : Word → BitVec 8) := extend .h false (ramRead ram (sp+3328#32) .h)
def stored (ram : Word → BitVec 8) (head : Head) := EmptyNextStores.memory ram sp
  (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2)
  (high0 ram) (high1 ram) (high2 ram)
def copied (ram : Word → BitVec 8) (head : Head) := MainNextCopy264.memory (stored ram head) sp 4552
def pad (ram : Word → BitVec 8) (head : Head) (k : Nat) := extend .b false (ramRead (copied ram head) (sp+BitVec.ofNat 32 (4817+k)) .b)
def memory (ram : Word → BitVec 8) (head : Head) := EmptyNextTail.memory (copied ram head) sp
  (BitVec.ofNat 32 head.len) (BitVec.ofNat 32 head.minor)
  (pad ram head 0) (pad ram head 1) (pad ram head 2) (pad ram head 3) (pad ram head 4) (pad ram head 5) (pad ram head 6)

/-- Actual Empty framing Next packaging: outcome branch, all actual loads,
    metadata/payload stores,264-byte memcpy, padding, raw/decoded cursors and
    jump. Unused payload bytes are read from RAM rather than prescribed. -/
theorem contract {c ram input s head served}
    (h : MainHeaderToBody.Ready c ram input s head)
    (original : HeadCompletedView.At ram (sp+4520#32) head) (exactHead : input.length=head.len)
    (bank : MainGprBank.At c) (serve : MainServeLayout.At ram served)
    (kind : head.framing=.empty) (countBound : served<100)
    (bounds : MainHeadAcceptedBounds.At 1024 1024 head)
    (contained : head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry)) :
    ∃ d, Quiet.Steps B img 409 ⟨c,ram⟩ ⟨d,memory ram head⟩ ∧
      RuntimeNext.Entry d (memory ram head) input s head
        0 head.len served (low ram) ∧ d.sameCsr c ∧
      ViewFrame.Region ram (memory ram head) (sp+72#32) 60 ∧
      ViewFrame.Region ram (memory ram head) (sp+16#32) 4 ∧ ViewFrame.Region ram (memory ram head) (sp+3204#32) 84 := by
  have stableIn : MainTransactionStable.At c ram input s := ⟨h.stable.sp,h.stable.fp,h.stable.uart,h.stable.one,h.stable.layout.bound,h.stable.layout.filled,h.stable.bytes,h.stable.app,h.stable.invariant,h.stable.stack,h.stable.masked⟩
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block stableIn.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have offset (a b : Nat) : (sp+BitVec.ofNat 32 a)+BitVec.ofNat 32 b=sp+BitVec.ofNat 32 (a+b) := by rw [BitVec.add_assoc,←BitVec.ofNat_add]
  have view : HeadCompletedView.At ram (sp+3320#32) head := by
    simpa only [show sp+3320#32=MainHeaderToBody.fp+116#32 by decide +kernel] using h.view
  have fpEq : sp+3204#32=fp := by decide +kernel
  have startPC : c.pc=0x80000fc0#32 := by simpa only [kind,MainBodyHeadDispatch.At] using h.cut
  obtain ⟨b,loads,bpc,b18,b27,b10,b12,b11,br,bc⟩ := EmptyNextLoads.contract B c ram sp (high0 ram) (high1 ram) (high2 ram) (low ram)
    stableIn.sp (by simpa only [fpEq] using stableIn.fp)
    (by simpa only [offset] using view.padding) rfl rfl rfl rfl stack (by decide) startPC
  have b2 := (br 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans stableIn.sp
  have b8 := (br 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans stableIn.fp
  obtain ⟨z,stores,zpc,_,_,zr,zc⟩ := EmptyNextStores.contract B b ram sp _ _ _ _ (high0 ram) (high1 ram) (high2 ram)
    b2 (by simpa only [fpEq] using b8) b10 b11 b12
    (by simpa only [offset] using original.methodStart) (by simpa only [offset] using original.methodEnd)
    (by simpa only [offset] using original.targetStart) (by simpa only [offset] using original.targetEnd) stack (by decide) bpc
  have z2 := (zr 2 (by decide) (by decide)).trans b2
  obtain ⟨v,call,vpc,v10,v12,v11,v1,vr,vc⟩ := EmptyNextCall.contract B z (stored ram head) sp z2 zpc
  have v2 := (vr 2 (by decide) (by decide) (by decide) (by decide)).trans z2
  obtain ⟨e,copy,ret,_⟩ := MainNextCopy264.contract B v (stored ram head) sp 4552 (Or.inr rfl) vpc v2 v10 v11 v12 stack (by decide)
  have epc : e.pc=0x8000101e#32 := by rw [ret.pc,v1];decide +kernel
  have copiedRegs (rr : Reg) (safe : rr∈MainSavedGpr.regs) : e.get rr=v.get rr := by
    have casesReg : rr=2 ∨ rr=8 ∨ rr=9 ∨ rr=18 ∨ rr=19 ∨ rr=20 ∨ rr=21 ∨ rr=22 ∨ rr=23 ∨ rr=24 ∨ rr=25 ∨ rr=26 ∨ rr=27 := by
      simpa only [MainSavedGpr.regs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using safe
    rcases casesReg with he|he|he|he|he|he|he|he|he|he|he|he|he <;> subst rr
    all_goals first | exact ret.sp | exact ret.x8 | exact ret.x9 | exact ret.x18 | exact ret.x19 | exact ret.x20 | exact ret.x21 | exact ret.x22 | exact ret.x23 | exact ret.x24 | exact ret.x25 | exact ret.x26 | exact ret.x27
  have back (rr : Reg) (safe : rr∈MainSavedGpr.regs) : e.get rr=b.get rr := by
    have neq : ∀ rr : Reg, rr∈MainSavedGpr.regs → rr≠10 ∧ rr≠12 ∧ rr≠11 ∧ rr≠1 ∧ rr≠13 := by decide +kernel
    obtain ⟨n10,n12,n11,n1,n13⟩ := neq rr safe
    exact (copiedRegs rr safe).trans ((vr rr n10 n12 n11 n1).trans (zr rr n13 n10))
  have firstFrame (off size : Nat) (lo : 40≤off) (hi : off+size≤4904) : ViewFrame.Region ram (copied ram head) (sp+BitVec.ofNat 32 off) size := by
    apply HeadRegionFrame.trans (EmptyNextStoreMemory.region ram sp _ _ _ _ (high0 ram) (high1 ram) (high2 ram) off size lo (by omega))
    exact MainNextCopy264.frame (stored ram head) sp 4552 off size (by omega) (Or.inl hi)
  have word (off : Nat) (lo : 40≤off) (hi : off+4≤4904) : ramRead (copied ram head) (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
    simpa only [BitVec.add_zero] using ViewFrame.word (firstFrame off 4 lo hi) 0 (by decide)
  have copiedHead := MainCopyView.head (firstFrame 4520 304 (by decide) (by decide)) head original
  have minorByte : extend .b false (ramRead (copied ram head) (sp+4816#32) .b)=BitVec.ofNat 32 head.minor := by
    have v : copied ram head (sp+4816#32)=BitVec.ofNat 8 head.minor := by simpa only [offset] using copiedHead.version
    rw [Memory.load_byte,v,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show head.minor<2^8 by have := bounds.version;omega)]
  have e20 : e.get 20=BitVec.ofNat 32 head.len := (back 20 (by decide)).trans ((br 20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.length)
  obtain ⟨d,tail,dpc,_,_,_,_,_,_,d25,d24,dr,dc⟩ := EmptyNextTail.contract B e (copied ram head) sp
    (BitVec.ofNat 32 head.len) (BitVec.ofNat 32 head.minor)
    (pad ram head 0) (pad ram head 1) (pad ram head 2) (pad ram head 3) (pad ram head 4) (pad ram head 5) (pad ram head 6)
    (ret.sp.trans v2) (by simpa only [fpEq] using (back 8 (by decide)).trans b8) stack (by decide)
    e20 minorByte rfl rfl rfl rfl rfl rfl rfl epc
  let after := memory ram head
  have tailFrame (off size : Nat) (bound : off+size≤5232) (apart : off+size≤40 ∨ 44≤off) (padApart : off+size≤4896 ∨ 4903≤off) :
      ViewFrame.Region (copied ram head) after (sp+BitVec.ofNat 32 off) size := EmptyNextTailMemory.region _ sp _ _ _ _ _ _ _ _ _ off size bound apart padApart
  have frame (off size : Nat) (lo : 44≤off) (hi : off+size≤4896) : ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) size :=
    HeadRegionFrame.trans (firstFrame off size (by omega) (by omega)) (tailFrame off size (by omega) (Or.inr lo) (Or.inl hi))
  have capacityFrame : ViewFrame.Region ram after (sp+16#32) 4 := by
    apply HeadRegionFrame.trans (EmptyNextStoreMemory.low ram sp (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2)
      (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2) (high0 ram) (high1 ram) (high2 ram) 16 4 (by decide))
    apply HeadRegionFrame.trans (MainNextCopy264.frame (stored ram head) sp 4552 16 4 (by decide) (Or.inl (by decide)))
    exact tailFrame 16 4 (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have keepB (rr : Reg) (safe : rr∈[2,8,9,18,19,20,21,22,23,26,27]) : d.get rr=b.get rr := by
    have neq : ∀ rr : Reg, rr∈[2,8,9,18,19,20,21,22,23,26,27] → rr∈MainSavedGpr.regs ∧ rr≠10 ∧ rr≠15 ∧ rr≠11 ∧ rr≠12 ∧ rr≠13 ∧ rr≠14 ∧ rr≠25 ∧ rr≠24 := by decide +kernel
    obtain ⟨member,a,b,c,f,g,i,j,k⟩ := neq rr safe
    exact (dr rr a b c f g i j k).trans (back rr member)
  have keep (rr : Reg) (safe : rr∈[2,8,9,19,20,21,22,23,26]) : d.get rr=c.get rr := by
    have neq : ∀ rr : Reg, rr∈[2,8,9,19,20,21,22,23,26] → rr∈[2,8,9,18,19,20,21,22,23,26,27] ∧ rr≠18 ∧ rr≠27 ∧ rr≠10 ∧ rr≠12 ∧ rr≠11 := by decide +kernel
    obtain ⟨member,n18,n27,n10,n12,n11⟩ := neq rr safe
    exact (keepB rr member).trans (br rr n18 n27 n10 n12 n11)
  have csr := ((((dc.trans ret.csr).trans vc).trans zc).trans bc)
  have stable : MainTransactionStable.At d after input s := by
    refine ⟨(keep 2 (by decide)).trans stableIn.sp,(keep 8 (by decide)).trans stableIn.fp,
      (keep 19 (by decide)).trans stableIn.uart,(keep 22 (by decide)).trans stableIn.one,stableIn.bound,?_,?_,?_,stableIn.invariant,stableIn.stack,(congrArg Prod.fst csr).trans stableIn.masked⟩
    · have v := ViewFrame.word (frame 3288 4 (by decide) (by decide)) 0 (by decide)
      simpa only [BitVec.add_zero,show sp+3288#32=fp+84#32 by decide +kernel] using v.trans stableIn.filled
    · intro i
      have region := frame 132 2048 (by decide) (by decide)
      exact (region ⟨i.val,by have := i.isLt;have := stableIn.bound;omega⟩).trans (stableIn.bytes i)
    · apply AppState.preserve ram after s stableIn.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using frame 44 25 (by decide) (by decide)
  have sourceHead := MainCopyView.head (EmptyNextStoreMemory.region ram sp (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2) (high0 ram) (high1 ram) (high2 ram) 4520 304 (by decide) (by decide)) head original
  have array := MainNextArrayFrame.preserve (MainNextArrayView.empty (stored ram head) sp head stack sourceHead)
    (tailFrame 4904 264 (by decide) (Or.inr (by decide)) (Or.inr (by decide)))
  have metadata (off : Nat) (bound : off+4≤40) : ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead (stored ram head) (sp+BitVec.ofNat 32 off) .w := by
    have region := HeadRegionFrame.trans (MainNextCopy264.frame (stored ram head) sp 4552 off 4 (by omega) (Or.inl (by omega)))
      (tailFrame off 4 (by omega) (Or.inl bound) (Or.inl (by omega)))
    simpa only [BitVec.add_zero] using ViewFrame.word region 0 (by decide)
  refine ⟨d,(((loads.trans stores).trans call).trans copy).trans tail,
    ⟨dpc,stable,MainGprBank.preserve (fun rr member => keep rr (by
      have sub : ∀ rr : Reg, rr∈[21,23,26] → rr∈[2,8,9,19,20,21,22,23,26] := by decide +kernel
      exact sub rr member)) bank,
      MainServeLayout.preserve (fun off safe => by
        have bound := MainServeLayout.bounds off safe
        have w := ViewFrame.word (frame (3204+off) 4 (by omega) (by omega)) 0 (by decide)
        simpa only [BitVec.add_zero,BitVec.ofNat_add,←BitVec.add_assoc,fpEq] using w) serve,countBound,
      (keep 9 (by decide)).trans h.tag,
      (keepB 18 (by decide)).trans b18,(keepB 27 (by decide)).trans b27,(keep 20 (by decide)).trans h.length,d24,
      (by simpa only [Nat.add_zero] using d25),MainCopyView.head (frame 3320 304 (by decide) (by decide)) head view,array,
      (metadata 28 (by decide)).trans (EmptyNextStoreMemory.methodStart ram sp _ _ _ _ _ _ _),
      (metadata 24 (by decide)).trans (EmptyNextStoreMemory.methodEnd ram sp _ _ _ _ _ _ _),
      (metadata 36 (by decide)).trans (EmptyNextStoreMemory.targetStart ram sp _ _ _ _ _ _ _),
      (metadata 32 (by decide)).trans (EmptyNextStoreMemory.targetEnd ram sp _ _ _ _ _ _ _),
      EmptyNextTailMemory.minor_word _ sp _ _ _ _ _ _ _ _ _,bounds,Or.inl kind,(by decide),(by omega),
      (by omega),contained⟩,csr,frame 72 60 (by decide) (by decide),capacityFrame,frame 3204 84 (by decide) (by decide)⟩
end E5R.Thermostat.EmptyNextReady
